"""Targeted regressions for accuracy, independent budgets and stale caches."""
import copy
import importlib.util
import json
from pathlib import Path
import sys
import tempfile

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
OLD = ROOT / 'original'
sys.path.insert(0, str(ROOT / 'src'))
from estimators import (Channel, solve_estimator, independent_validation,
                        mathematical_validation)
from run_identity import (StaleResultError, cache_identity, check_cached_result,
                          artifact_hashes, seal_result, source_hashes)
from projections import Partial, scipy_nuclear
from audit_solvers import markov_multipliers, pauli_matrices
import run_convergence
import run_global_benchmark


def main():
    checks = []
    def checked(name, condition, **details):
        assert condition, (name, details)
        checks.append(dict(name=name, passed=True, **details))
    data_dir = ROOT / 'fixtures/original_rank8_rep000'
    with np.load(data_dir / 'data.npz') as z:
        b = z['means'][0]
    c = Channel(4, 2)
    fresh = {}
    for method in ['PLS', 'OMD', 'MW-PLS']:
        x, stats = solve_estimator(c, b, 256, method)
        v = independent_validation(c, b, 256, x, method, stats)
        checked('Default ' + method + ' accepted by new validator', v['accepted'])
        fresh[method] = x, stats
    tight, ts = solve_estimator(c, b, 256, 'OMD', tol_factor=1e-6, omd_maxiter=10000)
    tv = independent_validation(c, b, 256, tight, 'OMD', ts, tol_factor=1e-6)
    checked('Tight OMD has scaled eta and meets original request',
            ts['eta'] == 1.25e-9 and tv['accepted'], iterations=ts['iterations'],
            eta=ts['eta'], original_gap=tv['omd_gap'], requested_tolerance=2.5e-7)

    # Feasible competitor calculation uses explicit physical Pauli matrices,
    # not the production channel coefficient transforms.
    paulis = pauli_matrices(4)
    multipliers = markov_multipliers(4, 2)
    def explicit_L(x):
        coeff = np.einsum('pij,ji->p', paulis, x) / 16
        return 17 * np.einsum('p,pij->ij', coeff * multipliers, paulis) - np.trace(x) * np.eye(16)
    y = 17 * b - np.eye(16)
    with np.load(ROOT / 'reports/before_tight_omd.npz') as z:
        old_tight = z['estimate']
    before_f = float(np.max(abs(np.linalg.eigvalsh(y - explicit_L(old_tight)))))
    after_f = float(np.max(abs(np.linalg.eigvalsh(y - explicit_L(tight)))))
    checked('Feasible new competitor proves old tight fit missed requested accuracy',
            before_f - after_f > 2.5e-7 and np.linalg.eigvalsh(tight)[0] > -1e-12,
            old_original_objective=before_f, corrected_original_objective=after_f,
            improvement=before_f-after_f)

    spec = importlib.util.spec_from_file_location('unchanged_original_omd', OLD / 'src_before_review/omd_tolerance.py')
    original = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(original)
    original.project_density = Partial().density
    original.nuclear_project = scipy_nuclear
    before_default, _ = original.solve(c, y, 256, regfrac=1., tolfrac=1., maxiter=20000)
    difference = float(np.linalg.norm(before_default - fresh['OMD'][0]))
    checked('Default OMD numerical output preserved', difference < 1e-13, difference=difference)

    for method in ['OMD', 'MW-PLS']:
        x, stats = fresh[method]
        wrong = independent_validation(c, b, 2**24, x, method, stats)
        checked('Wrong T rejected mathematically and by identity: ' + method,
                not wrong['accepted'] and not wrong['mathematical_checks_passed']
                and 'problem_mismatch' in wrong['metadata_errors'])
        budget_field = 'original_gap_tolerance' if method == 'OMD' else 'epsilon_Q'
        for value in [float('nan'), float('inf'), -1., 10.]:
            corrupt = copy.deepcopy(stats)
            corrupt[budget_field] = value
            rejected = independent_validation(c, b, 256, x, method, corrupt)
            checked('Invalid reported budget rejected: %s %s' % (method, value), not rejected['accepted'])
    x, stats = fresh['OMD']
    corrupt = copy.deepcopy(stats); corrupt['eta'] *= 2
    checked('Mismatched actual eta rejected', not independent_validation(c,b,256,x,'OMD',corrupt)['accepted'])
    for field in ['source_sha256', 'problem', 'estimate_sha256', 'dual_witness_sha256', 'solver_configuration_sha256']:
        corrupt = copy.deepcopy(stats); corrupt[field] = 'mismatch'
        checked('Mismatched provenance rejected: ' + field,
                not independent_validation(c,b,256,x,'OMD',corrupt)['accepted'])
    altered_b = b.copy(); altered_b[0,0] += 1e-6; altered_b[1,1] -= 1e-6
    checked('Different input statistic rejected',
            not independent_validation(c,altered_b,256,x,'OMD',stats)['accepted'])
    for T in [0, -1, True, float('nan'), 1.5]:
        try:
            mathematical_validation(c,b,T,x,'OMD',dual_witness=stats['_dual_witness'])
        except ValueError:
            checked('Invalid T rejected: ' + str(T), True)
        else:
            raise AssertionError(T)

    with tempfile.TemporaryDirectory(prefix='shadow-new-cache-') as temp:
        directory = Path(temp)
        target = directory / 'summary.json'
        (directory / 'fit.npz').write_bytes(b'cache-protocol-test')
        identity = cache_identity({'T': 256}, {'b': 'recorded-input-hash'})
        row = seal_result(dict(status='complete', cache_identity=identity,
                               artifact_sha256=artifact_hashes(directory)))
        target.write_text(json.dumps(row))
        checked('Matching complete cache can be reused', check_cached_result(target, identity) is not None)
        for field in ['source_sha256', 'configuration', 'inputs']:
            other = copy.deepcopy(identity); other[field] = {'changed': True}
            try:
                check_cached_result(target, other)
            except StaleResultError:
                checked('Cache rejects changed ' + field, True)
            else:
                raise AssertionError(field)
        (directory / 'fit.npz').write_bytes(b'changed-output')
        try:
            check_cached_result(target, identity)
        except StaleResultError:
            checked('Cache rejects modified saved output', True)
        else:
            raise AssertionError('output hash')
        # The two public study drivers must reject the exact stale-source
        # early-return cases reported by the external review.
        cfg=dict(name='case', repetitions=1, cases=[dict(n=4,k=2,family='rank8_rotated',sizes=[256])])
        p=directory/'results/case/n4_k2_rank8_rotated_rep000/summary.json'
        p.parent.mkdir(parents=True); p.write_text(json.dumps(dict(status='complete',source_sha256={'wrong':'wrong'})))
        run_convergence.ROOT=directory
        try:
            run_convergence.run(cfg,0)
        except StaleResultError:
            checked('Convergence driver rejects stale-source completion', True)
        else:
            raise AssertionError('convergence driver')
        p=directory/'results/global_rebenchmark/rep000/summary.json'
        p.parent.mkdir(parents=True); p.write_text(json.dumps(dict(status='complete',source_sha256={'wrong':'wrong'})))
        run_global_benchmark.ROOT=directory
        try:
            run_global_benchmark.run(0)
        except StaleResultError:
            checked('Global driver rejects stale-source completion', True)
        else:
            raise AssertionError('global driver')
        # Exercise successful generation, serialization and second-call reuse.
        cfg=dict(name='tiny_fresh',repetitions=1,cases=[dict(n=2,k=2,family='polynomial_rotated',sizes=[16])])
        run_convergence.run(cfg,0)
        p=directory/'results/tiny_fresh/n2_k2_polynomial_rotated_rep000/summary.json'
        before=p.read_bytes()
        run_convergence.run(cfg,0)
        checked('Fresh public driver result reused only when identity matches', p.read_bytes()==before)

    result=dict(status='passed', checks=checks, source_sha256=source_hashes(),
                tight_omd=dict(eta=ts['eta'],iterations=ts['iterations'],gap=tv['omd_gap'],
                               original_objective=after_f, old_original_objective=before_f))
    (ROOT/'reports/review_regressions.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':result['status'],'checks':len(checks),'tight_omd':result['tight_omd']},indent=2))


if __name__ == '__main__':
    main()
