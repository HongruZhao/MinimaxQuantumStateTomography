"""Independent small-dimension mathematical and optimization checks."""
import argparse
import itertools
import json
import time
from pathlib import Path
import numpy as np
from scipy.linalg import eigh
from baseline import herm, forward, opnorm, trnorm
from channel import Channel
from estimators import METHODS, solve_estimator, independent_validation
from projections import scipy_density
from solvers import apg_reference, objective, full_gap
from sampling import stabilizer_states, state
from large_simulation import records


def pauli_matrices(n):
    local = [np.eye(2), np.array([[0, 1], [1, 0]]),
             np.array([[0, -1j], [1j, 0]]), np.diag([1, -1])]
    basis = []
    for factors in itertools.product(local, repeat=n):
        p = np.array([[1.]])
        for factor in factors:
            p = np.kron(p, factor)
        basis.append(p)
    return np.asarray(basis)


def markov_multipliers(n, k):
    """Average uniform nonidentity Pauli labels block by block, then dephase.

    This does not use the transfer-matrix formula in FastChannel.
    """
    count = 4 ** n
    dist = np.eye(count).reshape((count,) + (4,) * n)
    blocks = [[(j * k + k // 2 + a) % n for a in range(k)] for j in range(n // k)]
    blocks += [[j * k + a for a in range(k)] for j in range(n // k)]
    for block in blocks:
        axes = [0] + [1 + q for q in block] + [1 + q for q in range(n) if q not in block]
        a = dist.transpose(axes).reshape(count, 4 ** k, -1).copy()
        a[:, 1:, :] = a[:, 1:, :].sum(axis=1, keepdims=True) / (4 ** k - 1)
        dist = a.reshape((count,) + (4,) * n).transpose(np.argsort(axes))
    diagonal = np.array([all(j in (0, 3) for j in code) for code in itertools.product(range(4), repeat=n)])
    return dist.reshape(count, count)[:, diagonal].sum(axis=1)


def ray_keys(vectors):
    vectors = vectors.copy()
    first = np.argmax(np.abs(vectors) > 1e-10, axis=1)
    phase = vectors[np.arange(len(vectors)), first]
    vectors *= (np.abs(phase) / phase)[:, None]
    return np.round(np.concatenate([vectors.real, vectors.imag], axis=1), 10)


def run(output):
    rng = np.random.default_rng(20260920)
    report = dict(status='running', checks=[], optimizer_checks=[], noiseless_checks=[])
    start = time.perf_counter()
    output.parent.mkdir(parents=True, exist_ok=True)

    def save():
        output.write_text(json.dumps(report, indent=2) + '\n')

    def checked(name, error, tolerance):
        item = dict(check=name, error=float(error), tolerance=tolerance, passed=bool(error <= tolerance))
        report['checks'].append(item)
        save()
        print(json.dumps(item), flush=True)
        assert item['passed'], name

    for n, k in [(2, 2), (4, 2), (4, 4)]:
        c = Channel(n, k)
        independent_m = markov_multipliers(n, k)
        checked('Pauli Markov channel n%d k%d' % (n, k), np.max(abs(c.m.ravel() - independent_m)), 1e-12)
        paulis = pauli_matrices(n)
        a = herm(rng.normal(size=(c.d, c.d)) + 1j * rng.normal(size=(c.d, c.d)))
        alpha = np.einsum('pij,ji->p', paulis, a) / c.d
        explicit = np.einsum('p,pij->ij', alpha * independent_m, paulis)
        checked('Explicit matrix channel n%d k%d' % (n, k), np.linalg.norm(c.apply(a, 'M') - explicit), 1e-11)
        checked('Inverse channel n%d k%d' % (n, k), np.linalg.norm(c.apply(c.apply(a, 'M'), 'inverse') - a), 1e-10)
        expected_l = (c.d + 1) * explicit - np.trace(a) * np.eye(c.d)
        checked('Score channel identity n%d k%d' % (n, k), np.linalg.norm(c.apply(a) - expected_l), 1e-10)

    pool = np.load(Path(__file__).parent / 'clifford_representatives.npz')['unitaries']
    checked('All 11520 pool matrices unitary', np.max(abs(pool @ pool.conj().transpose(0, 2, 1) - np.eye(4))), 1e-11)
    pool_rays, multiplicities = np.unique(ray_keys(pool.conj().reshape(-1, 4)), axis=0, return_counts=True)
    explicit_rays = np.unique(ray_keys(stabilizer_states(2)), axis=0)
    checked('Two-qubit finite sampler exactly matches original Clifford pool',
            np.max(abs(pool_rays - explicit_rays)), 1e-9)
    checked('Uniform projector multiplicities in original pool', np.max(abs(multiplicities - 768)), 0)
    vectors = stabilizer_states(4)
    checked('36720 distinct four-qubit stabilizer rays', abs(len(np.unique(ray_keys(vectors), axis=0)) - 36720), 0)
    for family in ['rank8_diagonal', 'rank8_rotated', 'polynomial_rotated']:
        rho, _, _ = state(4, family)
        probabilities = (16 / len(vectors)) * np.einsum('bi,ij,bj->b', vectors.conj(), rho, vectors).real
        exact_mean = (vectors.T * probabilities) @ vectors.conj()
        checked('Exact global Born expectation ' + family, np.linalg.norm(exact_mean - (rho + np.eye(16)) / 17), 1e-11)

    c = Channel(4, 2)
    rho, v, lam = state(4, 'rank8_rotated')
    b = records(4, v, lam, [65536], [20260920, 177])[0]
    checked('Periodic Born sampler empirical mean vs independent channel', np.linalg.norm(b - c.apply(rho, 'M')), .03)
    # A less accurate data mean gives an active constrained optimization problem.
    b = records(4, v, lam, [256], [20260920, 178])[0]
    y = 17 * b - np.eye(16)
    a = herm(rng.normal(size=(16, 16)) + 1j * rng.normal(size=(16, 16)))
    x = np.eye(16) / 16
    step = 1e-5
    difference = (objective(x + step*a, c.apply(x + step*a), y) - objective(x - step*a, c.apply(x - step*a), y)) / (2*step)
    derivative = np.vdot(c.apply(x) - y, a).real
    checked('MW objective directional derivative', abs(difference - derivative), 1e-8)

    reference, ref_stats = apg_reference(c, b, 256, tol=1e-9, maxiter=20000, max_seconds=120)
    assert ref_stats['converged'], ref_stats
    mw, mw_stats = solve_estimator(c, b, 256, 'MW-PLS', tol_factor=.001)
    mw_check = independent_validation(c, b, 256, mw, 'MW-PLS', mw_stats, tol_factor=.001)
    assert mw_check['accepted']
    checked('FW objective bounded by its gap against independent APG optimum',
            max(0., mw_check['mw_objective'] - ref_stats['objective'] - mw_check['mw_gap']), 2e-9)
    report['optimizer_checks'].append(dict(method='MW-PLS', validation=mw_check,
                                          independent_reference=ref_stats,
                                          objective_difference=mw_check['mw_objective'] - ref_stats['objective']))
    omd, omd_stats = solve_estimator(c, b, 256, 'OMD', tol_factor=.01)
    omd_check = independent_validation(c, b, 256, omd, 'OMD', omd_stats, tol_factor=.01)
    assert omd_check['accepted']
    # The reference solves h_eta accurately. Its unregularized gap need not
    # vanish because eta>0; require the paper's original-gap budget separately.
    pdhg, pdhg_stats = forward(c, y, 256, method='pdhg', tol_fraction=1.,
                               eta_fraction=.005*.01, maxiter=30000, regularized_tol_fraction=1e-7)
    assert pdhg_stats['converged'], {k:v for k,v in pdhg_stats.items() if k != 'history'}
    eta = omd_stats['eta']
    omd_h = opnorm(y - c.apply(omd)) + eta*np.linalg.norm(omd)**2
    pdhg_h = opnorm(y - c.apply(pdhg)) + eta*np.linalg.norm(pdhg)**2
    checked('ADMM regularized objective vs independent PDHG reference',
            max(0., omd_h - pdhg_h - omd_check['regularized_gap']), 2e-9)
    report['optimizer_checks'].append(dict(method='OMD', validation=omd_check,
                                          independent_reference=pdhg_stats,
                                          regularized_objective_difference=omd_h - pdhg_h))
    save()

    for n, k in [(2, 2), (4, 2), (4, 4)]:
        c = Channel(n, k)
        rho, _, _ = state(n, 'polynomial_rotated')
        b = c.apply(rho, 'M')
        for method in METHODS:
            fit, stats = solve_estimator(c, b, 2**30, method, maxiter=300000, max_seconds=120)
            validation = independent_validation(c, b, 2**30, fit, method, stats, rho=rho)
            stats.pop('_dual_witness', None)
            assert validation['accepted'], (n, k, method, stats)
            checked('Noiseless reconstruction n%d k%d %s' % (n, k, method), validation['trace_norm_error'], .002)
            report['noiseless_checks'].append(dict(n=n, k=k, method=method, validation=validation, stats=stats))
    report.update(status='passed', seconds=time.perf_counter() - start)
    save()


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--output', type=Path, default=Path(__file__).parent.parent / 'reports' / 'solver_audit.json')
    run(p.parse_args().output)
