"""Reproduce the review's three defects against the unchanged prior sources."""
import hashlib
import importlib
import json
from pathlib import Path
import sys
import tempfile
import types

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
OLD = ROOT / 'original'
sys.path.insert(0, str(OLD / 'src_before_review'))
from estimators import Channel, solve_estimator, independent_validation


def main():
    data_dir = ROOT / 'fixtures/original_rank8_rep000'
    with np.load(data_dir / 'data.npz') as data:
        b, rho = data['means'][0], data['rho']
    c = Channel(4, 2)
    records = json.loads((data_dir / 'summary.json').read_text())['records']
    result = {'source': str(OLD / 'src_before_review'), 'review': 'https://chatgpt.com/share/6aaf8102-d1a4-83e9-b909-997b0519979a'}
    with np.load(data_dir / 'estimates_T256.npz') as saved:
        wrong_T = []
        for method in ['OMD', 'MW-PLS']:
            row = next(r for r in records if r['T'] == 256 and r['method'] == method)
            stats = dict(row['stats'])
            if method == 'OMD':
                stats['_dual_witness'] = saved['OMD_dual']
            check = independent_validation(c, b, 2**24, saved[method.replace('-', '_')], method, stats)
            gap = check['omd_gap'] if method == 'OMD' else check['mw_gap']
            budget = np.sqrt(16 / 2**24) if method == 'OMD' else 16 / 2**24
            assert check['accepted'] and gap > budget
            wrong_T.append(dict(method=method, accepted=check['accepted'], recomputed_gap=gap,
                                independent_budget=budget, trusted_budget=check['stopping_threshold']))
    result['wrong_T_false_acceptance'] = wrong_T
    print('Reproduced wrong-T false acceptance', wrong_T, flush=True)

    # The cache tests exercise early-return control flow only. Hardware/load
    # helpers are stubs because no numerical work should be reached here.
    original_existing = sys.modules.get('existing')
    stub = types.ModuleType('existing')
    def unexpected(*a, **kw):
        raise AssertionError('An old early-return cache unexpectedly performed work')
    stub.hardware = stub.load_input = stub.save_json = unexpected
    sys.modules['existing'] = stub
    conv = importlib.import_module('run_convergence')
    glob = importlib.import_module('run_global_benchmark')
    with tempfile.TemporaryDirectory(prefix='shadow-before-cache-') as tmp:
        root = Path(tmp)
        config = dict(name='test', repetitions=1, cases=[dict(n=4, k=2, family='rank8_rotated', sizes=[256])])
        config_hash = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
        path = root / 'results/test/n4_k2_rank8_rotated_rep000/summary.json'
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps(dict(status='complete', config_sha256=config_hash,
                                       source_sha256={'deliberately_wrong.py': 'wrong'})))
        conv.ROOT = root
        conv.run(config, 0)
        path = root / 'results/global_rebenchmark/rep000/summary.json'
        path.parent.mkdir(parents=True)
        path.write_text(json.dumps(dict(status='complete', source_sha256={'wrong.py': 'wrong'})))
        glob.ROOT = root
        glob.run(0)
    result['stale_cache_early_return'] = dict(convergence=True, global_benchmark=True)
    print('Reproduced both stale-cache early returns', flush=True)
    if original_existing is not None:
        sys.modules['existing'] = original_existing
    else:
        del sys.modules['existing']

    fit, stats = solve_estimator(c, b, 256, 'OMD', tol_factor=1e-6, omd_maxiter=10000)
    witness = stats.pop('_dual_witness')
    np.savez_compressed(ROOT / 'reports/before_tight_omd.npz', estimate=fit, dual=witness)
    result['tight_omd'] = stats
    result['requested_original_tolerance'] = 2.5e-7
    assert not stats['converged'] and stats['gap'] > 2.5e-7
    (ROOT / 'reports/before_review_reproduction.json').write_text(json.dumps(result, indent=2) + '\n')
    print('Reproduced fixed-eta tight-tolerance failure',
          {k: stats[k] for k in ['eta', 'iterations', 'gap', 'regularized_gap', 'converged']}, flush=True)


if __name__ == '__main__':
    main()
