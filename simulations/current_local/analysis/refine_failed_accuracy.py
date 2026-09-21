"""Replay the single capped accuracy-stress fit; preserve the first attempt."""
from pathlib import Path
import json
import sys

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))
from estimators import Channel, solve_estimator, independent_validation
from runtime_io import hardware, save_json
from run_identity import (file_hash, cache_identity, check_cached_result,
                          artifact_hashes, seal_result, source_hashes)


def main():
    original = ROOT / 'results/review_fresh/n4_k2_polynomial_rotated_rep003'
    initial = json.loads((original / 'summary.json').read_text())
    failed = [r for r in initial['records'] if not r['validation']['accepted']]
    assert len(failed) == 1
    record = failed[0]
    assert record['T'] == 1048576 and record['profile'] == 'OMD_tight'
    folder = ROOT / 'results/review_accuracy_extension'
    folder.mkdir(parents=True, exist_ok=True)
    options = dict(tol_factor=record['tol_factor'], omd_maxiter=100000,
                   maxiter=300000, max_seconds=1200.)
    config = dict(options=options, method='OMD', T=record['T'],
                  driver_sha256=file_hash(__file__))
    inputs = {str(original.relative_to(ROOT) / p): file_hash(original / p)
              for p in ['data.npz', 'summary.json']}
    identity = cache_identity(config, inputs)
    if check_cached_result(folder / 'summary.json', identity) is not None:
        return
    with np.load(original / 'data.npz') as data:
        position = list(data['sizes']).index(record['T'])
        b, rho = data['means'][position], data['rho']
    c = Channel(4, 2)
    x, stats = solve_estimator(c, b, record['T'], 'OMD', **options)
    check = independent_validation(c, b, record['T'], x, 'OMD', stats,
                                   rho=rho, tol_factor=record['tol_factor'])
    dual = stats.pop('_dual_witness')
    np.savez_compressed(folder / 'estimate.npz', estimate=x, dual=dual)
    row = dict(status='complete' if check['accepted'] else 'incomplete_methods',
               case=initial['case'], rep=initial['rep'], T=record['T'],
               profile=record['profile'], method='OMD', tol_factor=record['tol_factor'],
               hardware=hardware(), source_sha256=source_hashes(),
               cache_identity=identity, stats=stats, validation=check,
               original_attempt=str(original.relative_to(ROOT)),
               original_attempt_seconds=record['stats']['wall_seconds'])
    row['artifact_sha256'] = artifact_hashes(folder)
    save_json(folder / 'summary.json', seal_result(row))
    print(json.dumps(dict(accepted=check['accepted'], iterations=stats['iterations'],
                          gap=check['omd_gap'], regularized_gap=check['regularized_gap'],
                          requested=stats['original_gap_tolerance'],
                          seconds=stats['wall_seconds'])), flush=True)
    assert check['accepted'], 'Extension did not meet the unchanged requested accuracy.'


if __name__ == '__main__':
    main()
