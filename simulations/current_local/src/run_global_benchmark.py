"""Rerun the original 100 global datasets with the shared spectral solver."""
import argparse
import gc
import hashlib
import time
from pathlib import Path
import numpy as np
from estimators import METHODS, Channel, solve_estimator, independent_validation
from runtime_io import save_json, hardware
from run_identity import (cache_identity, check_cached_result, array_hash, source_hashes,
                          artifact_hashes, seal_result, StaleResultError)

ROOT = Path(__file__).resolve().parent.parent


def load_input(case, rep):
    from existing import load_input as original_loader
    return original_loader(case, rep)


def run(rep):
    out = ROOT / 'results' / 'global_rebenchmark' / ('rep%03d' % rep)
    out.mkdir(parents=True, exist_ok=True)
    status_path = out / 'summary.json'
    case = dict(n=8, k=8, T=16384)
    if status_path.exists():
        import json
        prior = json.loads(status_path.read_text())
        if prior.get('source_sha256') != source_hashes():
            raise StaleResultError('Global benchmark source changed; use a new revision directory.')
    b, source = load_input(case, rep)
    identity = cache_identity(dict(case=case, rep=rep, warmups=1, timed_repeats=3),
                              {'empirical_mean': array_hash(b), 'origin': source})
    if check_cached_result(status_path, identity) is not None:
        return
    c = Channel(8, 8)
    rho = np.diag(np.r_[np.full(8, 1 / 8), np.zeros(248)])
    row = dict(case=case, rep=rep, status='running', input_source=source,
               input_sha256=hashlib.sha256(b.tobytes()).hexdigest(),
               hardware=hardware(), warmups=[], measured=[], methods={},
               source_sha256=source_hashes(), cache_identity=identity)
    order = list(METHODS[rep % 3:] + METHODS[:rep % 3])
    for method in order:
        x, stats = solve_estimator(c, b, case['T'], method)
        check = independent_validation(c, b, case['T'], x, method, stats, rho)
        assert check['accepted']
        row['warmups'].append(dict(method=method, stats=stats, validation=check))
        del x
        gc.collect()
    estimates = {}
    for repeat in range(3):
        for method in order if repeat % 2 == 0 else order[::-1]:
            gc.collect()
            x, stats = solve_estimator(c, b, case['T'], method)
            check = independent_validation(c, b, case['T'], x, method, stats, rho)
            assert check['accepted']
            row['measured'].append(dict(method=method, repeat=repeat, stats=stats, validation=check))
            if method in estimates:
                assert np.linalg.norm(estimates[method] - x) < 1e-12
            estimates[method] = x
    row['pairwise_frobenius_differences'] = {m: float(np.linalg.norm(estimates[m] - estimates['PLS'])) for m in METHODS}
    assert max(row['pairwise_frobenius_differences'].values()) < 1e-12
    for method in METHODS:
        items = [r for r in row['measured'] if r['method'] == method]
        row['methods'][method] = dict(median_seconds=float(np.median([r['stats']['wall_seconds'] for r in items])),
                                      validation=items[0]['validation'], solver=items[0]['stats']['solver'])
    np.savez_compressed(out / 'estimates.npz', **{m.replace('-', '_'): x for m, x in estimates.items()})
    row['status'] = 'complete'
    row['artifact_sha256'] = artifact_hashes(out)
    save_json(status_path, seal_result(row))
    print('GLOBAL', rep, row['pairwise_frobenius_differences'], flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('chunk', type=int)
    args = p.parse_args()
    assert 0 <= args.chunk < 10
    for rep in range(10 * args.chunk, 10 * args.chunk + 10):
        run(rep)
