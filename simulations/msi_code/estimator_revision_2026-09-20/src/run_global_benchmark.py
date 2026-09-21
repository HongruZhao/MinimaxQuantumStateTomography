"""Rerun the original 100 global datasets with the shared spectral solver."""
import argparse
import gc
import hashlib
import time
from pathlib import Path
import numpy as np
from estimators import METHODS, Channel, solve_estimator, independent_validation
from existing import load_input, save_json, hardware

ROOT = Path(__file__).resolve().parent.parent


def run(rep):
    out = ROOT / 'results' / 'global_rebenchmark' / ('rep%03d' % rep)
    out.mkdir(parents=True, exist_ok=True)
    status_path = out / 'summary.json'
    if status_path.exists():
        import json
        if json.loads(status_path.read_text()).get('status') == 'complete':
            return
    case = dict(n=8, k=8, T=16384)
    b, source = load_input(case, rep)
    c = Channel(8, 8)
    rho = np.diag(np.r_[np.full(8, 1 / 8), np.zeros(248)])
    row = dict(case=case, rep=rep, status='running', input_source=source,
               input_sha256=hashlib.sha256(b.tobytes()).hexdigest(),
               hardware=hardware(), warmups=[], measured=[], methods={},
               source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in Path(__file__).parent.glob('*.py')})
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
    save_json(status_path, row)
    print('GLOBAL', rep, row['pairwise_frobenius_differences'], flush=True)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('chunk', type=int)
    args = p.parse_args()
    assert 0 <= args.chunk < 10
    for rep in range(10 * args.chunk, 10 * args.chunk + 10):
        run(rep)
