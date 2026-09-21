"""New paired-data convergence study; raw estimates and all failures retained."""
import argparse
import hashlib
import json
import time
from pathlib import Path
import numpy as np
from estimators import METHODS, Channel, solve_estimator, independent_validation
from existing import hardware, save_json
from sampling import sample_means

ROOT = Path(__file__).resolve().parent.parent


def run(config, task):
    cases = config['cases']
    reps = config['repetitions']
    case = cases[task // reps]
    rep = task % reps
    name = 'n%d_k%d_%s_rep%03d' % (case['n'], case['k'], case['family'], rep)
    out = ROOT / 'results' / config['name'] / name
    out.mkdir(parents=True, exist_ok=True)
    config_hash = hashlib.sha256(json.dumps(config, sort_keys=True).encode()).hexdigest()
    data_path = out / 'data.npz'
    status_path = out / 'summary.json'
    if status_path.exists():
        prior = json.loads(status_path.read_text())
        if prior.get('status') == 'complete':
            assert prior['config_sha256'] == config_hash
            return
    row = dict(case=case, rep=rep, config_sha256=config_hash, status='started',
               hardware=hardware(), records=[],
               source_sha256={p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in Path(__file__).parent.glob('*.py')})
    save_json(status_path, row)
    start = time.perf_counter()
    if data_path.exists():
        with np.load(data_path) as data:
            rho, means = data['rho'], data['means']
            assert list(data['sizes']) == case['sizes']
        row['sampling'] = json.loads((out / 'sampling.json').read_text())
    else:
        rho, means, counts, info = sample_means(case['n'], case['k'], case['family'], case['sizes'], rep,
                                               cache_dir=ROOT / 'assets')
        np.savez_compressed(data_path, rho=rho, means=means, sizes=case['sizes'], counts=counts)
        row['sampling'] = info
        save_json(out / 'sampling.json', info)
    row['data_seconds'] = time.perf_counter() - start
    row['data_sha256'] = hashlib.sha256(data_path.read_bytes()).hexdigest()
    row['status'] = 'solving'
    save_json(status_path, row)
    c = Channel(case['n'], case['k'])
    for T, b in zip(case['sizes'], means):
        saved = {}
        for method in METHODS:
            print(name, T, method, 'START', flush=True)
            x, stats = solve_estimator(c, b, T, method, **config.get('solver_options', {}))
            check = independent_validation(c, b, T, x, method, stats, rho=rho)
            dual = stats.pop('_dual_witness', None)
            key = method.replace('-', '_')
            saved[key] = x
            if dual is not None:
                saved[key + '_dual'] = dual
            record = dict(T=T, method=method, stats=stats, validation=check,
                          mean_sha256=hashlib.sha256(b.tobytes()).hexdigest())
            row['records'].append(record)
            save_json(status_path, row)
            print(name, T, method, 'DONE', json.dumps({k: check[k] for k in ['accepted', 'trace_norm_error', 'mw_gap']}), flush=True)
        if c.k == c.n:
            differences = {m: float(np.linalg.norm(saved['PLS'] - saved[m.replace('-', '_')])) for m in METHODS}
            assert max(differences.values()) < 1e-12
            row.setdefault('global_output_differences', []).append(dict(T=T, differences=differences))
        np.savez_compressed(out / ('estimates_T%d.npz' % T), **saved)
    row['failed_records'] = [dict(T=r['T'], method=r['method']) for r in row['records'] if not r['validation']['accepted']]
    row['status'] = 'complete' if not row['failed_records'] else 'incomplete_methods'
    save_json(status_path, row)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('config', type=Path)
    p.add_argument('task', type=int)
    args = p.parse_args()
    config = json.loads(args.config.read_text())
    assert 0 <= args.task < len(config['cases']) * config['repetitions']
    run(config, args.task)
