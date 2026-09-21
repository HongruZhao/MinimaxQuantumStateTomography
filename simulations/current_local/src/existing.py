"""Paired, fully warmed, fresh-start timing of the two state estimators."""
import argparse
import gc
import hashlib
import json
import os
import platform
import socket
import time
from pathlib import Path

import numpy as np
import scipy
from threadpoolctl import threadpool_info

import accelerated
from baseline import FastChannel, herm, opnorm, trnorm
from projections import Partial, scipy_density, scipy_nuclear

HERE = Path('/projects/standard/galin/shared/hongru/Clifford_Minimax/fair_solver_comparison_100reps_2026-09-09')
MSI = Path('/projects/standard/galin/shared/hongru/Clifford_Minimax')
SIZES = [1024, 4096, 16384, 65536, 262144]
CASES = ([dict(n=8, k=2, T=t) for t in SIZES]
         + [dict(n=8, k=4, T=16384), dict(n=8, k=8, T=16384)]
         + [dict(n=4, k=2, T=1024), dict(n=6, k=2, T=4096), dict(n=10, k=2, T=65536)])


def save_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix('.tmp')
    tmp.write_text(json.dumps(value, indent=2) + '\n')
    tmp.replace(path)


def load_input(case, rep, root=MSI):
    n, k, T = case['n'], case['k'], case['T']
    if rep >= 20:
        source = HERE/'data'/f'rep_{rep:03d}'/f'n{n}_k{k}'/'data.npz'
        with np.load(source) as data:
            index = list(data['sizes']).index(T)
            b = data['means'][index].copy()
    elif (n, k) == (8, 2):
        source = root/'T_sweep_n8_k2_2026-09-09'/'results'/f'rep_{rep:02d}'/'data.npz'
        with np.load(source) as data:
            index = list(data['sizes']).index(T)
            b = data['means'][index].copy()
    else:
        source = root/'controlled_studies_2026-09-09'/'results'/f'rep_{rep:02d}'/f'n{n}_k{k}'/'data.npz'
        with np.load(source) as data:
            b = data['mean'].copy()
    assert b.shape == (2**n, 2**n)
    assert abs(np.trace(b).real - 1) < 1e-9
    assert np.linalg.norm(b-b.conj().T) < 1e-9
    b.flags.writeable = False
    return b, str(source)


class Channel(FastChannel):
    def pls(self, b):
        partial = Partial()
        if self.k == self.n:
            a = (self.d+1)*b - np.eye(self.d)
        else:
            a = self.apply(b, 'inverse')
        x = partial.density(a)
        self.last_pls = dict(expansions=partial.expansions, active_rank=partial.ranks[-1],
                             projection_calls=partial.calls)
        return x


def solve_fresh(c, b, T, method):
    """The only state input is b. Warm-up outputs are never passed here."""
    start = time.perf_counter()
    if method == 'PLS':
        x = c.pls(b)
        stats = dict(solver='spectral_pls', converged=True, pls_projection=dict(c.last_pls))
    elif c.k == c.n:
        x = c.pls(b)
        stats = dict(solver='exact_global_forward', converged=True, iterations=0,
                     eta=0., pls_projection=dict(c.last_pls),
                     certificate='Analytic global-Clifford reduction; independently checked after timing.')
    else:
        partial = Partial()
        accelerated.project_density = partial.density
        accelerated.nuclear_project = scipy_nuclear
        y = (c.d+1)*b - np.eye(c.d)
        x, stats = accelerated.solve(c, y, T, maxiter=4000)
        stats.update(solver='regularized_admm', eta=.005*min(1., np.sqrt(c.d/T)),
                     initialization='Fresh internal PLS, included in time.',
                     pls_projection=dict(c.last_pls), density_projection_calls=partial.calls,
                     density_projection_expansions=partial.expansions,
                     last_density_rank=partial.ranks[-1])
    elapsed = time.perf_counter() - start
    stats['wall_seconds'] = elapsed
    return x, stats


def validate_output(c, b, T, x, method, stats):
    eigs = np.linalg.eigvalsh(herm(x))
    trace_error = float(abs(np.trace(x)-1))
    min_eigenvalue = float(eigs[0])
    assert trace_error < 1e-9 and min_eigenvalue > -1e-9
    assert stats['converged']
    gamma = min(1., np.sqrt(c.d/T))
    if stats['solver'] == 'regularized_admm':
        assert stats['gap'] <= .01*gamma and stats['regularized_gap'] <= .01*gamma
    extra = {}
    if stats['solver'] == 'exact_global_forward':
        y = (c.d+1)*b - np.eye(c.d)
        w = np.linalg.eigvalsh(herm(y));s = w[::-1]
        thresholds = (np.cumsum(s)-1)/np.arange(1, c.d+1)
        theta = thresholds[np.flatnonzero(s>thresholds)[-1]]
        optimum = max(0., float(theta), -float(w[0]))
        residual = opnorm(y-x)
        assert abs(residual-optimum) < 1e-8
        assert np.max(np.abs(c.ell-1)) < 1e-10
        extra = dict(objective=residual, analytic_optimum=optimum,
                     original_gap=max(0., residual-optimum))
    rho = np.diag(np.r_[np.full(8, 1/8), np.zeros(c.d-8)])
    error = trnorm(x-rho)
    assert 0 <= error <= 2+1e-8
    return dict(trace_error=trace_error, min_eigenvalue=min_eigenvalue,
                trace_norm_error=error, **extra)


def hardware():
    info = dict(host=socket.gethostname(), platform=platform.platform(), numpy=np.__version__,
                scipy=scipy.__version__, threadpools=threadpool_info(),
                job_id=os.getenv('SLURM_JOB_ID'), array_id=os.getenv('SLURM_ARRAY_JOB_ID'),
                requested_cpus=os.getenv('SLURM_CPUS_PER_TASK'), cpu_binding=os.getenv('SLURM_CPU_BIND_LIST'),
                main_thread_affinity=sorted(os.sched_getaffinity(0)) if hasattr(os, 'sched_getaffinity') else None)
    tasks = Path('/proc/self/task')
    if tasks.exists():
        affinity = {}
        for task in tasks.iterdir():
            try:affinity[task.name] = sorted(os.sched_getaffinity(int(task.name)))
            except ProcessLookupError:pass
        info['thread_affinities'] = affinity
        info['observed_cpu_union'] = sorted({cpu for cpus in affinity.values() for cpu in cpus})
    cpuinfo = Path('/proc/cpuinfo')
    if cpuinfo.exists():
        info['cpu_model'] = next(x.split(':',1)[1].strip() for x in cpuinfo.read_text().splitlines()
                                 if x.startswith('model name'))
    return info


def run_case(case_index, rep, root=MSI, timing_repeats=3):
    case = CASES[case_index]
    out = HERE/'results'/f'case_{case_index:02d}'/f'rep_{rep:02d}'
    prior = out/'summary.json'
    if prior.exists():
        old=json.loads(prior.read_text())
        if old['status']=='complete':
            assert old['technical_timing_repeats']==timing_repeats
            return old
    row = dict(case_index=case_index, rep=rep, **case, d=2**case['n'], true_rank=8,
               technical_timing_repeats=timing_repeats, hardware=hardware(),
               status='started', warmups=[], measured=[])
    save_json(out/'summary.json', row)
    start = time.perf_counter();b, source = load_input(case, rep, root)
    row.update(input_source=source, input_sha256=hashlib.sha256(b.tobytes()).hexdigest(),
               input_load_seconds=time.perf_counter()-start)
    start=time.perf_counter();c=Channel(case['n'], case['k'])
    row['channel_setup_seconds']=time.perf_counter()-start
    warm_order = ['PLS','Forward'] if (rep+case_index)%2==0 else ['Forward','PLS']
    for method in warm_order:
        print('WARMUP', case_index, rep, method, flush=True)
        x, stats = solve_fresh(c, b, case['T'], method)
        assert stats['converged'], 'Full warm-up did not converge.'
        row['warmups'].append(dict(method=method, **stats))
        del x
        gc.collect()
        row['status']='warming';save_json(out/'summary.json', row)
    row['hardware_after_warmup'] = hardware()
    outputs={'PLS':[],'Forward':[]}
    for repeat in range(timing_repeats):
        order=['PLS','Forward'] if (rep+case_index+repeat)%2==0 else ['Forward','PLS']
        for position, method in enumerate(order):
            gc.collect()
            print('MEASURE', case_index, rep, repeat, method, flush=True)
            x, stats=solve_fresh(c,b,case['T'],method)
            outputs[method].append(x)
            row['measured'].append(dict(method=method, timing_repeat=repeat, position=position,
                                        method_order=order, **stats))
            row['status']='measuring';save_json(out/'summary.json',row)
    row['methods']={}
    for method in ['PLS','Forward']:
        records=[r for r in row['measured'] if r['method']==method]
        checks=[validate_output(c,b,case['T'],x,method,r) for x,r in zip(outputs[method],records)]
        for record, check in zip(records, checks):record['validation']=check
        first=outputs[method][0]
        maxdiff=max(float(np.linalg.norm(x-first)) for x in outputs[method])
        assert maxdiff<1e-8, 'Repeated fresh solves changed their output.'
        row['methods'][method]=dict(median_seconds=float(np.median([r['wall_seconds'] for r in records])),
                                    trace_norm_error=checks[0]['trace_norm_error'],
                                    max_repeat_frobenius_difference=maxdiff,
                                    solver=records[0]['solver'])
        np.save(out/(method.lower()+'.npy'),first)
    gold=scipy_density(c.apply(b,'inverse'))
    difference=float(np.linalg.norm(outputs['PLS'][0]-gold))
    assert difference<1e-8, 'Adaptive PLS disagrees with the full spectral projection.'
    row['pls_full_projection_difference']=difference
    row['status']='complete';save_json(out/'summary.json',row)
    print('COMPLETE',case_index,rep,json.dumps(row['methods']),flush=True)
    return row


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('task',type=int)
    parser.add_argument('--root',type=Path,default=MSI)
    args=parser.parse_args();assert 0<=args.task<800
    run_case(args.task//80,20+args.task%80,args.root)
