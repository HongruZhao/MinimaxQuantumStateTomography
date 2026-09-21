"""Fixed-state Monte Carlo study varying sample size only."""
import json, os, resource, socket, sys, time
from pathlib import Path
import numpy as np
import scipy
from threadpoolctl import threadpool_info
import accelerated
from baseline import FastChannel, trnorm
from projections import Partial, scipy_nuclear
from large_simulation import records

REP = int(sys.argv[1])
assert 0 <= REP < 20
N, K, RANK = 8, 2, 8
D = 2**N
SIZES = [1024, 4096, 16384, 65536, 262144]
SEED = [20260910, N, K, RANK, REP]
OUT = Path('results') / f'rep_{REP:02d}'
OUT.mkdir(parents=True, exist_ok=True)
result = dict(n=N, k=K, d=D, true_rank=RANK, rep=REP, seed=SEED,
              sample_sizes=SIZES, state='uniform mixture of first eight computational basis states',
              sampling='nested records within replicate; independent replicates',
              job_id=os.getenv('SLURM_JOB_ID'), host=socket.gethostname(),
              numpy=np.__version__, scipy=scipy.__version__,
              threads=threadpool_info(), status='started', runs=[])

def save():
    result['process_maxrss_KiB'] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    tmp = OUT / 'summary.tmp'
    tmp.write_text(json.dumps(result, indent=2))
    tmp.replace(OUT / 'summary.json')

class Channel(FastChannel):
    def pls(self, b):
        return Partial().density(self.apply(b, 'inverse'))

save()
t = time.perf_counter()
c = Channel(N, K)
result['channel_seconds'] = time.perf_counter() - t
lam = np.r_[np.full(RANK, 1/RANK), np.zeros(D-RANK)]
rho = np.diag(lam)
t = time.perf_counter()
means = records(N, np.eye(D, dtype=complex), lam, SIZES, SEED)
result['sampling_seconds_all_sizes'] = time.perf_counter() - t
np.savez_compressed(OUT / 'data.npz', means=means, lam=lam, sizes=SIZES)
assert np.max(np.abs(np.trace(means, axis1=1, axis2=2)-1)) < 1e-10
result['status'] = 'data ready'
save()
print('DATA READY', REP, result['sampling_seconds_all_sizes'], flush=True)
# Warm small spectral library calls outside the timers for either estimator.
Partial().density(np.eye(16)/16)
scipy_nuclear(np.eye(16), 1.)
for i, (T, b) in enumerate(zip(SIZES, means)):
    row = dict(T=T, T_over_d=T/D, gamma=min(1., np.sqrt(D/T)))
    # Alternate execution order to limit systematic timing bias.
    order = ['PLS', 'Forward'] if (REP+i) % 2 == 0 else ['Forward', 'PLS']
    row['method_order'] = order
    estimates = {}
    for method in order:
        if method == 'PLS':
            t = time.perf_counter()
            x = c.pls(b)
            elapsed = time.perf_counter() - t
            row['pls_seconds'] = elapsed
            row['pls_error'] = trnorm(x-rho)
        else:
            partial = Partial()
            accelerated.project_density = partial.density
            accelerated.nuclear_project = scipy_nuclear
            x, dg = accelerated.solve(c, (D+1)*b-np.eye(D), T, maxiter=4000)
            row['forward'] = dg
            row['forward_error'] = trnorm(x-rho)
            row['density_projection_expansions'] = partial.expansions
        trace_error = abs(np.trace(x).real-1)
        min_eig = np.linalg.eigvalsh(x)[0]
        assert trace_error < 1e-9 and min_eig > -1e-9
        row[method.lower()+'_feasibility'] = dict(trace_error=float(trace_error), min_eigenvalue=float(min_eig))
        estimates[method.lower()] = x
    result['runs'].append(row)
    result['status'] = f'completed {i+1} of {len(SIZES)} sample sizes'
    save()
    np.savez_compressed(OUT/f'estimates_T{T}.npz', **estimates)
    print('RESULT', REP, T, row['pls_error'], row['forward_error'], row['pls_seconds'], row['forward']['seconds'], row['forward']['converged'], flush=True)
result['status'] = 'complete' if all(r['forward']['converged'] for r in result['runs']) else 'solver limit'
save()
