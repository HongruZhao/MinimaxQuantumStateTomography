"""Plot only a complete, converged 20-by-5 paired Monte Carlo study."""
from pathlib import Path
import csv, json, os
os.environ.setdefault('MPLCONFIGDIR', '/tmp/minimax-matplotlib')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
SIZES = np.array([1024, 4096, 16384, 65536, 262144])
reps = [json.loads((HERE/'results'/f'rep_{i:02d}'/'summary.json').read_text()) for i in range(20)]
assert all(r['status'] == 'complete' and len(r['runs']) == 5 for r in reps)
assert all(r['n'] == 8 and r['k'] == 2 and r['d'] == 256 and r['true_rank'] == 8 for r in reps)
for rep in reps:
    assert [r['T'] for r in rep['runs']] == list(SIZES)
    for r in rep['runs']:
        assert r['forward']['converged']
        assert r['forward']['gap'] <= .01*r['gamma']
        assert r['forward']['regularized_gap'] <= .01*r['gamma']
        assert all(r[m+'_feasibility']['min_eigenvalue'] > -1e-9 and
                   r[m+'_feasibility']['trace_error'] < 1e-9 for m in ['pls','forward'])
errors = {
    'PLS': np.array([[r['pls_error'] for r in rep['runs']] for rep in reps]),
    'Forward': np.array([[r['forward_error'] for r in rep['runs']] for rep in reps]),
}
times = {
    'PLS': np.array([[r['pls_seconds'] for r in rep['runs']] for rep in reps]),
    'Forward': np.array([[r['forward']['seconds'] for r in rep['runs']] for rep in reps]),
}
assert all(np.all((e>=0)&(e<=2+1e-8)) for e in errors.values())
rng = np.random.default_rng(20260910)
resample = rng.integers(20, size=(10000,20))
summary = []
for i,T in enumerate(SIZES):
    row = dict(T=int(T),n=8,k=2,d=256,true_rank=8,repetitions=20)
    for method in errors:
        lo,hi = np.quantile(errors[method][resample,i].mean(axis=1),[.025,.975])
        row.update({method+'_mean_error':float(errors[method][:,i].mean()),
                    method+'_error_ci_low':float(lo),method+'_error_ci_high':float(hi),
                    method+'_median_seconds':float(np.median(times[method][:,i])),
                    method+'_seconds_q25':float(np.quantile(times[method][:,i],.25)),
                    method+'_seconds_q75':float(np.quantile(times[method][:,i],.75))})
    gain = errors['PLS'][:,i]-errors['Forward'][:,i]
    lo,hi = np.quantile(gain[resample].mean(axis=1),[.025,.975])
    row.update(paired_mean_error_gain=float(gain.mean()),paired_gain_ci_low=float(lo),paired_gain_ci_high=float(hi))
    summary.append(row)
with (HERE/'summary.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=summary[0]);w.writeheader();w.writerows(summary)
(HERE/'summary.json').write_text(json.dumps(summary,indent=2))
raw=[]
for rep in reps:
    for r in rep['runs']:
        raw.append(dict(rep=rep['rep'],T=r['T'],pls_error=r['pls_error'],forward_error=r['forward_error'],
                        pls_seconds=r['pls_seconds'],forward_seconds=r['forward']['seconds'],
                        forward_iterations=r['forward']['iterations'],gap=r['forward']['gap'],
                        regularized_gap=r['forward']['regularized_gap'],host=rep['host']))
with (HERE/'replicate_results.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=raw[0]);w.writeheader();w.writerows(raw)

plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
fig,axes=plt.subplots(1,2,figsize=(13.8,6.0))
colors={'PLS':'#247c87','Forward':'#d1762d'}
for method in errors:
    mean=errors[method].mean(axis=0)
    lo,hi=np.quantile(errors[method][resample].mean(axis=1),[.025,.975],axis=0)
    axes[0].plot(SIZES,mean,'o-',color=colors[method],lw=2.2,ms=6,label=method)
    axes[0].fill_between(SIZES,lo,hi,color=colors[method],alpha=.19)
    median=np.median(times[method],axis=0)
    q25,q75=np.quantile(times[method],[.25,.75],axis=0)
    axes[1].plot(SIZES,median,'o-',color=colors[method],lw=2.2,ms=6,label=method)
    axes[1].fill_between(SIZES,q25,q75,color=colors[method],alpha=.19)
for ax in axes:
    ax.set_xscale('log');ax.set_yscale('log')
    ax.set_xticks(SIZES,[f'{T:,}' for T in SIZES])
    ax.set_xlabel('Number of measurements T')
    ax.grid(which='major',alpha=.2);ax.set_axisbelow(True)
    ax.legend(frameon=False)
axes[0].set_title('Reconstruction accuracy',fontsize=14)
axes[0].set_ylabel('Mean trace-norm error (log scale)')
axes[0].axhline(2,color='#777777',ls=':',lw=1)
axes[0].set_ylim(min(v.min() for v in errors.values())*.8,2.2)
axes[1].set_title('Computation time',fontsize=14)
axes[1].set_ylabel('Median solver time in seconds (log scale)')
fig.suptitle('Increasing the measurement count, with the state and circuit fixed',fontsize=16,y=.99)
fig.text(.5,.91,'8 qubits  |  2-qubit Clifford blocks  |  true rank 8  |  20 repetitions',ha='center',fontsize=12)
fig.text(.5,.025,'Same data for both estimators; nested measurements within each independent repetition.\n'
         'Error bands: pointwise 95% bootstrap intervals for the mean. Time bands: interquartile ranges.\n'
         'Solver time excludes data generation. These small-system experiments lie outside the theorem’s sufficient regime.',
         ha='center',fontsize=10,linespacing=1.4)
fig.tight_layout(rect=[0,.15,1,.87],w_pad=3)
fig.savefig(HERE/'T_sweep_comparison.png',dpi=180,facecolor='white')
fig.savefig(HERE/'T_sweep_comparison.svg',facecolor='white')
print(json.dumps(summary,indent=2))
