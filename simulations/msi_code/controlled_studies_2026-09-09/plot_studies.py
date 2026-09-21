"""Render complete controlled block-size and dimension comparisons."""
from pathlib import Path
import csv,json,os,sys
os.environ.setdefault('MPLCONFIGDIR','/tmp/minimax-matplotlib')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

HERE=Path(__file__).resolve().parent
TROOT=HERE.parent/'msi_T_sweep_n8_k2_2026-09-09'
if not TROOT.exists(): TROOT=HERE.parent/'T_sweep_n8_k2_2026-09-09'
new=[json.loads((HERE/'results'/f'rep_{i:02d}'/'summary.json').read_text()) for i in range(20)]
old=[json.loads((TROOT/'results'/f'rep_{i:02d}'/'summary.json').read_text()) for i in range(20)]
BLOCK_ONLY='--block-only' in sys.argv
SMALL_ONLY='--small-only' in sys.argv
NS=[4,6,8] if SMALL_ONLY else [4,6,8,10]
assert all(r['status']=='complete' and len(r['runs'])==5 for r in old)
if not BLOCK_ONLY and not SMALL_ONLY: assert all(r['status']=='complete' and len(r['runs'])==5 for r in new)

def cases(n,k):
    if (n,k)==(8,2):return [next(x for x in r['runs'] if x['T']==16384) for r in old]
    return [next(x for x in r['runs'] if (x['n'],x['k'])==(n,k)) for r in new]

for n,k in ([(8,2),(8,4),(8,8)] if BLOCK_ONLY else [(n,2) for n in NS]+[(8,4),(8,8)]):
    for r in cases(n,k):
        assert r['forward']['converged']
        assert r['forward']['gap']<=.01/8 and r['forward']['regularized_gap']<=.01/8
        for method in ['pls','forward']:
            assert 0<=r[method+'_error']<=2+1e-8
            assert r[method+'_feasibility']['min_eigenvalue']>-1e-9
            assert r[method+'_feasibility']['trace_error']<1e-9

rng=np.random.default_rng(20260911);indices=rng.integers(20,size=(10000,20))
COLORS={'PLS':'#247c87','Forward':'#d1762d'}
plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
summary=[]
def summarize(settings,study):
    all_data={}
    for method in ['PLS','Forward']:
        prefix=method.lower()
        errors=np.array([[r[prefix+'_error'] for r in cases(n,k)] for n,k in settings]).T
        times=np.array([[r['pls_seconds'] if method=='PLS' else r['forward']['seconds'] for r in cases(n,k)] for n,k in settings]).T
        lo,hi=np.quantile(errors[indices].mean(axis=1),[.025,.975],axis=0)
        q25,q75=np.quantile(times,[.25,.75],axis=0)
        data=dict(mean=errors.mean(0),lo=lo,hi=hi,median=np.median(times,axis=0),q25=q25,q75=q75)
        all_data[method]=data
        for i,(n,k) in enumerate(settings):
            summary.append(dict(study=study,n=n,k=k,d=2**n,T=64*2**n,true_rank=8,repetitions=20,method=method,
                                mean_error=float(data['mean'][i]),error_ci_low=float(lo[i]),error_ci_high=float(hi[i]),
                                median_seconds=float(data['median'][i]),seconds_q25=float(q25[i]),seconds_q75=float(q75[i])))
    return all_data

block=summarize([(8,2),(8,4),(8,8)],'block_size')
fig,axes=plt.subplots(1,2,figsize=(13.8,6))
for method,data in block.items():
    for ax,metric,low,high in [(axes[0],'mean','lo','hi'),(axes[1],'median','q25','q75')]:
        ax.plot([2,4,8],data[metric],'o-',color=COLORS[method],lw=2.2,ms=6,label=method)
        ax.fill_between([2,4,8],data[low],data[high],color=COLORS[method],alpha=.19)
for ax in axes:
    ax.set_xticks([2,4,8],['2','4','8\n(global Clifford)'])
    ax.set_xlabel('Qubits per Clifford block k');ax.grid(alpha=.18);ax.set_axisbelow(True);ax.legend(frameon=False)
axes[0].set_ylabel('Mean trace-norm error');axes[0].set_ylim(0,2.08);axes[0].set_title('Reconstruction accuracy',fontsize=14)
axes[1].set_ylabel('Median solver time in seconds (log scale)');axes[1].set_yscale('log');axes[1].set_title('Computation time',fontsize=14)
fig.suptitle('Changing block size, with the state and measurement count fixed',fontsize=16,y=.99)
fig.text(.5,.91,'8 qubits  |  16,384 measurements  |  true rank 8  |  20 repetitions',ha='center',fontsize=12)
fig.text(.5,.025,'Same observations for both estimators at each setting. Error bands: pointwise 95% bootstrap intervals for the mean.\n'
         'Time bands: interquartile ranges. Forward uses the same regularized ADMM, without a special shortcut for global Clifford.\n'
         'Lines connect observed settings. This fixed-state study lies outside the theorem’s sufficient regime.',ha='center',fontsize=10,linespacing=1.4)
fig.tight_layout(rect=[0,.15,1,.87],w_pad=3)
for ext in ['png','svg']:fig.savefig(HERE/f'block_size_comparison.{ext}',dpi=180,facecolor='white')

if BLOCK_ONLY:
    (HERE/'block_summary.json').write_text(json.dumps(summary,indent=2))
    print(json.dumps(summary,indent=2))
    sys.exit(0)

dimension=summarize([(n,2) for n in NS],'dimension')
mem={method:[json.loads((HERE/'memory'/f'n{n}_{method}.json').read_text()) for n in NS] for method in COLORS}
assert all(r['converged'] for vals in mem.values() for r in vals)
fig,axes=plt.subplots(1,2,figsize=(13.8,6));dims=[2**n for n in NS]
for method,data in dimension.items():
    axes[0].plot(dims,data['median'],'o-',color=COLORS[method],lw=2.2,ms=6,label=method)
    axes[0].fill_between(dims,data['q25'],data['q75'],color=COLORS[method],alpha=.19)
    axes[1].plot(dims,[r['peak_process_MiB'] for r in mem[method]],'o-',color=COLORS[method],lw=2.2,ms=6,label=method)
for ax in axes:
    ax.set_xscale('log',base=2);ax.set_xticks(dims,[f'{2**n:,}\n({n} qubits)' for n in NS])
    ax.set_xlabel('State dimension d');ax.grid(alpha=.18);ax.set_axisbelow(True);ax.legend(frameon=False)
axes[0].set_yscale('log');axes[0].set_ylabel('Median solver time in seconds (log scale)');axes[0].set_title('Computation time',fontsize=14)
axes[1].set_ylim(bottom=0);axes[1].set_ylabel('Peak process memory (MiB)');axes[1].set_title('Memory in separate processes',fontsize=14)
fig.suptitle('Increasing dimension with a fixed block size and sample ratio',fontsize=16,y=.99)
fig.text(.5,.91,'2-qubit blocks  |  T/d = 64  |  true rank 8  |  4 CPU threads per task',ha='center',fontsize=12)
fig.text(.5,.025,'Time: 20 repetitions, medians and interquartile ranges; same stopping rule at every dimension.\n'
         'Memory: one separate process per estimator and dimension on replicate 0, including inputs, channel, and solver.\n'
         'Measurement generation and post-solver error evaluation are excluded. These experiments lie outside the theorem’s sufficient regime.',ha='center',fontsize=10,linespacing=1.4)
fig.tight_layout(rect=[0,.15,1,.87],w_pad=3)
suffix='_small' if SMALL_ONLY else ''
for ext in ['png','svg']:fig.savefig(HERE/f'dimension_scaling{suffix}.{ext}',dpi=180,facecolor='white')
with (HERE/f'controlled_summary{suffix}.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=summary[0]);w.writeheader();w.writerows(summary)
(HERE/f'controlled_summary{suffix}.json').write_text(json.dumps(summary,indent=2))
print(json.dumps(summary,indent=2))
