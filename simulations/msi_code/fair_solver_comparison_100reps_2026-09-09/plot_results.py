"""Render verified comparisons only; never drop missing/unconverged cases."""
import argparse
import csv
import json
import os
from pathlib import Path
os.environ.setdefault('MPLCONFIGDIR','/tmp/minimax-matplotlib')
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from benchmark import CASES,HERE

parser=argparse.ArgumentParser();parser.add_argument('--small-only',action='store_true');args=parser.parse_args()
case_indices=list(range(9 if args.small_only else 10))
all_rows={}
for case_index in case_indices:
    rows=[]
    for rep in range(100):
        p=HERE/'results'/f'case_{case_index:02d}'/f'rep_{rep:02d}'/'summary.json'
        r=json.loads(p.read_text())
        assert r['status']=='complete' and r['technical_timing_repeats']==3,(case_index,rep)
        assert len(r['measured'])==6 and len(r['warmups'])==2
        assert all(x['converged'] for x in r['measured']+r['warmups'])
        assert r['pls_full_projection_difference']<1e-8
        for method in ['PLS','Forward']:
            assert r['methods'][method]['max_repeat_frobenius_difference']<1e-8
            assert 0<=r['methods'][method]['trace_norm_error']<=2+1e-8
        pools=r['hardware']['threadpools']
        assert pools and all(x['num_threads']==4 for x in pools if x['user_api']=='blas')
        assert r['hardware']['requested_cpus']=='4'
        assert 'AMD EPYC' in r['hardware'].get('cpu_model',''),r['hardware']
        rows.append(r)
    all_rows[case_index]=rows
assert len({r['hardware']['cpu_model'] for rows in all_rows.values() for r in rows})==1, 'Report distinct CPU models separately.'

rng=np.random.default_rng(20260912);indices=rng.integers(100,size=(10000,100))
colors={'PLS':'#247c87','Forward':'#d1762d'}
markers={'PLS':'o','Forward':'s'}
plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False})
summary=[];paired=[]

def stats(settings,study):
    results={}
    for method in colors:
        err=np.array([[r['methods'][method]['trace_norm_error'] for r in all_rows[j]] for j in settings]).T
        times=np.array([[r['methods'][method]['median_seconds'] for r in all_rows[j]] for j in settings]).T
        low,high=np.quantile(err[indices].mean(axis=1),[.025,.975],axis=0)
        q25,q75=np.quantile(times,[.25,.75],axis=0)
        v=dict(mean=err.mean(0),lo=low,hi=high,median=np.median(times,axis=0),q25=q25,q75=q75)
        results[method]=v
        for i,j in enumerate(settings):
            case=CASES[j]
            summary.append(dict(study=study,case_index=j,**case,d=2**case['n'],true_rank=8,
                  repetitions=100,timing_repeats=3,method=method,solver=all_rows[j][0]['methods'][method]['solver'],
                  mean_trace_norm_error=float(v['mean'][i]),error_ci_low=float(low[i]),error_ci_high=float(high[i]),
                  median_seconds=float(v['median'][i]),seconds_q25=float(q25[i]),seconds_q75=float(q75[i])))
    for j in settings:
        diff=np.array([r['methods']['Forward']['trace_norm_error']-r['methods']['PLS']['trace_norm_error'] for r in all_rows[j]])
        lo,hi=np.quantile(diff[indices].mean(1),[.025,.975])
        paired.append(dict(study=study,case_index=j,**CASES[j],mean_forward_minus_pls=float(diff.mean()),
                           ci_low=float(lo),ci_high=float(hi)))
    return results

def plot_error_time(settings,study,x,xlabels,xlabel,title,subtitle,footnote,filename,logx=False):
    data=stats(settings,study)
    fig,axes=plt.subplots(1,2,figsize=(13.8,6.2))
    for method,v in data.items():
        for ax,metric,lower,upper in [(axes[0],'mean','lo','hi'),(axes[1],'median','q25','q75')]:
            ax.plot(x,v[metric],marker=markers[method],color=colors[method],lw=2.2,ms=7 if method=='PLS' else 4.5,label=method)
            ax.fill_between(x,v[lower],v[upper],color=colors[method],alpha=.19)
    for ax in axes:
        if logx:ax.set_xscale('log',base=2)
        ax.set_xticks(x,xlabels);ax.set_xlabel(xlabel);ax.grid(alpha=.18);ax.set_axisbelow(True);ax.legend(frameon=False)
    axes[0].set_ylim(0,2.06);axes[0].set_ylabel('Mean trace-norm error');axes[0].set_title('Reconstruction accuracy',fontsize=14)
    axes[1].set_yscale('log');axes[1].set_ylabel('Solver time (seconds; log scale)');axes[1].set_title('Time after complete warm-up',fontsize=14)
    fig.suptitle(title,fontsize=16,y=.99);fig.text(.5,.91,subtitle,ha='center',fontsize=12)
    fig.text(.5,.025,footnote,ha='center',fontsize=9.5,linespacing=1.45)
    fig.tight_layout(rect=[0,.17,1,.87],w_pad=3)
    for ext in ['png','svg']:fig.savefig(HERE/f'{filename}.{ext}',dpi=180,facecolor='white')
    plt.close(fig)

basefoot=('100 independent data repetitions; both methods use identical data. Each solver is warmed once, then restarted for 3 timed runs.\n'
          'Error bands: pointwise 95% bootstrap mean intervals. Time bands: IQR across repetition-level median times.\n')
plot_error_time(list(range(5)),'measurements',[1024,4096,16384,65536,262144],
     ['1,024','4,096','16,384','65,536','262,144'],'Measurements T',
     'Varying the number of measurements','8 qubits  |  2-qubit blocks  |  true rank 8  |  4 CPU threads',
     basefoot+'Forward time includes its fresh PLS initialization and convergence checks. These fixed-state experiments do not measure minimax risk.',
     'vary_measurements',True)
plot_error_time([2,5,6],'block_size',[2,4,8],['2','4','8\n(global Clifford)'],'Qubits per block k',
     'Varying the Clifford block size','8 qubits  |  16,384 measurements  |  same true rank-eight state',
     basefoot+'At k=n, both use the exact PLS/forward spectral solution; the global forward point has no numerical regularizer. Lines connect observed settings.',
     'vary_block_size')

ns=[4,6,8] if args.small_only else [4,6,8,10]
ids=[7,8,2] if args.small_only else [7,8,2,9]
dim=stats(ids,'dimension');dims=[2**n for n in ns]
memory={method:[[json.loads((HERE/'memory'/f'n{n}_{method}_rep{rep:03d}.json').read_text()) for rep in range(100)] for n in ns] for method in colors}
assert all(r['solver']['converged'] for vals in memory.values() for group in vals for r in group)
assert all(r['hardware']['requested_cpus']=='4' for vals in memory.values() for group in vals for r in group)
memory_summary=[]
for method,groups in memory.items():
    for n,group in zip(ns,groups):
        values=np.array([r['peak_process_MiB'] for r in group])
        memory_summary.append(dict(n=n,d=2**n,method=method,profiles=100,median_MiB=float(np.median(values)),q25_MiB=float(np.quantile(values,.25)),q75_MiB=float(np.quantile(values,.75))))
(HERE/'memory_summary.json').write_text(json.dumps(memory_summary,indent=2)+'\n')
fig,axes=plt.subplots(1,2,figsize=(13.8,6.2))
for method,v in dim.items():
    axes[0].plot(dims,v['median'],marker=markers[method],lw=2.2,color=colors[method],label=method)
    axes[0].fill_between(dims,v['q25'],v['q75'],color=colors[method],alpha=.19)
    mem=np.array([[r['peak_process_MiB'] for r in group] for group in memory[method]])
    axes[1].plot(dims,np.median(mem,axis=1),marker=markers[method],lw=2.2,color=colors[method],label=method)
    lo,hi=np.quantile(mem,[.25,.75],axis=1)
    axes[1].fill_between(dims,lo,hi,color=colors[method],alpha=.19)
for ax in axes:
    ax.set_xscale('log',base=2);ax.set_xticks(dims,[f'{d:,}\n({n} qubits)' for n,d in zip(ns,dims)])
    ax.set_xlabel('Dimension d');ax.grid(alpha=.18);ax.set_axisbelow(True);ax.legend(frameon=False)
axes[0].set_yscale('log');axes[0].set_ylabel('Solver time (seconds; log scale)');axes[0].set_title('Time after complete warm-up',fontsize=14)
axes[1].set_ylim(bottom=0);axes[1].set_ylabel('Peak process memory (MiB)');axes[1].set_title('Memory in separate fresh processes',fontsize=14)
fig.suptitle('Varying the state dimension',fontsize=16,y=.99)
fig.text(.5,.91,'2-qubit blocks  |  T/d = 64  |  true rank 8  |  same tolerances and 4 CPU threads',ha='center',fontsize=12)
fig.text(.5,.025,'Time: 100 independent inputs; median of 3 fresh timed runs after complete warm-up per input; band is the interquartile range.\n'
         'Memory: 100 fresh-process profiles per estimator/dimension; median and IQR, including inputs, channel, solver and output.\n'
         'Sampling and post-solver error evaluation are excluded. All plotted solves passed the numerical convergence and feasibility checks.',ha='center',fontsize=9.5,linespacing=1.45)
fig.tight_layout(rect=[0,.17,1,.87],w_pad=3)
suffix='_small' if args.small_only else ''
for ext in ['png','svg']:fig.savefig(HERE/f'vary_dimension{suffix}.{ext}',dpi=180,facecolor='white')
plt.close(fig)

with (HERE/f'summary{suffix}.csv').open('w',newline='') as f:
    w=csv.DictWriter(f,fieldnames=summary[0]);w.writeheader();w.writerows(summary)
(HERE/f'summary{suffix}.json').write_text(json.dumps(dict(rows=summary,paired_error_differences=paired),indent=2)+'\n')
(HERE/f'validation{suffix}.json').write_text(json.dumps(dict(status='passed',unique_cases=len(case_indices)*100,
          fresh_measured_solves=len(case_indices)*100*6,complete_warmup_solves=len(case_indices)*100*2,
          cpu_models=sorted({r['hardware']['cpu_model'] for rows in all_rows.values() for r in rows}),
          all_converged=True,all_feasible=True,all_pls_full_projection_checks_passed=True),indent=2)+'\n')
print('Rendered verified figures.',len(case_indices)*100,'unique paired inputs.',flush=True)
