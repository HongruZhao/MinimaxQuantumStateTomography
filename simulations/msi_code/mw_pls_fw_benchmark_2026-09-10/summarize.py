"""Validate and plot complete 100-repetition cells; incomplete cells are explicit."""
import argparse,json,math,csv,os
from pathlib import Path
import numpy as np
os.environ.setdefault('MPLCONFIGDIR','/tmp/mwfw-matplotlib')
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from existing import CASES
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('--root',type=Path,default=ROOT);p.add_argument('--output',type=Path);p.add_argument('--allow-partial',action='store_true');a=p.parse_args()
base=a.root;out=a.output or base/'reports';out.mkdir(parents=True,exist_ok=True)
names=['PLS','OMD_strict','OMD_stat','MW_line_search_identity','MW_line_search_pls','MW_deterministic_identity','MW_deterministic_pls']
labels=['PLS','OMD: strict gap','OMD: statistical gap','MW-FW: line search, I/d','MW-FW: line search, PLS start','MW-FW: fixed steps, I/d','MW-FW: fixed steps, PLS start']
colors=['#247c87','#c46826','#dbaa3d','#8b6bb0','#267345','#389fbd','#b24880']
styles=['-','-','--','--','-','--','-']
phase_a={7,8,2,5,6,9};rows={};missing=[];cell=[];memory={};models=set();maxtrace=0.;mineig=1.
input_hashes={};matched_memory_inputs=0

def hardware(h):
    assert h['requested_cpus']=='4'
    pools=[v for v in h['threadpools'] if v['user_api']=='blas']
    assert pools and all(v['num_threads']==4 for v in pools)
    assert h['cpu_model']=='AMD EPYC 7763 64-Core Processor'
    models.add(h['cpu_model'])

def check(s,v,d,T,method,k):
    global maxtrace,mineig
    assert s['converged']
    assert math.isfinite(v['Q']) and math.isfinite(v['MW_gap']) and v['MW_gap']>=0
    assert v['trace_error']<1e-9 and v['min_eigenvalue']>-1e-9
    assert 0<=v['trace_norm_error']<=2+1e-8
    assert 0<=v['squared_frobenius_error']<=2+1e-8
    assert abs(v['frobenius_error']**2-v['squared_frobenius_error'])<1e-12
    if method.startswith('MW_'):
        assert s['tol_factor']==1 and s['epsilon_Q']==min(1.,d/T)
        assert s['gap']<=s['epsilon_Q'] and v['MW_gap']<=s['epsilon_Q']+1e-10
        assert s['full_extreme_checks']>=1
    if method.startswith('OMD_') and 2**k!=d:
        factor=.01 if method=='OMD_strict' else 1.
        tol=factor*min(1.,math.sqrt(d/T))
        assert s['original_gap_tolerance']==tol and s['gap']<=tol
        assert s['regularized_gap']<=tol
    maxtrace=max(maxtrace,v['trace_error']);mineig=min(mineig,v['min_eigenvalue'])

for ci,case in enumerate(CASES):
    phase='main_100_phase_a' if ci in phase_a else 'main_100_phase_b'
    rows[ci]={}
    for rep in range(100):
        path=base/phase/f'case_{ci:02d}'/f'rep_{rep:02d}'/'summary.json'
        if not path.exists():missing.append(dict(case_index=ci,rep=rep,reason='no record'));continue
        r=json.loads(path.read_text())
        assert (r['case_index'],r['rep'],r['n'],r['k'],r['T'])==(ci,rep,case['n'],case['k'],case['T'])
        if 'input_sha256' in r:input_hashes[ci,rep]=r['input_sha256']
        hardware(r['hardware']);valid={}
        for name in names:
            m=r['methods'].get(name,{})
            if m.get('status')!='complete':
                missing.append(dict(case_index=ci,rep=rep,method=name,reason=m.get('status',r['status'])));continue
            warm=[v for v in r['warmups'] if v['method']==name]
            timed=[v for v in r['measured'] if v['method']==name]
            assert len(warm)==1 and len(timed)==3
            assert sorted(t['repeat'] for t in timed)==[0,1,2]
            for t in warm+timed:check(t['stats'],t['validation'],r['d'],r['T'],name,r['k'])
            assert m['max_repeat_frobenius_difference']<1e-8
            assert np.isclose(m['median_seconds'],np.median([t['stats']['wall_seconds'] for t in timed]),rtol=0,atol=1e-12)
            assert m['median_seconds']>0 and np.isfinite(m['median_seconds'])
            valid[name]=m
        rows[ci][rep]=valid
    for name in names:
        count=sum(name in v for v in rows[ci].values())
        cell.append(dict(case_index=ci,**case,method=name,complete_repetitions=count,required_repetitions=100,status='complete' if count==100 else 'incomplete'))

for n in [4,6,8,10]:
    for name in names:
        group=[]
        for rep in range(100):
            path=base/'main_100_phase_a_memory'/f'n{n}_{name}_rep{rep:03d}.json'
            if not path.exists():continue
            r=json.loads(path.read_text())
            assert (r['n'],r['rep'],r['method'])==(n,rep,name)
            if r['status']!='complete':continue
            ci={4:7,6:8,8:2,10:9}[n]
            if (ci,rep) in input_hashes:
                assert r['input_sha256']==input_hashes[ci,rep]
                matched_memory_inputs+=1
            hardware(r['hardware']);check(r['stats'],r['validation'],2**n,64*2**n,name,2)
            assert r['peak_process_MiB']>0
            group.append(r)
        memory[n,name]=group
counts=dict(complete_paired_records=sum(all(name in r for name in names) for rs in rows.values() for r in rs.values()),
            required_paired_records=1000,complete_memory_profiles=sum(len(v) for v in memory.values()),required_memory_profiles=2800)
complete=counts['complete_paired_records']==1000 and counts['complete_memory_profiles']==2800
status=dict(status='passed' if complete else 'partial',**counts,cells=cell,missing=missing,max_trace_error=maxtrace,min_eigenvalue=mineig,cpu_models=sorted(models),matched_memory_input_hashes=matched_memory_inputs,
 scope='Checks stored numerical diagnostics, not a new proof or a replay of every dense matrix solve.')
(out/'validation.json').write_text(json.dumps(status,indent=2)+'\n')
if not complete and not a.allow_partial:raise SystemExit('Incomplete records; see validation.json. Use --allow-partial to label incomplete cells explicitly.')

rng=np.random.default_rng(20260919);boot=rng.integers(100,size=(10000,100));summary=[];paired=[];stats={}
for ci,case in enumerate(CASES):
    for name in names:
        if not all(name in rows[ci].get(rep,{}) for rep in range(100)):continue
        ms=[rows[ci][rep][name] for rep in range(100)]
        entry=dict(case_index=ci,**case,d=2**case['n'],method=name,repetitions=100,timing_repeats=3)
        for metric in ['trace_norm_error','frobenius_error','squared_frobenius_error']:
            values=np.array([m['validation'][metric] for m in ms]);lo,hi=np.quantile(values[boot].mean(1),[.025,.975])
            entry[metric]=float(values.mean());entry[metric+'_ci_low']=float(lo);entry[metric+'_ci_high']=float(hi)
        times=np.array([m['median_seconds'] for m in ms]);entry.update(seconds=float(np.median(times)),seconds_q25=float(np.quantile(times,.25)),seconds_q75=float(np.quantile(times,.75)))
        for key in ['Q','MW_gap']:
            vals=np.array([m['validation'][key] for m in ms]);lo,hi=np.quantile(vals[boot].mean(1),[.025,.975])
            entry['mean_'+key]=float(vals.mean())
            entry['mean_'+key+'_ci_low']=float(lo);entry['mean_'+key+'_ci_high']=float(hi)
        entry['max_MW_gap']=max(m['validation']['MW_gap'] for m in ms)
        if name.startswith('MW_'):
            for key in ['iterations','lmo_calls','full_extreme_checks','lmo_seconds','channel_seconds','channel_calls']:
                vals=[m['stats'][key] for m in ms];entry['median_'+key]=float(np.median(vals));entry[key+'_q25']=float(np.quantile(vals,.25));entry[key+'_q75']=float(np.quantile(vals,.75))
            entry['max_eigenvector_residual']=max(m['stats']['max_eigenvector_residual'] for m in ms)
            entry['max_rayleigh_minus_full_min']=max(abs(m['stats']['rayleigh_minus_full_min']) for m in ms)
        summary.append(entry);stats[ci,name]=entry
    if (ci,'PLS') in stats:
        for name in names[1:]:
            if (ci,name) not in stats:continue
            for metric in ['trace_norm_error','frobenius_error','squared_frobenius_error']:
                delta=np.array([rows[ci][rep][name]['validation'][metric]-rows[ci][rep]['PLS']['validation'][metric] for rep in range(100)])
                lo,hi=np.quantile(delta[boot].mean(1),[.025,.975]);paired.append(dict(case_index=ci,method=name,reference='PLS',metric=metric,mean_difference=float(delta.mean()),ci_low=float(lo),ci_high=float(hi)))
memsummary=[]
for (n,name),group in memory.items():
    if len(group)==100:
        vals=np.array([r['peak_process_MiB'] for r in group]);memsummary.append(dict(n=n,d=2**n,method=name,profiles=100,median_MiB=float(np.median(vals)),q25_MiB=float(np.quantile(vals,.25)),q75_MiB=float(np.quantile(vals,.75))))
(out/'summary.json').write_text(json.dumps(dict(status=status['status'],rows=summary,paired_differences=paired,memory=memsummary),indent=2)+'\n')
if summary:
    keys=list(dict.fromkeys(k for r in summary for k in r))
    with (out/'summary.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(summary)

plt.rcParams.update({'font.size':10,'axes.spines.top':False,'axes.spines.right':False})
prefix='' if complete else 'PARTIAL — '
metrics=[('trace_norm_error','Mean trace-norm error'),('frobenius_error','Mean Frobenius error'),('squared_frobenius_error','Mean squared Frobenius error'),('seconds','Solver time (seconds)')]
def finish(fig,filename,caption):
    handles=[]
    for i,name in enumerate(names):handles.append(plt.Line2D([],[],color=colors[i],ls=styles[i],marker='o',label=labels[i]))
    legend_y=.17 if fig.get_size_inches()[1]<=7 else .13
    fig.legend(handles=handles,loc='lower center',bbox_to_anchor=(.5,legend_y),ncol=3,frameon=False,fontsize=9)
    fig.text(.5,.02,caption,ha='center',fontsize=9,linespacing=1.4)
    bottom=.31 if fig.get_size_inches()[1]<=7 else .25
    fig.tight_layout(rect=[0,bottom,1,.94])
    for ext in ['png','svg']:fig.savefig(out/(filename+'.'+ext),dpi=180,facecolor='white')
    plt.close(fig)

def plot_four(ids,x,ticks,xlabel,title,filename):
    fig,axes=plt.subplots(2,2,figsize=(14,10));fig.suptitle(prefix+title,fontsize=15)
    for ax,(metric,ylabel) in zip(axes.flat,metrics):
        for i,name in enumerate(names):
            data=[stats.get((ci,name),{}) for ci in ids]
            y=[r.get(metric,np.nan) for r in data]
            if metric=='seconds':lo=[r.get('seconds_q25',np.nan) for r in data];hi=[r.get('seconds_q75',np.nan) for r in data]
            else:lo=[r.get(metric+'_ci_low',np.nan) for r in data];hi=[r.get(metric+'_ci_high',np.nan) for r in data]
            ax.plot(x,y,ls=styles[i],color=colors[i],marker='o',ms=4,lw=1.7);ax.fill_between(x,lo,hi,color=colors[i],alpha=.10)
        ax.set_xscale('log',base=2);ax.set_xlim(min(x)/1.15,max(x)*1.15);ax.set_xticks(x,ticks);ax.set_xlabel(xlabel);ax.set_ylabel(ylabel);ax.grid(alpha=.18)
        if metric=='seconds':
            if not any((ci,name) in stats for ci in ids for name in names):ax.set_ylim(1e-4,1.)
            ax.set_yscale('log')
        else:ax.set_ylim(bottom=0)
        incomplete=[str(ticks[j]).replace('\n',' ') for j,ci in enumerate(ids) if any((ci,n) not in stats for n in names)]
        if incomplete:ax.text(.02,.98,'Incomplete cells at '+', '.join(incomplete),transform=ax.transAxes,va='top',fontsize=8,color='#a33128')
    global_note='\nAt k=n, the PLS/OMD route also gives the analytic MW solution; MW-FW curves report generic solver routes.' if 6 in ids else ''
    finish(fig,filename,'100 independent inputs per completed cell; paired data; one full warm-up and three fresh timed solves per method.\nError bands: pointwise 95% bootstrap mean intervals. Time bands: IQR of input-level median times. Missing/capped cells are not averaged away.\nFW uses g <= min(1,d/T); OMD uses its own strict/statistical operator-norm gap thresholds. Small-block fixed-state experiments do not prove minimaxity.'+global_note)

plot_four([0,1,2,3,4],[1024,4096,16384,65536,262144],['1,024','4,096','16,384','65,536','262,144'],'Measurements T',
          'Measurements: n=8, k=2, true rank 8','vary_measurements')
plot_four([2,5,6],[2,4,8],['2','4','8 (global)'],'Block size k',
          'Block size: n=8, T=16,384, same rank-eight state','vary_block_size')
plot_four([7,8,2,9],[16,64,256,1024],['16','64','256','1,024'],'Dimension d',
          'Dimension: k=2, T/d=64, true rank 8','dimension_errors')

fig,axes=plt.subplots(1,2,figsize=(14,7));fig.suptitle(prefix+'Dimension: solver time and fresh-process memory',fontsize=15)
for i,name in enumerate(names):
    ids=[7,8,2,9];dims=[16,64,256,1024];ns=[4,6,8,10]
    data=[stats.get((ci,name),{}) for ci in ids]
    axes[0].plot(dims,[r.get('seconds',np.nan) for r in data],color=colors[i],ls=styles[i],marker='o',ms=4)
    axes[0].fill_between(dims,[r.get('seconds_q25',np.nan) for r in data],[r.get('seconds_q75',np.nan) for r in data],color=colors[i],alpha=.10)
    ms=[next((r for r in memsummary if r['n']==n and r['method']==name),{}) for n in ns]
    axes[1].plot(dims,[r.get('median_MiB',np.nan) for r in ms],color=colors[i],ls=styles[i],marker='o',ms=4)
    axes[1].fill_between(dims,[r.get('q25_MiB',np.nan) for r in ms],[r.get('q75_MiB',np.nan) for r in ms],color=colors[i],alpha=.10)
for ax in axes:
    ax.set_xscale('log',base=2);ax.set_xlim(min(dims)/1.15,max(dims)*1.15);ax.set_xticks(dims,['16\n4 qubits','64\n6 qubits','256\n8 qubits','1,024\n10 qubits']);ax.set_xlabel('Dimension d');ax.grid(alpha=.18)
if not any((ci,name) in stats for ci in [7,8,2,9] for name in names):axes[0].set_ylim(1e-4,1.)
axes[0].set_yscale('log');axes[0].set_ylabel('Solver seconds (median and IQR)');axes[1].set_ylabel('Peak process MiB (median and IQR)');axes[1].set_ylim(bottom=0)
timing_missing=[format(d,',') for ci,d in zip(ids,dims) if any((ci,name) not in stats for name in names)]
memory_missing=[format(d,',') for n,d in zip(ns,dims) if any(len(memory[n,name])<100 for name in names)]
for ax,missing_dims in zip(axes,[timing_missing,memory_missing]):
    if missing_dims:ax.text(.02,.98,'Incomplete method cells at d='+', '.join(missing_dims),transform=ax.transAxes,va='top',fontsize=8,color='#a33128')
finish(fig,'vary_dimension','k=2; T/d=64; true rank eight; four allocated CPU cores and four BLAS threads on AMD EPYC7763.\nMemory: 100 independent fresh processes per method/dimension, captured before post-solver validation.\nAt k=n in the block plot, PLS/OMD use the shared analytic MW solution; all MW-FW curves report generic iterative routes separately.')

fig,axes=plt.subplots(1,2,figsize=(14,7));fig.suptitle(prefix+'FW computational work: n=8, k=2, varying T',fontsize=15)
xs=[1024,4096,16384,65536,262144]
for i,name in enumerate(names):
    if not name.startswith('MW_'):continue
    data=[stats.get((ci,name),{}) for ci in range(5)]
    for ax,metric in zip(axes,['iterations','lmo_calls']):
        ax.plot(xs,[r.get('median_'+metric,np.nan) for r in data],color=colors[i],ls=styles[i],marker='o')
        ax.fill_between(xs,[r.get(metric+'_q25',np.nan) for r in data],[r.get(metric+'_q75',np.nan) for r in data],color=colors[i],alpha=.10)
for ax in axes:
    ax.set_xscale('log',base=2);ax.set_xlim(min(xs)/1.15,max(xs)*1.15);ax.set_xticks(xs,['1,024','4,096','16,384','65,536','262,144']);ax.set_xlabel('Measurements T');ax.grid(alpha=.18)
    work_missing=[format(xs[ci],',') for ci in range(5) if any((ci,name) not in stats for name in names if name.startswith('MW_'))]
    if work_missing:ax.text(.02,.98,'Incomplete cells at T='+', '.join(work_missing),transform=ax.transAxes,va='top',fontsize=8,color='#a33128')
axes[0].set_ylabel('FW updates (median and IQR)');axes[1].set_ylabel('Smallest-eigenpair calls (median and IQR)')
finish(fig,'fw_work','Every FW stopping decision is independently checked against a recomputed gradient and full extreme-eigenvalue calculation.\nObjective values, gaps, eigenvector residuals, cache drift and Q-optimum intervals are preserved in the numerical records.\nNo theorem-regime curvature bound or guaranteed iteration count is assumed for these small-block settings.')

fig,axes=plt.subplots(1,2,figsize=(14,7));fig.suptitle(prefix+'MW objective and optimality gap: n=8, k=2, varying T',fontsize=15)
for i,name in enumerate(names):
    data=[stats.get((ci,name),{}) for ci in range(5)]
    for ax,key in zip(axes,['mean_Q','mean_MW_gap']):
        ax.plot(xs,[r.get(key,np.nan) for r in data],color=colors[i],ls=styles[i],marker='o',ms=4)
        ax.fill_between(xs,[r.get(key+'_ci_low',np.nan) for r in data],[r.get(key+'_ci_high',np.nan) for r in data],color=colors[i],alpha=.10)
axes[1].plot(xs,[min(1.,256/t) for t in xs],color='#555555',ls=':',lw=1.5)
axes[1].annotate('FW stopping threshold',xy=(xs[-1],256/xs[-1]),xytext=(-6,10),textcoords='offset points',ha='right',fontsize=8,color='#555555')
for ax in axes:
    ax.set_xscale('log',base=2);ax.set_xlim(min(xs)/1.15,max(xs)*1.15);ax.set_xticks(xs,['1,024','4,096','16,384','65,536','262,144']);ax.set_xlabel('Measurements T');ax.grid(alpha=.18)
    incomplete=[str(xs[ci]) for ci in range(5) if any((ci,name) not in stats for name in names)]
    if incomplete:ax.text(.02,.98,'Incomplete cells at '+', '.join(incomplete),transform=ax.transAxes,va='top',fontsize=8,color='#a33128')
axes[0].set_ylabel('Mean MW objective Q');axes[1].set_ylabel('Mean MW Frank–Wolfe gap');axes[1].set_yscale('log')
finish(fig,'objective_gap','The same Q and its Frank–Wolfe gap are evaluated for every output. PLS and OMD generally target other objectives.\nBands: pointwise 95% bootstrap intervals for means over 100 paired inputs. The dotted threshold applies only to the four MW-FW routes.\nA smaller Q is not evidence of a smaller state-reconstruction error; these experiments do not establish minimaxity.')
print(json.dumps(dict(status=status['status'],**counts),indent=2))
