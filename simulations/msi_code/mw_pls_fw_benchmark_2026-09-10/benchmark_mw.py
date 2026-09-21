"""Paired warmed benchmark. Config selects only variants justified by the pilot."""
import argparse,hashlib,json,time,gc,resource
from pathlib import Path
import numpy as np
from existing import Channel,CASES,load_input,hardware,save_json,solve_fresh
from solvers import fw,full_gap,objective
from baseline import trnorm
from projections import Partial,scipy_nuclear
import omd_tolerance
ROOT=Path(__file__).resolve().parent

def method_solve(c,b,T,spec):
    start=time.perf_counter()
    if spec['kind']=='fw':
        x,s=fw(c,b,T,step_rule=spec['step'],initialization=spec['initialization'],tol_factor=spec['tol_factor'],
               maxiter=spec['maxiter'],max_seconds=spec['max_seconds'])
    elif spec['kind']=='pls':x,s=solve_fresh(c,b,T,'PLS')
    elif spec['kind']=='analytic_global':
        assert c.n==c.k
        x,s=solve_fresh(c,b,T,'Forward')
    elif spec['kind']=='omd':
        if c.k==c.n:
            x,s=solve_fresh(c,b,T,'Forward')
        else:
            part=Partial();omd_tolerance.project_density=part.density;omd_tolerance.nuclear_project=scipy_nuclear
            y=(c.d+1)*b-np.eye(c.d);tol=spec['tol_factor']
            x,s=omd_tolerance.solve(c,y,T,regfrac=tol,tolfrac=tol,maxiter=4000)
            s.update(solver='omd_admm',initialization='fresh PLS included',eta=.005*min(1.,np.sqrt(c.d/T)),
                     original_gap_tolerance=tol*min(1.,np.sqrt(c.d/T)),regularized_gap_tolerance=tol*min(1.,np.sqrt(c.d/T)),
                     projection_calls=part.calls,projection_expansions=part.expansions)
    else:raise ValueError(spec)
    s['wall_seconds']=time.perf_counter()-start
    return x,s

def validate(c,b,T,x,spec,stats):
    w=np.linalg.eigvalsh(x);traceerr=float(abs(np.trace(x)-1));mineig=float(w[0])
    assert traceerr<1e-9 and mineig>-1e-9
    rho=np.diag(np.r_[np.full(8,1/8),np.zeros(c.d-8)]);diff=x-rho;y=(c.d+1)*b-np.eye(c.d)
    qgap,_,_=full_gap(c,x,y)
    if spec['kind']=='fw' and stats['converged']:assert qgap<=stats['epsilon_Q']+1e-10
    if spec['kind']=='omd' and c.k!=c.n and stats['converged']:
        assert stats['gap']<=stats['original_gap_tolerance'] and stats['regularized_gap']<=stats['regularized_gap_tolerance']
    return dict(trace_error=traceerr,min_eigenvalue=mineig,trace_norm_error=trnorm(diff),
        frobenius_error=float(np.linalg.norm(diff)),squared_frobenius_error=float(np.linalg.norm(diff)**2),
        Q=objective(x,c.apply(x),y),MW_gap=qgap)

def run(config,case_index,rep):
    case=CASES[case_index];d=2**case['n'];T=case['T'];assert d<=1024
    output=ROOT/config['output']/f'case_{case_index:02d}'/f'rep_{rep:02d}';output.mkdir(parents=True,exist_ok=True)
    fingerprint=hashlib.sha256(json.dumps(config,sort_keys=True).encode()).hexdigest()
    prior=output/'summary.json'
    if prior.exists():
        old=json.loads(prior.read_text());assert old['config_sha256']==fingerprint
        if old['status']=='complete':return
    row=dict(case_index=case_index,rep=rep,**case,d=d,true_rank=8,config_sha256=fingerprint,config=config,
       source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.glob('*.py')},hardware=hardware(),warmups=[],measured=[],methods={},status='started')
    def save():save_json(output/'summary.json',row)
    save();start=time.perf_counter();b,path=load_input(case,rep)
    row.update(input_source=path,input_sha256=hashlib.sha256(b.tobytes()).hexdigest(),input_load_seconds=time.perf_counter()-start)
    # Preserve one exact input locally on MSI in each new paired record.
    np.savez_compressed(output/'input.npz',mean=b,n=case['n'],k=case['k'],T=T)
    start=time.perf_counter();c=Channel(case['n'],case['k']);row['channel_setup_seconds']=time.perf_counter()-start
    methods=config['methods'];m=len(methods);rotation=(rep+case_index)%m;ordered=methods[rotation:]+methods[:rotation]
    outputs={spec['name']:[] for spec in methods};failed=set()
    for spec in ordered:
        name=spec['name'];print('WARMUP',case_index,rep,name,flush=True)
        x,stats=method_solve(c,b,T,spec);check=validate(c,b,T,x,spec,stats)
        row['warmups'].append(dict(method=name,stats=stats,validation=check))
        if not stats['converged']:
            failed.add(name);row['methods'][name]=dict(status='warmup_not_converged',validation=check,stats=stats)
            np.savez_compressed(output/(name+'_unconverged.npz'),estimate=x)
        del x;gc.collect();row['status']='warming';save()
    row['hardware_after_warmup']=hardware()
    for repeat in range(3):
        order=ordered if repeat%2==0 else list(reversed(ordered))
        for position,spec in enumerate(order):
            name=spec['name']
            if name in failed:continue
            gc.collect();print('MEASURE',case_index,rep,repeat,name,flush=True)
            x,stats=method_solve(c,b,T,spec);check=validate(c,b,T,x,spec,stats)
            row['measured'].append(dict(method=name,repeat=repeat,position=position,order=[s['name'] for s in order],stats=stats,validation=check))
            outputs[name].append(x)
            if not stats['converged']:failed.add(name)
            row['status']='measuring';save()
    for spec in methods:
        name=spec['name'];items=[r for r in row['measured'] if r['method']==name]
        if name in failed:
            row['methods'].setdefault(name,{}).update(status='not_converged',measured_runs=len(items));continue
        assert len(items)==3
        first=outputs[name][0];difference=max(float(np.linalg.norm(x-first)) for x in outputs[name])
        assert difference<1e-8
        row['methods'][name]=dict(status='complete',median_seconds=float(np.median([r['stats']['wall_seconds'] for r in items])),
            max_repeat_frobenius_difference=difference,validation=items[0]['validation'],stats=items[0]['stats'])
        np.savez_compressed(output/(name+'.npz'),estimate=first)
    successful=[m['validation'] for m in row['methods'].values() if m.get('status')=='complete']
    if successful:
        lower=max(v['Q']-v['MW_gap'] for v in successful)
        upper=min(v['Q'] for v in successful)
        assert lower<=upper+1e-8
        row['Q_optimum_interval']=dict(lower=lower,upper=upper,source='Feasible Q values and full-gradient FW gaps; floating-point interval, not an exact reference optimum.')
        for m in row['methods'].values():
            if m.get('status')=='complete':
                q=m['validation']['Q'];m['Q_excess_interval']=dict(lower=max(0.,q-upper),upper=max(0.,q-lower))
    if c.n==c.k:
        assert row['methods']['PLS']['validation']['MW_gap']<1e-8
        row['global_analytic_MW_reference_method']='PLS; this exact shared spectral procedure also minimizes the OMD objective. MW_* labels report generic FW separately.'
    row['status']='complete' if not failed else 'incomplete_methods';row['failed_methods']=sorted(failed);save()
    print('FINISHED',case_index,rep,row['status'],flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('config',type=Path);p.add_argument('task',type=int);a=p.parse_args()
    cfg=json.loads(a.config.read_text());cases=cfg['case_indices'];reps=cfg['repetitions'];assert 0<=a.task<len(cases)*len(reps)
    run(cfg,cases[a.task//len(reps)],reps[a.task%len(reps)])
