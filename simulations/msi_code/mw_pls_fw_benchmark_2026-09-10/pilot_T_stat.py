"""Exploratory single-solve resource/accuracy pilot; NOT the final timed benchmark."""
import argparse,hashlib,json,time,resource,os
from pathlib import Path
import numpy as np
from existing import Channel,CASES,load_input,hardware,solve_fresh,save_json
from baseline import trnorm
from solvers import fw,apg_reference,objective,full_gap
from projections import scipy_density,Partial,scipy_nuclear
import omd_tolerance
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('case',type=int);p.add_argument('--rep',type=int,default=0);p.add_argument('--large',action='store_true');a=p.parse_args()
case=CASES[a.case];n,k,T=case['n'],case['k'],case['T'];d=2**n
assert d<=1024
out=ROOT/'pilot_results'/f'case_{a.case:02d}_rep_{a.rep:02d}';out.mkdir(parents=True,exist_ok=True)
source_hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.glob('*.py')}
row=dict(source_sha256=source_hashes,scope='Exploratory one fresh solve per configuration, no timing warm-up/repeats; no speed comparison claim.',case=a.case,rep=a.rep,**case,d=d,hardware=hardware(),status='started',methods=[])
def save():save_json(out/'summary.json',row)
save();start=time.perf_counter();b,source=load_input(case,a.rep);row.update(input_source=source,input_sha256=hashlib.sha256(b.tobytes()).hexdigest(),input_load_seconds=time.perf_counter()-start)
np.savez_compressed(out/'input.npz',mean=b,n=n,k=k,T=T)
start=time.perf_counter();c=Channel(n,k);row.update(channel_setup_seconds=time.perf_counter()-start,channel_norm=c.norm,channel_min_eigenvalue=float(c.ell.min()))
y=(d+1)*b-np.eye(d);rho=np.diag(np.r_[np.full(8,1/8),np.zeros(d-8)]);eps=min(1.,d/T)
save()

def record(name,x,stats):
    eig=np.linalg.eigvalsh(x);err=x-rho
    start=time.perf_counter();gap,_,_=full_gap(c,x,y)
    check=dict(trace_error=float(abs(np.trace(x)-1)),min_eigenvalue=float(eig[0]),hermitian_error=float(np.linalg.norm(x-x.conj().T)),
        trace_norm_error=trnorm(err),frobenius_error=float(np.linalg.norm(err)),squared_frobenius_error=float(np.linalg.norm(err)**2),
        Q=objective(x,c.apply(x),y),MW_gap=gap,postcheck_seconds=time.perf_counter()-start)
    assert check['trace_error']<1e-9 and check['min_eigenvalue']>-1e-9
    item=dict(name=name,stats=stats,validation=check)
    if 'reference_Q' in row:
        item['Q_minus_reference']=check['Q']-row['reference_Q']
        assert item['Q_minus_reference']>=-max(1e-8,2*row['reference_gap'])
        assert item['Q_minus_reference']<=gap+1e-8
    row['methods'].append(item);np.save(out/(name+'.npy'),x);row['process_peak_RSS_MiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
    save();print('RESULT',a.case,a.rep,name,stats.get('converged'),stats.get('iterations'),stats.get('wall_seconds'),check['MW_gap'],check['trace_norm_error'],flush=True)

if not a.large:
    row['stage']='reference';save()
    x,stats=apg_reference(c,b,T,tol=1e-8*eps,maxiter=10000,max_seconds=600)
    row['reference_Q']=stats['objective'];row['reference_gap']=stats['gap'];row['reference_converged']=stats['converged'];record('reference_apg',x,stats)
    if k==n:
        exact=scipy_density(y);row['global_reference_frobenius_difference']=float(np.linalg.norm(x-exact));assert row['global_reference_frobenius_difference']<1e-6
    if not stats['converged']:row['status']='reference_limit';save();raise RuntimeError('Reference did not converge; inspect before trusting comparisons')

# Large pilot begins with line search; exploration is bounded and failures remain visible.
variants=[('line_search','identity'),('line_search','pls'),('deterministic','identity'),('deterministic','pls')]
for tol in [1.]:
 for rule,initial in variants:
    name=f'fw_{rule}_{initial}_tol{tol:g}'
    row['stage']=name;save();print('START',a.case,name,flush=True)
    def progress(item):
        save_json(out/'progress.json',dict(method=name,**item));print('PROGRESS',name,item['iteration'],item['previous_gap'],flush=True)
    x,stats=fw(c,b,T,step_rule=rule,initialization=initial,tol_factor=tol,maxiter=12000,max_seconds=600,progress=progress)
    record(name,x,stats)

row['stage']='PLS';save();x,stats=solve_fresh(c,b,T,'PLS');record('PLS',x,stats)
if k==n:
    x,stats=solve_fresh(c,b,T,'Forward');record('analytic_global_OMD_MW_PLS',x,stats)
elif not a.large:
 for tol in [.01,1.]:
    row['stage']=f'OMD_tol{tol:g}';save();partial=Partial();omd_tolerance.project_density=partial.density;omd_tolerance.nuclear_project=scipy_nuclear
    start=time.perf_counter();x,stats=omd_tolerance.solve(c,y,T,regfrac=tol,tolfrac=tol,maxiter=4000);stats['wall_seconds']=time.perf_counter()-start
    stats.update(initialization='fresh PLS included',original_gap_tolerance=tol*min(1.,np.sqrt(d/T)),regularized_gap_tolerance=tol*min(1.,np.sqrt(d/T)))
    record(f'OMD_tol{tol:g}',x,stats)
row['status']='exploration_complete';row['all_exploratory_variants_converged']=all(m['stats']['converged'] for m in row['methods']);row['stage']='finished';save()
