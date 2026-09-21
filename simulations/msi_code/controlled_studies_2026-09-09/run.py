import json,os,resource,socket,sys,time
from pathlib import Path
import numpy as np
import scipy,stim
from threadpoolctl import threadpool_info
import accelerated
from baseline import FastChannel,trnorm
from projections import Partial,scipy_nuclear
from large_simulation import records as two_qubit_records
from stabilizer_sampling import records as general_records

rep=int(sys.argv[1]);assert 0<=rep<20
OUT=Path('results')/f'rep_{rep:02d}';OUT.mkdir(parents=True,exist_ok=True)
r=dict(rep=rep,true_rank=8,T_over_d=64,job_id=os.getenv('SLURM_JOB_ID'),host=socket.gethostname(),
       numpy=np.__version__,scipy=scipy.__version__,stim=stim.__version__,threads=threadpool_info(),runs=[],status='started')
def save():
    r['process_maxrss_KiB']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    p=OUT/'summary.tmp';p.write_text(json.dumps(r,indent=2));p.replace(OUT/'summary.json')
class Channel(FastChannel):
    def pls(self,b):return Partial().density(self.apply(b,'inverse'))
save()
for index,(n,k) in enumerate([(4,2),(6,2),(8,4),(8,8),(10,2)]):
    d=2**n;T=64*d;seed=[20260910,n,k,8,rep]
    folder=OUT/f'n{n}_k{k}';folder.mkdir(exist_ok=True)
    row=dict(n=n,k=k,d=d,T=T,true_rank=8,seed=seed)
    t=time.perf_counter();c=Channel(n,k);row['channel_seconds']=time.perf_counter()-t
    lam=np.r_[np.full(8,1/8),np.zeros(d-8)];rho=np.diag(lam)
    t=time.perf_counter()
    if k==2:b=two_qubit_records(n,np.eye(d,dtype=complex),lam,[T],seed)[0]
    else:b=general_records(n,k,8,T,seed,folder/'records')
    row['sampling_seconds']=time.perf_counter()-t
    np.savez_compressed(folder/'data.npz',mean=b,lam=lam)
    Partial().density(np.eye(16)/16);scipy_nuclear(np.eye(16))
    order=['PLS','Forward'] if (rep+index)%2==0 else ['Forward','PLS'];row['method_order']=order
    for method in order:
        if method=='PLS':
            t=time.perf_counter();x=c.pls(b);row['pls_seconds']=time.perf_counter()-t;row['pls_error']=trnorm(x-rho)
        else:
            partial=Partial();accelerated.project_density=partial.density;accelerated.nuclear_project=scipy_nuclear
            x,dg=accelerated.solve(c,(d+1)*b-np.eye(d),T,maxiter=4000)
            row['forward']=dg;row['forward_error']=trnorm(x-rho)
        te=float(abs(np.trace(x).real-1));me=float(np.linalg.eigvalsh(x)[0])
        assert te<1e-9 and me>-1e-9
        row[method.lower()+'_feasibility']=dict(trace_error=te,min_eigenvalue=me)
        np.save(folder/(method.lower()+'.npy'),x)
    r['runs'].append(row);r['status']=f'completed {index+1} of 5 settings';save()
    print('RESULT',rep,n,k,T,row['pls_error'],row['forward_error'],row['pls_seconds'],row['forward']['seconds'],row['forward']['converged'],flush=True)
    del c,b,rho,x
r['status']='complete' if all(x['forward']['converged'] for x in r['runs']) else 'solver limit';save()
