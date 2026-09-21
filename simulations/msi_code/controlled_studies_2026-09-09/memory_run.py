import json,resource,sys,time,socket
from pathlib import Path
import numpy as np
import accelerated
from baseline import FastChannel
from projections import Partial,scipy_nuclear
task=int(sys.argv[1]);n=[4,6,8,10][task//2];method=['PLS','Forward'][task%2];d=2**n;T=64*d
class Channel(FastChannel):
    def pls(self,b):return Partial().density(self.apply(b,'inverse'))
b=np.load(Path('memory_inputs')/f'task_{task}.npy');c=Channel(n,2)
start=time.perf_counter()
if method=='PLS':x=c.pls(b);diag={}
else:
    partial=Partial();accelerated.project_density=partial.density;accelerated.nuclear_project=scipy_nuclear
    x,diag=accelerated.solve(c,(d+1)*b-np.eye(d),T,maxiter=4000)
    assert diag['converged']
elapsed=time.perf_counter()-start
row=dict(n=n,k=2,d=d,T=T,true_rank=8,rep=0,method=method,host=socket.gethostname(),seconds=elapsed,
         peak_process_MiB=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024,
         description='Fresh process including imports, one empirical mean, channel setup, solver and output; excludes data generation and post-solver risk evaluation.',converged=True)
out=Path('memory');out.mkdir(exist_ok=True);(out/f'n{n}_{method}.json').write_text(json.dumps(row,indent=2))
print(json.dumps(row),flush=True)
