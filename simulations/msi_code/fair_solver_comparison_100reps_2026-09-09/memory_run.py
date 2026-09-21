"""One independent fresh process per method, dimension and data repetition."""
import argparse,resource
import numpy as np
from benchmark import HERE,Channel,hardware,save_json,solve_fresh,validate_output
p=argparse.ArgumentParser();p.add_argument('task',type=int);a=p.parse_args();assert 0<=a.task<800
n=[4,6,8,10][a.task//200];method=['PLS','Forward'][(a.task//100)%2];rep=a.task%100;d=2**n;T=64*d
b=np.load(HERE/'memory_inputs'/f'rep_{rep:03d}'/f'n{n}.npy');b.flags.writeable=False
c=Channel(n,2);x,stats=solve_fresh(c,b,T,method)
peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
validation=validate_output(c,b,T,x,method,stats)
save_json(HERE/'memory'/f'n{n}_{method}_rep{rep:03d}.json',dict(n=n,k=2,d=d,T=T,rep=rep,method=method,
 peak_process_MiB=peak,hardware=hardware(),solver=stats,validation=validation,
 description='Fresh process including imports, one mean, channel and solver; excludes sampling and post-solver validation.'))
print(n,method,rep,peak,flush=True)
