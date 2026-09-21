import sys
import numpy as np
from threadpoolctl import threadpool_limits
from existing import Channel
from solvers import fw,apg_reference,inner,objective
from projections import scipy_density
rng=np.random.default_rng(71901)
with threadpool_limits(limits=1):
 for n,k in [(4,2),(4,4)]:
  c=Channel(n,k);d=c.d;T=1024
  # Trace-one PSD synthetic empirical mean, independent of the true-state loss computation.
  a=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));b=a@a.conj().T;b/=np.trace(b);y=(d+1)*b-np.eye(d)
  x,ref=apg_reference(c,b,T,tol=1e-10,maxiter=5000)
  assert ref['converged']
  if k==n:assert np.linalg.norm(x-scipy_density(y))<1e-9
  for rule in ['line_search','deterministic']:
   z,st=fw(c,b,T,rule,'identity',tol_factor=.01,maxiter=10000,max_seconds=30)
   assert st['converged'],st
   qdiff=st['objective']-ref['objective']
   assert -1e-9<=qdiff<=st['gap']+1e-9
   assert abs(np.trace(z)-1)<1e-10 and np.linalg.eigvalsh(z)[0]>-1e-10
   print(n,k,rule,st['iterations'],st['gap'],qdiff)
print('Independent APG comparison and global analytic checks passed.')
