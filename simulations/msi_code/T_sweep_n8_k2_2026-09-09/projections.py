from baseline import *
from scipy.linalg import eigh

class Partial:
 def __init__(self,q=16):self.q=q;self.calls=0;self.expansions=0;self.ranks=[]
 def density(self,x):
  x=herm(x);d=len(x);q=min(self.q,d);self.calls+=1
  while True:
   w,v=eigh(x,subset_by_index=[d-q,d-1],driver='evr',check_finite=False)
   s=w[::-1];ts=(np.cumsum(s)-1)/np.arange(1,len(s)+1);theta=ts[np.flatnonzero(s>ts)[-1]]
   # Returned bottom eigenvalue bounds every omitted eigenvalue above.
   # A margin forces expansion near a threshold crossing.
   margin=1e-11*max(1,float(np.max(np.abs(w))),abs(theta))
   if q==d or w[0]<theta-margin:break
   q=min(d,2*q);self.expansions+=1
  keep=w>theta;self.ranks.append(int(keep.sum()));qv=v[:,keep]
  self.q=min(d,max(16,2*int(keep.sum())+1))
  return herm((qv*(w[keep]-theta))@qv.conj().T)

def scipy_density(x,driver='evr'):
 w,v=eigh(herm(x),driver=driver,check_finite=False);s=w[::-1];ts=(np.cumsum(s)-1)/np.arange(1,len(s)+1);theta=ts[np.flatnonzero(s>ts)[-1]]
 keep=w>theta;q=v[:,keep];return herm((q*(w[keep]-theta))@q.conj().T)

def scipy_nuclear(x,radius=1,driver='evr'):
 w,v=eigh(herm(x),driver=driver,check_finite=False);a=np.abs(w)
 if a.sum()<=radius:return herm(x)
 s=np.sort(a)[::-1];ts=(np.cumsum(s)-radius)/np.arange(1,len(s)+1);theta=ts[np.flatnonzero(s>ts)[-1]]
 keep=a>theta;q=v[:,keep];return herm((q*(np.sign(w[keep])*(a[keep]-theta)))@q.conj().T)
