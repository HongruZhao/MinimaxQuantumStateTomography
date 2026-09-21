"""Over-relaxed two-block ADMM with cached Pauli coordinates."""
from baseline import *

def solve(c,y,T,alpha=1.7,beta=1.,regfrac=.01,maxiter=12000):
    start=time.perf_counter();gamma=min(1,np.sqrt(c.d/T));eta=.005*gamma
    z=c.pls((y+np.eye(c.d))/(c.d+1));x=z.copy();lx=c.apply(x)
    r=y-lx;u=np.zeros_like(z);v=u.copy();hist=[]
    den=1/(c.ell**2+1)
    for j in range(1,maxiter+1):
        xc=(c.ell*c.coefficients(y-r-u)+c.coefficients(z-v))*den
        x=c.matrix(xc);lx=c.matrix(c.ell*xc)
        # Relax the full affine image (L X, X), not only the state variable.
        lr=alpha*lx+(1-alpha)*(y-r);xr=alpha*x+(1-alpha)*z
        s=y-lr-u;r=s-nuclear_project(s,1/beta)
        z=project_density((xr+v)/(1+2*eta/beta))
        u+=lr+r-y;v+=xr-z
        if j%20==0:
            dg=certificate(c,y,z,-beta*u,eta);hist.append([j,time.perf_counter()-start,dg['gap'],dg['regularized_gap']]); print('progress',hist[-1],flush=True)
            if dg['gap']<=.01*gamma and dg['regularized_gap']<=regfrac*gamma:break
    dg=certificate(c,y,z,-beta*u,eta)
    return z,dict(dg,seconds=time.perf_counter()-start,iterations=j,converged=bool(dg['gap']<=.01*gamma and dg['regularized_gap']<=regfrac*gamma),history=hist)
