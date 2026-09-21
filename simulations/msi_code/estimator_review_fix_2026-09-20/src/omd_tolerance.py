"""Over-relaxed two-block ADMM with cached Pauli coordinates."""
from baseline import *

def solve(c,y,T,alpha=1.7,beta=1.,regularized_tol_factor=1.,maxiter=12000,
          original_tol_factor=1.,eta=None,return_witness=False):
    from run_identity import accuracy_spec
    request=accuracy_spec(c.d,T,original_tol_factor)
    accuracy_spec(c.d,T,regularized_tol_factor)
    gamma=request['paper_omd_limit']
    eta=request['eta'] if eta is None else float(eta)
    if not np.isfinite(eta) or eta<0 or eta>request['original_gap_tolerance']/2:
        raise ValueError('eta must be finite, nonnegative and at most half the original accuracy budget.')
    if maxiter<1 or not 0<alpha<2 or not np.isfinite(beta) or beta<=0:
        raise ValueError('Invalid ADMM iteration or penalty parameters.')
    start=time.perf_counter()
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
            dg=certificate(c,y,z,-beta*u,eta);hist.append([j,time.perf_counter()-start,dg['gap'],dg['regularized_gap']])
            if dg['gap']<=original_tol_factor*gamma and dg['regularized_gap']<=regularized_tol_factor*gamma:break
    dg=certificate(c,y,z,-beta*u,eta)
    stats=dict(dg,seconds=time.perf_counter()-start,iterations=j,
               eta=eta,original_gap_tolerance=original_tol_factor*gamma,
               regularized_gap_tolerance=regularized_tol_factor*gamma,
               converged=bool(dg['gap']<=original_tol_factor*gamma and
                              dg['regularized_gap']<=regularized_tol_factor*gamma),history=hist)
    if return_witness:stats['_dual_witness']=-beta*u.copy()
    return z,stats
