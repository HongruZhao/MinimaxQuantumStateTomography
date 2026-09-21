"""MW-PLS over density matrices: rank-one FW and an independent APG reference.
All reported certificates are floating-point diagnostics, not interval proofs.
"""
import time
import numpy as np
from scipy.linalg import eigh
from baseline import herm
from projections import scipy_density


def inner(a,b):
    return float(np.vdot(a,b).real)


def objective(x,lx,y):
    return .5*inner(x,lx)-inner(y,x)


def full_gap(c,x,y):
    gmat=herm(c.apply(x)-y)
    smallest=float(eigh(gmat,eigvals_only=True,driver='evd',check_finite=False)[0])
    gap=inner(gmat,x)-smallest
    if gap < -1e-8:raise ArithmeticError('Negative independently checked FW gap')
    return max(0.,gap),smallest,gmat


def fw(c,b,T,step_rule='line_search',initialization='identity',tol_factor=1.,maxiter=12000,max_seconds=1800.,progress=None):
    start=time.perf_counter();d=c.d;y=(d+1)*b-np.eye(d)
    if initialization=='identity':x=np.eye(d,dtype=complex)/d
    elif initialization=='pls':x=c.pls(b)
    else:raise ValueError(initialization)
    initial_seconds=time.perf_counter()-start
    lx=c.apply(x);eps=tol_factor*min(1.,d/T)
    updates=0;partial_calls=0;full_checks=0;apply_calls=1
    lmo_seconds=0.;channel_seconds=0.;check_seconds=0.;max_residual=0.;history=[]
    status='iteration_limit';checked_gap=None;last_rayleigh_error=None;min_den=None
    while True:
        gmat=herm(lx-y)
        tm=time.perf_counter();w,v=eigh(gmat,subset_by_index=[0,0],driver='evr',check_finite=False)
        lmo_seconds+=time.perf_counter()-tm;partial_calls+=1
        v=v[:,0];v=v/np.linalg.norm(v)
        rayleigh=float(np.vdot(v,gmat@v).real)
        residual=float(np.linalg.norm(gmat@v-rayleigh*v));max_residual=max(max_residual,residual)
        candidate_gap=max(0.,inner(gmat,x)-float(w[0]))
        elapsed=time.perf_counter()-start
        if candidate_gap<=eps or updates==maxiter or elapsed>=max_seconds:
            tm=time.perf_counter();checked_gap,lam_full,gfull=full_gap(c,x,y)
            full_checks+=1;apply_calls+=1;check_seconds+=time.perf_counter()-tm
            last_rayleigh_error=rayleigh-lam_full
            history.append(dict(iteration=updates,seconds=time.perf_counter()-start,gap=checked_gap,kind='full_check',rayleigh_minus_full_min=last_rayleigh_error))
            if checked_gap<=eps:
                status='converged';break
            if updates==maxiter:break
            if time.perf_counter()-start>=max_seconds:status='time_limit';break
            # A partial eigenpair may not certify termination; continue after the full check.
        p=np.outer(v,v.conj());direction=p-x
        tm=time.perf_counter();lp=c.apply(p);channel_seconds+=time.perf_counter()-tm;apply_calls+=1
        ld=lp-lx;den=inner(direction,ld);min_den=den if min_den is None else min(min_den,den)
        numerator=inner(gmat,x)-rayleigh
        if den<=0:
            if np.linalg.norm(direction)<1e-12 and candidate_gap<=eps:step=0.
            else:status='nonpositive_curvature';break
        elif step_rule=='line_search':step=float(np.clip(numerator/den,0.,1.))
        elif step_rule=='deterministic':step=2./(updates+2.)
        else:raise ValueError(step_rule)
        x=herm((1-step)*x+step*p);lx=herm((1-step)*lx+step*lp);updates+=1
        if updates%100==0:
            record=dict(iteration=updates,seconds=time.perf_counter()-start,previous_gap=candidate_gap,step=step)
            history.append(record)
            if progress:progress(record)
    # Independent full gap already computed at ordinary exits. Always recompute Lx for reported Q.
    if checked_gap is None or status=='nonpositive_curvature':
        tm=time.perf_counter();checked_gap,_,_=full_gap(c,x,y);full_checks+=1;apply_calls+=1;check_seconds+=time.perf_counter()-tm
    true_lx=c.apply(x);apply_calls+=1
    stats=dict(solver='rank_one_fw',step_rule=step_rule,initialization=initialization,tol_factor=tol_factor,
        epsilon_Q=eps,gap=checked_gap,objective=objective(x,true_lx,y),status=status,converged=bool(checked_gap<=eps),
        iterations=updates,lmo_calls=partial_calls,full_extreme_checks=full_checks,channel_calls=apply_calls,
        lmo_seconds=lmo_seconds,channel_seconds=channel_seconds,full_check_seconds=check_seconds,
        initialization_seconds=initial_seconds,max_eigenvector_residual=max_residual,rayleigh_minus_full_min=last_rayleigh_error,
        min_direction_curvature=min_den,channel_cache_frobenius_drift=float(np.linalg.norm(true_lx-lx)),
        history=history,wall_seconds=time.perf_counter()-start,
        eigen_check='Each LMO: dense EVR smallest eigenpair; termination independently checks full EVD spectrum and recomputed gradient.')
    return x,stats


def apg_reference(c,b,T,tol=1e-8,maxiter=10000,max_seconds=1800.):
    """Separate full-projection accelerated-gradient reference, no FW updates."""
    start=time.perf_counter();d=c.d;y=(d+1)*b-np.eye(d);x=np.eye(d,dtype=complex)/d;z=x.copy();t=1.
    L=float(c.ell.max());history=[];gap=float('inf');status='iteration_limit'
    for j in range(1,maxiter+1):
        grad=c.apply(z)-y
        nx=scipy_density(z-grad/L)
        nt=(1+np.sqrt(1+4*t*t))/2
        z=herm(nx+(t-1)/nt*(nx-x));x=nx;t=nt
        if j%10==0 or j==maxiter:
            gap,_,_=full_gap(c,x,y)
            history.append(dict(iteration=j,gap=gap,seconds=time.perf_counter()-start))
            if gap<=tol:status='converged';break
            if time.perf_counter()-start>=max_seconds:status='time_limit';break
    return x,dict(solver='independent_projected_gradient_reference',gap=gap,epsilon_Q=tol,
        objective=objective(x,c.apply(x),y),iterations=j,converged=gap<=tol,status=status,
        history=history,wall_seconds=time.perf_counter()-start)
