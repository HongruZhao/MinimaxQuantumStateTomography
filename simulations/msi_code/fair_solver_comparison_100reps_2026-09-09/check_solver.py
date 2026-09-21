"""Targeted checks for fresh starts and the global-Clifford shortcut."""
import numpy as np
from benchmark import Channel, solve_fresh, validate_output
from projections import scipy_density

rng=np.random.default_rng(8912)
for n,k in [(4,2),(4,4)]:
    c=Channel(n,k);d=c.d;T=64*d
    rho=np.diag(np.r_[np.full(8,1/8),np.zeros(d-8)])
    v=rng.normal(size=d)+1j*rng.normal(size=d);v/=np.linalg.norm(v)
    b=.92*c.apply(rho,'M')+.08*np.outer(v,v.conj())
    before=b.copy();b.flags.writeable=False
    outputs={}
    for method in ['PLS','Forward']:
        first,stats=solve_fresh(c,b,T,method)
        validate_output(c,b,T,first,method,stats)
        # Interpose the other solver; a fresh run must not inherit its result.
        solve_fresh(c,b,T,'Forward' if method=='PLS' else 'PLS')
        second,stats2=solve_fresh(c,b,T,method)
        assert np.linalg.norm(first-second)<1e-10
        outputs[method]=first
    assert np.array_equal(b,before)
    assert np.linalg.norm(outputs['PLS']-scipy_density(c.apply(b,'inverse')))<1e-10
    if n==k:assert np.linalg.norm(outputs['PLS']-outputs['Forward'])<1e-10
print('Passed: unchanged input, fresh solver starts, full-projection agreement, and exact global equivalence.')
