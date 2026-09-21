"""Matrix-free Pauli channel, exact PLS, and certified convex forward solvers."""
import os
os.environ.setdefault('VECLIB_MAXIMUM_THREADS','1')
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
os.environ.setdefault('OMP_NUM_THREADS','1')
import time
import numpy as np

def herm(x):return (x+x.conj().T)/2

def project_density(x):
    w,v=np.linalg.eigh(herm(x));s=w[::-1];threshold=(np.cumsum(s)-1)/np.arange(1,len(s)+1)
    theta=threshold[np.flatnonzero(s>threshold)[-1]]
    return herm((v*np.maximum(w-theta,0))@v.conj().T)

def nuclear_project(x,radius=1):
    w,v=np.linalg.eigh(herm(x));a=np.abs(w)
    if a.sum()<=radius:return herm(x)
    s=np.sort(a)[::-1];ts=(np.cumsum(s)-radius)/np.arange(1,len(s)+1)
    theta=ts[np.flatnonzero(s>ts)[-1]]
    return herm((v*(np.sign(w)*np.maximum(a-theta,0)))@v.conj().T)

def trnorm(x):return float(np.abs(np.linalg.eigvalsh(herm(x))).sum())
def opnorm(x):return float(np.max(np.abs(np.linalg.eigvalsh(herm(x)))))

class FastChannel:
    def __init__(self,n,k=2):
        assert k%2==0 and n%k==0
        self.n,self.k,self.d=n,k,2**n
        self.axes=tuple(a for q in range(n) for a in (q,n+q))
        self.unaxes=tuple(np.argsort(self.axes))
        codes=np.arange(4**n,dtype=np.int64)
        Q=2**k;K=np.array([[[1,1/(Q+1)],[0,0]],np.array([[1,1],[2*Q,Q]])/(Q+1)**2])
        product=np.broadcast_to(np.eye(2),(len(codes),2,2)).copy()
        for j in range(n//k):
            active=np.zeros(len(codes),bool)
            for a in range(k):
                q=(j*k+k//2+a)%n
                active|=((codes>>(2*(n-1-q)))&3)!=0
            product=product@K[active.astype(int)]
        self.m=np.trace(product,axis1=1,axis2=2).reshape((4,)*n)
        self.ell=(self.d+1)*self.m;self.ell.flat[0]=1
        self.norm=float(self.ell.max())
    def coefficients(self,x):
        a=np.asarray(x,dtype=complex).reshape((2,)*(2*self.n)).transpose(self.axes).reshape((4,)*self.n).copy()
        for q in range(self.n):
            b=np.moveaxis(a,q,0);z=np.empty_like(b)
            z[0]=(b[0]+b[3])/np.sqrt(2);z[1]=(b[1]+b[2])/np.sqrt(2)
            z[2]=1j*(b[1]-b[2])/np.sqrt(2);z[3]=(b[0]-b[3])/np.sqrt(2)
            a=np.moveaxis(z,0,q)
        return a
    def matrix(self,a):
        a=np.asarray(a,dtype=complex)
        for q in range(self.n):
            b=np.moveaxis(a,q,0);z=np.empty_like(b)
            z[0]=(b[0]+b[3])/np.sqrt(2);z[1]=(b[1]-1j*b[2])/np.sqrt(2)
            z[2]=(b[1]+1j*b[2])/np.sqrt(2);z[3]=(b[0]-b[3])/np.sqrt(2)
            a=np.moveaxis(z,0,q)
        return herm(a.reshape((2,)*(2*self.n)).transpose(self.unaxes).reshape(self.d,self.d))
    def apply(self,x,kind='L'):
        weights={'L':self.ell,'M':self.m,'inverse':1/self.m}[kind]
        return self.matrix(weights*self.coefficients(x))
    def pls(self,b):return project_density(self.apply(b,'inverse'))

def certificate(c,y,x,a,eta):
    a=herm(a);a=a/max(1,trnorm(a));la=c.apply(a)
    residual=opnorm(y-c.apply(x));linear=float(np.trace(a@y).real)
    lower0=max(0.,linear-float(np.linalg.eigvalsh(la)[-1]))
    if eta:
        v=project_density(la/(2*eta))
        lower_eta=linear+eta*np.linalg.norm(v)**2-float(np.trace(la@v).real)
    else:lower_eta=lower0
    upper=residual+eta*np.linalg.norm(x)**2
    if residual-lower0 < -1e-8 or upper-lower_eta < -1e-8:
        raise ArithmeticError('Inconsistent primal-dual bound')
    return {'objective':residual,'gap':max(0.,residual-lower0),'regularized_gap':max(0.,float(upper-lower_eta))}

def forward(c,y,T,method='pdhg',tol_fraction=.01,eta_fraction=.005,maxiter=20000,check_every=20,regularized_tol_fraction=None):
    d=c.d;gamma=min(1,np.sqrt(d/T));eta=eta_fraction*gamma;tol=tol_fraction*gamma
    regtol=(tol_fraction if regularized_tol_fraction is None else regularized_tol_fraction)*gamma
    start=time.perf_counter();x=c.pls((y+np.eye(d))/(d+1));a=np.zeros_like(x);hist=[]
    initial=certificate(c,y,x,a,eta)
    if initial['gap']<tol and initial['regularized_gap']<regtol:return x,dict(initial,seconds=time.perf_counter()-start,iterations=0,converged=True,history=[])
    if method=='pdhg':
        xbar=x.copy();tau=step=.99/c.norm
        for j in range(1,maxiter+1):
            a=nuclear_project(a+step*(y-c.apply(xbar)))
            nx=project_density((x+tau*c.apply(a))/(1+2*tau*eta))
            xbar=2*nx-x;x=nx
            if j%check_every==0:
                diag=certificate(c,y,x,a,eta);hist.append([j,time.perf_counter()-start,diag['gap'],diag['regularized_gap']])
                if diag['gap']<=tol and diag['regularized_gap']<=regtol:break
    elif method=='admm':
        z=x.copy();r=y-c.apply(x);u=np.zeros_like(x);v=np.zeros_like(x);beta=1.
        for j in range(1,maxiter+1):
            rhs=c.ell*c.coefficients(y-r-u)+c.coefficients(z-v)
            x=c.matrix(rhs/(c.ell**2+1))
            lx=c.apply(x);arg=y-lx-u;r=arg-nuclear_project(arg,1/beta)
            z=project_density((x+v)/(1+2*eta/beta))
            u+=lx+r-y;v+=x-z
            if j%check_every==0:
                diag=certificate(c,y,z,-beta*u,eta);hist.append([j,time.perf_counter()-start,diag['gap'],diag['regularized_gap']])
                if diag['gap']<=tol and diag['regularized_gap']<=regtol:break
        x=z
    else:raise ValueError(method)
    diag=certificate(c,y,x,a if method=='pdhg' else -beta*u,eta)
    return x,dict(diag,seconds=time.perf_counter()-start,iterations=j,converged=bool(diag['gap']<=tol and diag['regularized_gap']<=regtol),history=hist)
