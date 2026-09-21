from pathlib import Path
import time,json,csv
import numpy as np
from baseline import FastChannel,forward,trnorm
ROOT=Path(__file__).resolve().parent

def local_apply(states,gates,support,n):
    rest=[q for q in range(n) if q not in support]
    axes=[0]+[q+1 for q in support+rest]
    z=states.reshape((len(states),)+(2,)*n).transpose(axes).reshape(len(states),4,-1)
    z=np.einsum('bij,bjk->bik',gates,z)
    return z.reshape((len(states),)+(2,)*n).transpose(np.argsort(axes)).reshape(len(states),-1)

def records(n,v,lam,sizes,seed):
    cliff=np.load(ROOT/'clifford_representatives.npz')['unitaries'];rng=np.random.default_rng(seed);d=2**n
    first=[[(2*j+1)%n,(2*j+2)%n] for j in range(n//2)];second=[[2*j,2*j+1] for j in range(n//2)]
    total=np.zeros((d,d),complex);means=[];pos=0
    for target in sizes:
        while pos<target:
            count=min(256,target-pos);idx=rng.integers(len(cliff),size=(count,n))
            latent=rng.choice(d,size=count,p=lam);psi=v[:,latent].T.copy()
            for j,support in enumerate(first+second):psi=local_apply(psi,cliff[idx[:,j]],support,n)
            p=np.abs(psi)**2;assert np.max(np.abs(p.sum(1)-1))<1e-11
            b=(rng.random(count)[:,None]>np.cumsum(p/p.sum(1)[:,None],axis=1)).sum(1)
            psi=np.zeros((count,d),complex);psi[np.arange(count),b]=1
            for j in range(n-1,-1,-1):psi=local_apply(psi,cliff[idx[:,j]].conj().transpose(0,2,1),(first+second)[j],n)
            total+=psi.T@psi.conj();pos+=count
        means.append((total+total.conj().T)/(2*target))
    return np.array(means)

def main():
    rows=[]
    settings=[(6,8,'computational',4,[2048,8192,32768]),(6,32,'computational',4,[2048,8192,32768]),(6,8,'haar',4,[2048,8192,32768]),(8,8,'computational',1,[8192])]
    for si,(n,rank,basis,reps,sizes) in enumerate(settings):
        c=FastChannel(n);d=c.d;v=np.eye(d,dtype=complex)
        if basis=='haar':
            rng=np.random.default_rng(9202026+si);z=rng.normal(size=(d,d))+1j*rng.normal(size=(d,d));v,r=np.linalg.qr(z);v=v*(np.diag(r)/np.abs(np.diag(r)))
        lam=np.r_[np.full(rank,1/rank),np.zeros(d-rank)];rho=(v*lam)@v.conj().T
        for rep in range(reps):
            name=f'd{d}_r{rank}_{basis}_{rep}';start=time.perf_counter();means=records(n,v,lam,sizes,[9202026,si,rep]);gen=time.perf_counter()-start
            np.savez_compressed(ROOT/(name+'_data.npz'),rho=rho,means=means,sizes=sizes)
            print(name,'sampling seconds',round(gen,3),flush=True)
            for T,b in zip(sizes,means):
                y=(d+1)*b-np.eye(d);start=time.perf_counter();p=c.pls(b);pt=time.perf_counter()-start
                for method in ['pdhg','admm']:
                    x,diag=forward(c,y,T,method,maxiter=12000)
                    rows.append(dict(d=d,rank=rank,basis=basis,rep=rep,T=T,method=method,pls_seconds=pt,pls_loss=trnorm(p-rho),forward_loss=trnorm(x-rho),**{k:v for k,v in diag.items() if k!='history'}))
                    (ROOT/f'{name}_T{T}_{method}_history.json').write_text(json.dumps(diag['history']))
                    print(' ',T,method,'seconds',round(diag['seconds'],3),'iters',diag['iterations'],'gap',diag['gap'],'ok',diag['converged'],flush=True)
                with (ROOT/'large_results.csv').open('w',newline='') as f:
                    w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)

if __name__=='__main__':main()
