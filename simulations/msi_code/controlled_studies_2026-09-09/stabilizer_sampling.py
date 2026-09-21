"""Born sampling of diagonal mixed states through uniform Clifford blocks."""
from pathlib import Path
import numpy as np
import stim

def supports(n,k):
    assert k%2==0 and n%k==0
    return [[(j*k+k//2+a)%n for a in range(k)] for j in range(n//k)]+[[j*k+a for a in range(k)] for j in range(n//k)]

def precise_state(sim):
    v=sim.state_vector(endian='big').astype(complex)
    mask=np.abs(v)>0
    v[mask]=v[mask]/np.abs(v[mask])/np.sqrt(mask.sum())
    return v

def one_record(n,k,latent,seed):
    blocks=supports(n,k)
    gates=[stim.Tableau.random(k) for _ in blocks]
    sim=stim.TableauSimulator(seed=seed)
    sim.set_num_qubits(n)
    for q in range(n):
        if (latent>>(n-1-q))&1:sim.x(q)
    for g,s in zip(gates,blocks):sim.do_tableau(g,s)
    bits=sim.measure_many(*range(n))
    b=sum(int(bit)<<(n-1-q) for q,bit in enumerate(bits))
    # The post-measurement state is |b>; reverse U to obtain U^dagger|b>.
    for g,s in reversed(list(zip(gates,blocks))):sim.do_tableau(g.inverse(),s)
    return precise_state(sim),b,gates

def records(n,k,rank,T,seed,folder):
    rng=np.random.default_rng(seed);d=2**n;total=np.zeros((d,d),complex)
    folder=Path(folder);folder.mkdir(exist_ok=True)
    for pos in range(0,T,128):
        count=min(128,T-pos);vectors=[];outcomes=[];encoded=[]
        latent=rng.integers(rank,size=count)
        for j in range(count):
            v,b,gs=one_record(n,k,int(latent[j]),int(rng.integers(2**63)))
            vectors.append(v);outcomes.append(b)
            encoded.append([np.packbits(np.concatenate([a.ravel() for a in g.to_numpy()])) for g in gs])
        vectors=np.array(vectors)
        total+=vectors.T@vectors.conj()
        # Archive actual draws because Tableau.random has no seed parameter.
        np.savez_compressed(folder/f'batch_{pos:07d}.npz',tableau_bits=np.array(encoded),outcomes=outcomes,latent=latent,n=n,k=k)
    return (total+total.conj().T)/(2*T)
