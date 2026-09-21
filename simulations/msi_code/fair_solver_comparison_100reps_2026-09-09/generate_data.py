"""Generate independent repetitions 20--99; preserve nested T observations."""
import argparse,time
import numpy as np
from benchmark import HERE,CASES,SIZES,save_json,load_input
from large_simulation import records as records_two
from stabilizer_sampling import records as records_general

p=argparse.ArgumentParser();p.add_argument('rep',type=int);p.add_argument('--only-n4',action='store_true');a=p.parse_args()
assert 20<=a.rep<100
settings=[(4,2,[1024])] if a.only_n4 else [(8,2,SIZES),(8,4,[16384]),(8,8,[16384]),(4,2,[1024]),(6,2,[4096]),(10,2,[65536])]
for n,k,sizes in settings:
 folder=HERE/'data'/f'rep_{a.rep:03d}'/f'n{n}_k{k}';folder.mkdir(parents=True,exist_ok=True)
 if (folder/'data.npz').exists():continue
 seed=[20260910,n,k,8,a.rep];d=2**n;lam=np.r_[np.full(8,1/8),np.zeros(d-8)]
 start=time.perf_counter()
 if k==2:means=records_two(n,np.eye(d,dtype=complex),lam,sizes,seed)
 else:means=np.array([records_general(n,k,8,sizes[0],seed,folder/'records')])
 assert np.max(np.abs(np.trace(means,axis1=1,axis2=2)-1))<1e-9
 temp=folder/'data.tmp.npz';np.savez_compressed(temp,means=means,sizes=sizes,lam=lam);temp.replace(folder/'data.npz')
 save_json(folder/'metadata.json',dict(n=n,k=k,rep=a.rep,true_rank=8,seed=seed,sizes=sizes,seconds=time.perf_counter()-start,
  sampling='Same sampler as repetitions 0--19; new repetition-indexed random stream. For k>2 actual Stim Clifford draws are archived because its sampler has no seed API.'))
 print('DATA',a.rep,n,k,flush=True)
 if 64*d in sizes and k==2:
  dest=HERE/'memory_inputs'/f'rep_{a.rep:03d}';dest.mkdir(parents=True,exist_ok=True)
  np.save(dest/f'n{n}.npy',means[sizes.index(64*d)])
# Also repair a missing memory cache when resuming an already-saved dataset.
for n,k,sizes in settings:
 if k==2 and 64*(2**n) in sizes:
  dest=HERE/'memory_inputs'/f'rep_{a.rep:03d}';dest.mkdir(parents=True,exist_ok=True)
  if not (dest/f'n{n}.npy').exists():
   with np.load(HERE/'data'/f'rep_{a.rep:03d}'/f'n{n}_k{k}'/'data.npz') as data:
    np.save(dest/f'n{n}.npy',data['means'][list(data['sizes']).index(64*(2**n))])
