import numpy as np
from stabilizer_sampling import one_record,supports

def apply_vector(v,u,support,n):
    rest=[q for q in range(n) if q not in support];axes=support+rest
    z=v.reshape((2,)*n).transpose(axes).reshape(2**len(support),-1)
    return (u@z).reshape((2,)*n).transpose(np.argsort(axes)).reshape(-1)

for n,k in [(4,2),(8,4),(8,8)]:
    for seed in range(4):
        latent=seed%8;v,b,gs=one_record(n,k,latent,seed)
        x=np.eye(2**n,dtype=complex)[:,latent]
        matrices=[]
        for g in gs:
            u=g.to_unitary_matrix(endian='big').astype(complex);mask=np.abs(u)>0
            u[mask]=u[mask]/np.abs(u[mask])/np.sqrt(mask[:,0].sum());matrices.append(u)
        for u,s in zip(matrices,supports(n,k)):x=apply_vector(x,u,s,n)
        assert abs(x[b])**2 > 1e-12
        x=np.eye(2**n,dtype=complex)[:,b]
        for u,s in reversed(list(zip(matrices,supports(n,k)))):x=apply_vector(x,u.conj().T,s,n)
        assert abs(abs(np.vdot(x,v))-1)<1e-11
        assert abs(np.linalg.norm(v)-1)<1e-12
print('Stabilizer Born outcomes and recovered projectors match dense circuit calculations for k=2,4,8.',flush=True)
