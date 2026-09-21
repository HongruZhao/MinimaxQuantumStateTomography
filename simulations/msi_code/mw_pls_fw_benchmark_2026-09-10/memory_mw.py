"""Separate fresh process for each method/dimension/input; capture peak RSS before validation."""
import argparse,json,resource,time,hashlib
from pathlib import Path
import numpy as np
from existing import Channel,HERE as OLD,hardware,save_json,CASES
from benchmark_mw import method_solve,validate
ROOT=Path(__file__).resolve().parent
p=argparse.ArgumentParser();p.add_argument('config',type=Path);p.add_argument('task',type=int);a=p.parse_args()
cfg=json.loads(a.config.read_text());cases=[7,8,2,9];reps=cfg['repetitions'];methods=cfg['methods'];count=len(reps)*len(methods)
assert 0<=a.task<4*count
ci=cases[a.task//count];rem=a.task%count;spec=methods[rem//len(reps)];rep=reps[rem%len(reps)];case=CASES[ci]
n,k,T=case['n'],case['k'],case['T'];d=2**n;assert d<=1024
out=ROOT/(cfg['output']+'_memory')/f"n{n}_{spec['name']}_rep{rep:03d}.json"
if out.exists():
    old=json.loads(out.read_text())
    if old['status']=='complete' and old['configuration']==spec:
        print('Retaining completed memory profile',out,flush=True);raise SystemExit(0)
source=OLD/'memory_inputs'/f'rep_{rep:03d}'/f'n{n}.npy'
start=time.perf_counter();b=np.load(source);b.flags.writeable=False;loadtime=time.perf_counter()-start
start=time.perf_counter();c=Channel(n,k);setuptime=time.perf_counter()-start
x,stats=method_solve(c,b,T,spec)
peak=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss/1024
check=validate(c,b,T,x,spec,stats)
row=dict(n=n,k=k,T=T,d=d,rep=rep,method=spec['name'],configuration=spec,status='complete' if stats['converged'] else 'not_converged',
   peak_process_MiB=peak,input_source=str(source),input_sha256=hashlib.sha256(b.tobytes()).hexdigest(),
   input_load_seconds=loadtime,channel_setup_seconds=setuptime,stats=stats,validation=check,hardware=hardware(),
   source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in ROOT.glob('*.py')},
   scope='Fresh-process peak RSS includes imports, one empirical mean, channel, solver and output; captured before post-solver validation.')
save_json(out,row);print(n,rep,spec['name'],row['status'],peak,flush=True)
