"""Small fresh-data experiment for the reviewed solver correction."""
import argparse
import json
from pathlib import Path
import sys
import time

import numpy as np

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))
from estimators import Channel, solve_estimator, independent_validation
from sampling import sample_means
from runtime_io import hardware, save_json
from run_identity import (source_hashes, file_hash, cache_identity, check_cached_result,
                          artifact_hashes, seal_result, StaleResultError)


def run(config_path, task):
    config = json.loads(Path(config_path).read_text())
    repetitions = config['repetitions']
    case = config['cases'][task // repetitions]
    rep = task % repetitions
    data_rep = config['seed_offset'] + rep
    folder = ROOT / 'results' / config['name'] / ('n%d_k%d_%s_rep%03d' % (case['n'],case['k'],case['family'],rep))
    folder.mkdir(parents=True, exist_ok=True)
    data_path, summary_path = folder/'data.npz', folder/'summary.json'
    identity_config = dict(config=config, task=task, driver_sha256=file_hash(__file__))
    if summary_path.exists():
        if not data_path.exists():
            raise StaleResultError('Cached review run is missing its input.')
        identity = cache_identity(identity_config, {'data.npz':file_hash(data_path)})
        if check_cached_result(summary_path,identity) is not None:
            return
        with np.load(data_path) as data:
            rho,means=data['rho'],data['means']
        sampling=json.loads((folder/'sampling.json').read_text())
    else:
        if data_path.exists():
            raise StaleResultError('Untracked data would bypass generation provenance.')
        print('SAMPLING',task,case,'new repetition seed',data_rep,flush=True)
        start=time.perf_counter()
        rho,means,counts,sampling=sample_means(case['n'],case['k'],case['family'],
                                             config['sizes'],data_rep)
        sampling['seconds']=time.perf_counter()-start
        np.savez_compressed(data_path,rho=rho,means=means,counts=counts,sizes=config['sizes'])
        save_json(folder/'sampling.json',sampling)
    identity=cache_identity(identity_config,{'data.npz':file_hash(data_path)})
    row=dict(status='running',case=case,rep=rep,data_rep=data_rep,hardware=hardware(),
             sampling=sampling,source_sha256=source_hashes(),cache_identity=identity,records=[])
    save_json(summary_path,row)
    c=Channel(case['n'],case['k'])
    for T,b in zip(config['sizes'],means):
        saved={}
        for profile in config['profiles']:
            method,tau,label=profile['method'],profile['tol_factor'],profile['label']
            x,stats=solve_estimator(c,b,T,method,tol_factor=tau,**config['solver_options'])
            check=independent_validation(c,b,T,x,method,stats,rho=rho,tol_factor=tau)
            witness=stats.pop('_dual_witness',None)
            saved[label]=x
            if witness is not None:saved[label+'_dual']=witness
            row['records'].append(dict(T=T,profile=label,method=method,tol_factor=tau,
                                       stats=stats,validation=check))
            save_json(summary_path,row)
            print('FIT',task,T,label,'accepted',check['accepted'],
                  'loss',check['trace_norm_error'],'iterations',stats['iterations'],flush=True)
        np.savez_compressed(folder/('estimates_T%d.npz'%T),**saved)
        if c.k==c.n:
            assert all(np.array_equal(saved['PLS'],x) for name,x in saved.items() if not name.endswith('_dual'))
    row['failed_records']=[dict(T=r['T'],profile=r['profile']) for r in row['records'] if not r['validation']['accepted']]
    row['status']='complete' if not row['failed_records'] else 'incomplete_methods'
    row['artifact_sha256']=artifact_hashes(folder,('*.npz','sampling.json'))
    save_json(summary_path,seal_result(row))
    if row['failed_records']:
        raise RuntimeError('Unaccepted fits retained: '+str(row['failed_records']))


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('config',type=Path);p.add_argument('task',type=int)
    args=p.parse_args();run(args.config,args.task)
