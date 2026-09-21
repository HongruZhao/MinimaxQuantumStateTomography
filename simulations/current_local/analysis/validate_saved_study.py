"""Verify saved numerical fits and summarize the supplemental study."""
from pathlib import Path
import csv
import json
import sys

import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'src'))
from estimators import Channel, independent_validation
from run_identity import (canonical_hash, file_hash, source_hashes,
                          cache_identity, check_cached_result)
from runtime_io import save_json


def verify_envelope(folder, row):
    assert row['source_sha256'] == source_hashes()
    assert row['result_sha256'] == canonical_hash({k:v for k,v in row.items() if k!='result_sha256'})
    for p,h in row['artifact_sha256'].items():
        assert file_hash(folder/p)==h, (folder,p)


def main():
    config=json.loads((ROOT/'configs/review_fresh.json').read_text())
    finals={}
    attempts=[]
    globals_checked=0
    for case_id,case in enumerate(config['cases']):
        c=Channel(case['n'],case['k'])
        for rep in range(config['repetitions']):
            name='n%d_k%d_%s_rep%03d'%(case['n'],case['k'],case['family'],rep)
            folder=ROOT/'results/review_fresh'/name
            row=json.loads((folder/'summary.json').read_text())
            verify_envelope(folder,row)
            expected=cache_identity(dict(config=config,task=case_id*config['repetitions']+rep,
                                         driver_sha256=file_hash(ROOT/'analysis/run_review_simulation.py')),
                                    {'data.npz':file_hash(folder/'data.npz')})
            assert row['cache_identity']==expected
            assert row['data_rep']==config['seed_offset']+rep
            assert row['sampling']['seed']==[20260920,case['n'],case['k'],
                   {'rank8_rotated':1,'polynomial_rotated':2}[case['family']],config['seed_offset']+rep]
            with np.load(folder/'data.npz') as data:
                rho,means,sizes=data['rho'],data['means'],list(data['sizes'])
            assert sizes==config['sizes'] and len(row['records'])==16
            for record in row['records']:
                T,label=record['T'],record['profile']
                profile=next(p for p in config['profiles'] if p['label']==label)
                assert record['tol_factor']==profile['tol_factor'] and record['method']==profile['method']
                with np.load(folder/('estimates_T%d.npz'%T)) as arrays:
                    x=arrays[label]
                    stats=dict(record['stats'])
                    if label+'_dual' in arrays:
                        stats['_dual_witness']=arrays[label+'_dual']
                    if c.k==c.n:
                        assert np.array_equal(x,arrays['PLS'])
                        globals_checked+=1
                check=independent_validation(c,means[sizes.index(T)],T,x,record['method'],stats,
                                             rho=rho,tol_factor=profile['tol_factor'])
                assert check['accepted']==record['validation']['accepted']
                assert abs(check['trace_norm_error']-record['validation']['trace_norm_error'])<1e-10
                result=dict(case_id=case_id,case=case,rep=rep,T=T,profile=label,
                            loss=check['trace_norm_error'],accepted=check['accepted'],
                            iterations=stats['iterations'],seconds=stats['wall_seconds'],
                            validation=check,source=str(folder.relative_to(ROOT)))
                attempts.append(result)
                finals[(case_id,rep,T,label)]=result
    assert len(attempts)==240
    initial_failures=[r for r in attempts if not r['accepted']]
    assert len(initial_failures)==1
    failed=initial_failures[0]
    assert (failed['case_id'],failed['rep'],failed['T'],failed['profile'])==(1,3,1048576,'OMD_tight')
    extension=ROOT/'results/review_accuracy_extension'
    replay=json.loads((extension/'summary.json').read_text())
    verify_envelope(extension,replay)
    expected=replay['cache_identity']
    assert expected['configuration']['driver_sha256']==file_hash(ROOT/'analysis/refine_failed_accuracy.py')
    for path,h in expected['inputs'].items():
        assert file_hash(ROOT/path)==h
    assert check_cached_result(extension/'summary.json',cache_identity(expected['configuration'],expected['inputs']))
    original=ROOT/replay['original_attempt']
    with np.load(original/'data.npz') as data:
        b=data['means'][list(data['sizes']).index(replay['T'])]
        rho=data['rho']
    with np.load(extension/'estimate.npz') as data:
        stats=dict(replay['stats'],_dual_witness=data['dual'])
        check=independent_validation(Channel(4,2),b,replay['T'],data['estimate'],'OMD',stats,
                                     rho=rho,tol_factor=1e-6)
    assert check['accepted']
    result=dict(case_id=1,case=replay['case'],rep=3,T=replay['T'],profile='OMD_tight',
                loss=check['trace_norm_error'],accepted=True,iterations=stats['iterations'],
                seconds=stats['wall_seconds'],validation=check,source=str(extension.relative_to(ROOT)),
                all_attempt_seconds=stats['wall_seconds']+replay['original_attempt_seconds'])
    attempts.append(result)
    finals[(1,3,replay['T'],'OMD_tight')]=result
    assert all(r['accepted'] for r in finals.values())
    summaries=[]
    for case_id,case in enumerate(config['cases']):
        for T in config['sizes']:
            for profile in config['profiles']:
                label=profile['label']
                group=[finals[(case_id,rep,T,label)] for rep in range(config['repetitions'])]
                loss=np.array([r['loss'] for r in group])
                summaries.append(dict(case_id=case_id,n=case['n'],k=case['k'],family=case['family'],
                         T=T,profile=label,repetitions=len(group),mean=float(loss.mean()),
                         sd=float(loss.std(ddof=1)),minimum=float(loss.min()),maximum=float(loss.max()),
                         median_seconds=float(np.median([r.get('all_attempt_seconds',r['seconds']) for r in group])),
                         maximum_iterations=max(r['iterations'] for r in group)))
    with (ROOT/'reports/fresh_summary.csv').open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=list(summaries[0]));w.writeheader();w.writerows(summaries)
    gap_ratios={}
    for label in ['OMD','MW_PLS','OMD_tight']:
        group=[r for r in finals.values() if r['profile']==label and r['case']['k']<r['case']['n']]
        key,budget=('mw_gap','epsilon_Q') if label=='MW_PLS' else ('omd_gap','original_gap_tolerance')
        gap_ratios[label]=max(r['validation'][key]/r['validation']['independent_accuracy'][budget] for r in group)
    report=dict(status='passed',datasets=15,planned_fits=240,initial_accepted=239,
                initially_rejected=1,total_attempts=len(attempts),final_accepted=240,
                global_matrix_equality_checks=globals_checked,maximum_gap_ratios=gap_ratios,
                initial_failures=initial_failures,extension=result,summaries=summaries,
                source_sha256=source_hashes(),attempts=attempts)
    save_json(ROOT/'reports/fresh_review_validation.json',report)
    print(json.dumps({k: report[k] for k in ['status', 'datasets', 'total_attempts', 'final_accepted']}, indent=2))

if __name__ == '__main__':
    main()
