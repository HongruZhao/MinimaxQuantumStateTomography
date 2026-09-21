"""Validate complete paired runs, summarize uncertainty, and draw raw curves."""
import argparse
import csv
import hashlib
import json
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent.parent
METHODS = ('PLS', 'OMD', 'MW-PLS')
COLORS = {'PLS': '#1769AA', 'OMD': '#D17A00', 'MW-PLS': '#8A3FA0'}
MARKERS = {'PLS': 'o', 'OMD': 's', 'MW-PLS': '^'}
STYLES = {'PLS': '-', 'OMD': '--', 'MW-PLS': '-.'}
FAMILIES = {'rank8_diagonal': 'Rank 8, diagonal', 'rank8_rotated': 'Rank 8, rotated',
            'polynomial_rotated': 'Polynomial decay, rotated'}


def save_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def mean_ci(values, indices):
    values = np.asarray(values)
    means = values[indices].mean(axis=1)
    return [float(values.mean()), *map(float, np.quantile(means, [.025, .975]))]


def summarize_study(name, allow_incomplete=False):
    config = json.loads((ROOT / 'configs' / (name + '.json')).read_text())
    expected = len(config['cases']) * config['repetitions']
    records = [json.loads(p.read_text()) for p in sorted((ROOT / 'results' / name).glob('*/summary.json'))]
    failures = [dict(case=x['case'], rep=x['rep'], status=x['status'], failed=x.get('failed_records', []))
                for x in records if x['status'] != 'complete']
    if not allow_incomplete:
        assert len(records) == expected, (name, len(records), expected)
        assert not failures, failures
    complete = [r for r in records if r['status'] == 'complete']
    rows = []
    checks = 0
    for case_index, case in enumerate(config['cases']):
        selected = sorted([r for r in complete if r['case'] == case], key=lambda r: r['rep'])
        if not selected:
            continue
        assert len(set(r['rep'] for r in selected)) == len(selected)
        rng = np.random.default_rng([20260920, 1901, case_index, case['n']])
        indices = rng.integers(len(selected), size=(10000, len(selected)))
        for T in case['sizes']:
            for dataset in selected:
                paired = [r for r in dataset['records'] if r['T'] == T]
                assert set(r['method'] for r in paired) == set(METHODS)
                assert len(set(r['mean_sha256'] for r in paired)) == 1
                assert all(r['validation']['accepted'] for r in paired)
                checks += len(paired)
            for method in METHODS:
                cells = [next(r for r in dataset['records'] if r['T'] == T and r['method'] == method) for dataset in selected]
                error, low, high = mean_ci([r['validation']['trace_norm_error'] for r in cells], indices)
                seconds = np.array([r['stats']['wall_seconds'] for r in cells])
                ratios = []
                for r in cells:
                    v, s = r['validation'], r['stats']
                    if case['n'] == case['k']:
                        ratio = max(v['omd_gap'], v['mw_gap'])
                    elif method == 'PLS':
                        ratio = v['pls_full_projection_difference']
                    elif method == 'OMD':
                        ratio = max(v['omd_gap'] / s['original_gap_tolerance'],
                                    v['regularized_gap'] / s['regularized_gap_tolerance'])
                    else:
                        ratio = v['mw_gap'] / s['epsilon_Q']
                    ratios.append(ratio)
                rows.append(dict(n=case['n'], d=2**case['n'], k=case['k'], family=case['family'],
                                 T=T, method=method, repetitions=len(cells), trace_norm_error=error,
                                 error_ci_low=low, error_ci_high=high, median_seconds=float(np.median(seconds)),
                                 seconds_q25=float(np.quantile(seconds, .25)), seconds_q75=float(np.quantile(seconds, .75)),
                                 max_stopping_ratio_or_projection_error=float(max(ratios)),
                                 all_accepted=True))
    result = dict(name=name, expected_datasets=expected, available_datasets=len(records),
                  complete_datasets=len(complete), failed_datasets=failures, checked_fits=checks,
                  status='complete' if len(complete) == expected and not failures else 'incomplete', rows=rows)
    save_json(ROOT / 'reports' / (name + '_summary.json'), result)
    if rows:
        with (ROOT / 'reports' / (name + '_summary.csv')).open('w', newline='') as f:
            writer = csv.DictWriter(f, fieldnames=list(rows[0]))
            writer.writeheader(); writer.writerows(rows)
    return result


def global_summary():
    datasets = [json.loads(p.read_text()) for p in sorted((ROOT / 'results/global_rebenchmark').glob('*/summary.json'))]
    assert len(datasets) == 100 and all(d['status'] == 'complete' for d in datasets)
    assert len(set(d['rep'] for d in datasets)) == 100
    indices = np.random.default_rng(2026092019).integers(100, size=(10000, 100))
    rows = []
    for method in METHODS:
        error, low, high = mean_ci([d['methods'][method]['validation']['trace_norm_error'] for d in datasets], indices)
        seconds = np.array([d['methods'][method]['median_seconds'] for d in datasets])
        rows.append(dict(method=method, repetitions=100, trace_norm_error=error,
                         error_ci_low=low, error_ci_high=high, median_seconds=float(np.median(seconds)),
                         seconds_q25=float(np.quantile(seconds, .25)), seconds_q75=float(np.quantile(seconds, .75))))
    result = dict(status='complete', rows=rows,
                  max_pairwise_output_difference=max(max(d['pairwise_frobenius_differences'].values()) for d in datasets),
                  max_independent_mw_gap=max(r['validation']['mw_gap'] for d in datasets for r in d['measured']),
                  max_independent_omd_gap=max(r['validation']['omd_gap'] for d in datasets for r in d['measured']))
    save_json(ROOT / 'reports/global_summary.json', result)
    return result


def curves(ax, rows, log_error=True):
    for method in METHODS:
        cells = sorted([r for r in rows if r['method'] == method], key=lambda r: r['T'])
        x = [r['T'] for r in cells]
        y = [r['trace_norm_error'] for r in cells]
        ax.plot(x, y, color=COLORS[method], linestyle=STYLES[method], marker=MARKERS[method],
                label=method, linewidth=1.8, markersize=4, markerfacecolor='white')
        ax.fill_between(x, [r['error_ci_low'] for r in cells], [r['error_ci_high'] for r in cells],
                        color=COLORS[method], alpha=.12, linewidth=0)
    ax.set_xscale('log', base=10)
    if log_error:
        ax.set_yscale('log')
    else:
        ax.set_ylim(bottom=0)
    ax.grid(True, which='major', color='#d8dde3', linewidth=.6)
    ax.set_xlabel('Copies T')
    ax.set_ylabel('Mean trace-norm error')


def draw_studies(small, large):
    plt.rcParams.update({'font.size': 13, 'axes.spines.top': False, 'axes.spines.right': False,
                         'pdf.fonttype': 42, 'ps.fonttype': 42})
    for log_error in [True, False]:
        fig, axes = plt.subplots(2, 3, figsize=(13.1, 8.2))
        fig.subplots_adjust(left=.075, right=.99, bottom=.075, top=.83, wspace=.30, hspace=.52)
        for i, k in enumerate([2, 4]):
            for j, family in enumerate(FAMILIES):
                cells = [r for r in small['rows'] if r['k'] == k and r['family'] == family]
                if not cells:
                    continue
                curves(axes[i, j], cells, log_error=log_error)
                axes[i, j].set_title(FAMILIES[family] + ('\nPeriodic blocks, k=2' if k == 2 else '\nGlobal Clifford, k=4'))
                if k == 4:
                    axes[i, j].text(.97, .97, 'All three outputs coincide', transform=axes[i, j].transAxes,
                                    ha='right', va='top', fontsize=9)
        handles, labels = axes[0, 0].get_legend_handles_labels()
        fig.legend(handles, labels, loc='upper center', bbox_to_anchor=(.5,.952), ncol=3, frameon=False)
        title = 'Increasing sample size: d=16, 20 independent datasets per state/design'
        if small['status'] != 'complete':
            title = 'PRELIMINARY: d=16, %d of %d datasets complete' % (small['complete_datasets'], small['expected_datasets'])
        fig.suptitle(title, y=.993, fontsize=14)
        suffix = 'log' if log_error else 'linear'
        for extension in ['png', 'pdf']:
            fig.savefig(ROOT / 'figures' / ('convergence_n4_' + suffix + '.' + extension), dpi=200, bbox_inches='tight')
        plt.close(fig)
    if large['rows']:
        fig, axes = plt.subplots(1, 2, figsize=(11, 4.8))
        fig.subplots_adjust(left=.085, right=.985, bottom=.145, top=.77, wspace=.32)
        curves(axes[0], large['rows'], log_error=False)
        curves(axes[1], large['rows'], log_error=True)
        axes[0].set_title('Trace-norm error decreases with T')
        axes[1].set_title('The same errors on logarithmic axes')
        handles, labels = axes[0].get_legend_handles_labels()
        fig.legend(handles, labels, loc='upper center', bbox_to_anchor=(.5,.94), ncol=3, frameon=False)
        title = 'Paper setting: d=256, k=2, rank 8; new paired datasets'
        if large['status'] != 'complete':
            title = 'PRELIMINARY: d=256, %d of %d datasets complete' % (large['complete_datasets'], large['expected_datasets'])
        fig.suptitle(title, y=.993, fontsize=14)
        for extension in ['png', 'pdf']:
            fig.savefig(ROOT / 'figures' / ('convergence_n8.' + extension), dpi=200, bbox_inches='tight')
        plt.close(fig)
    fig, ax = plt.subplots(figsize=(8.8, 4.6), layout='constrained')
    for method in ['OMD', 'MW-PLS']:
        for study, style in [(small, '-'), (large, '--')]:
            ts = sorted(set(r['T'] for r in study['rows'] if r['k'] < r['n']))
            maxima = [max(r['max_stopping_ratio_or_projection_error'] for r in study['rows']
                          if r['T'] == t and r['method'] == method and r['k'] < r['n']) for t in ts]
            ax.plot(ts, maxima, color=COLORS[method], linestyle=style, marker=MARKERS[method],
                    label=method + (' d=16 (all states)' if study is small else ' d=256'))
    ax.axhline(1, color='#444444', linewidth=1, label='Acceptance threshold')
    ax.set_xscale('log'); ax.set_ylim(0, 1.08)
    ax.set_xlabel('Copies T'); ax.set_ylabel('Largest recomputed gap / its allowed tolerance')
    ax.set_title('Optimization checks across every retained dataset')
    ax.grid(True, alpha=.25); ax.legend(fontsize=9, ncol=2, loc='lower left')
    for extension in ['png', 'pdf']:
        fig.savefig(ROOT / 'figures' / ('stopping_checks.' + extension), dpi=200, bbox_inches='tight')
    plt.close(fig)


def draw_global(result):
    rows = result['rows']
    fig, axes = plt.subplots(1, 2, figsize=(10.6, 4.1), layout='constrained')
    x = np.arange(3)
    errors = [r['trace_norm_error'] for r in rows]
    axes[0].errorbar(x, errors,
                    yerr=[[r['trace_norm_error'] - r['error_ci_low'] for r in rows],
                          [r['error_ci_high'] - r['trace_norm_error'] for r in rows]],
                    fmt='o', capsize=5, color='#26384C')
    axes[0].set_ylabel('Mean trace-norm error')
    axes[0].set_title('Identical estimates and errors')
    times = np.array([r['median_seconds'] for r in rows]) * 1000
    axes[1].bar(x, times, color=[COLORS[m] for m in METHODS], width=.6)
    axes[1].errorbar(x, times,
                    yerr=[times-np.array([r['seconds_q25'] for r in rows])*1000,
                          np.array([r['seconds_q75'] for r in rows])*1000-times],
                    fmt='none', color='#26384C', capsize=5)
    axes[1].set_ylabel('Median solver time (milliseconds)')
    axes[1].set_title('Same computation; independently measured times')
    for ax in axes:
        ax.set_xticks(x, METHODS); ax.grid(True, axis='y', alpha=.25); ax.set_axisbelow(True)
    fig.suptitle('Corrected global case: n=k=8, T=16384, 100 original datasets', y=1.06, fontsize=13)
    for extension in ['png','pdf']:
        fig.savefig(ROOT/'figures'/('global_corrected.'+extension),dpi=200,bbox_inches='tight')
    plt.close(fig)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--allow-incomplete', action='store_true')
    args = parser.parse_args()
    (ROOT / 'figures').mkdir(exist_ok=True)
    global_result = global_summary(); draw_global(global_result)
    small = summarize_study('convergence_n4', args.allow_incomplete)
    large = summarize_study('convergence_n8', args.allow_incomplete)
    if small['rows']:
        draw_studies(small, large)
    print(json.dumps({'global':global_result, 'n4_status':small['status'], 'n8_status':large['status']},indent=2))
