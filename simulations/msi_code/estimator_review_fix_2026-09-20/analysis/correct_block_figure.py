"""Retain k<n records and use fresh shared-spectral timings at k=n."""
import json
from pathlib import Path
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
from summarize_results import METHODS, COLORS, MARKERS, STYLES, global_summary

ROOT = Path(__file__).resolve().parent.parent
old_path = ROOT / 'original/msi_snapshot/three_estimator_comparison_2026-09-11/selected_summary.json'
old = json.loads(old_path.read_text())
fresh = global_summary()
names = {'PLS':'PLS', 'OMD_stat':'OMD', 'MW_line_search_identity':'MW-PLS'}
rows = []
for row in old['rows']:
    if row['case_index'] not in [2, 5]:
        continue
    rows.append(dict(k=row['k'], method=names[row['method']], repetitions=row['repetitions'],
                     trace_norm_error=row['trace_norm_error'], error_ci_low=row['trace_norm_error_ci_low'],
                     error_ci_high=row['trace_norm_error_ci_high'], median_seconds=row['seconds'],
                     seconds_q25=row['seconds_q25'], seconds_q75=row['seconds_q75'],
                     source='Original 2026-09-11 paired benchmark; k<n unchanged'))
for row in fresh['rows']:
    rows.append(dict(row, k=8, source='Fresh 2026-09-20 common spectral rerun on original input hashes'))
assert len(rows) == 9
result = dict(n=8, d=256, T=16384, rows=rows, global_output_max_difference=fresh['max_pairwise_output_difference'])
(ROOT/'reports/corrected_block_summary.json').write_text(json.dumps(result,indent=2)+'\n')

plt.rcParams.update({'font.size':11,'axes.spines.top':False,'axes.spines.right':False,'pdf.fonttype':42})
fig, axes = plt.subplots(1, 2, figsize=(10.8, 4.1), layout='constrained')
for method in METHODS:
    selected = sorted([r for r in rows if r['method']==method], key=lambda r:r['k'])
    x = [r['k'] for r in selected]
    axes[0].plot(x,[r['trace_norm_error'] for r in selected],label=method,color=COLORS[method],
                 linestyle=STYLES[method],marker=MARKERS[method],markerfacecolor='white',linewidth=2,markersize=6)
    axes[0].fill_between(x,[r['error_ci_low'] for r in selected],[r['error_ci_high'] for r in selected],
                         color=COLORS[method],alpha=.13)
    axes[1].plot(x,[r['median_seconds'] for r in selected],label=method,color=COLORS[method],
                 linestyle=STYLES[method],marker=MARKERS[method],markerfacecolor='white',linewidth=2,markersize=6)
    axes[1].fill_between(x,[r['seconds_q25'] for r in selected],[r['seconds_q75'] for r in selected],
                         color=COLORS[method],alpha=.13)
axes[0].set_ylabel('Mean trace-norm error');axes[0].set_ylim(0,2)
axes[1].set_ylabel('Median solver time (seconds)');axes[1].set_yscale('log')
axes[0].set_title('Reconstruction error');axes[1].set_title('Solver time')
for ax in axes:
    ax.set_xticks([2,4,8]);ax.set_xlabel('Block size k');ax.grid(True,alpha=.25)
    ax.axvspan(7.7,8.3,color='#d7dce2',alpha=.20,zorder=0)
axes[1].text(.96,.97,'k=n: same spectral routine',ha='right',va='top',fontsize=9,transform=axes[1].transAxes)
fig.legend(*axes[0].get_legend_handles_labels(),loc='outside upper center',ncol=3,frameon=False)
for extension in ['png','pdf','svg']:
    fig.savefig(ROOT/'figures'/('vary_block_size_three_corrected.'+extension),dpi=220,bbox_inches='tight')
plt.close(fig)
print(json.dumps(fresh,indent=2))
