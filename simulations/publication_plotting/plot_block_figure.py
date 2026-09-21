"""Render the supplemental block-size figure from the MSI-matched summary."""
from pathlib import Path
import json
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt
BASE=Path(__file__).resolve().parent
OUT=BASE/'generated'
OUT.mkdir(exist_ok=True)
rows=json.loads((BASE/'data/corrected_block_summary.json').read_text())['rows']
METHODS=('PLS','OMD','MW-PLS')
COLORS={'PLS':'#1769AA','OMD':'#D17A00','MW-PLS':'#8A3FA0'}
MARKERS={'PLS':'o','OMD':'s','MW-PLS':'^'}
STYLES={'PLS':'-','OMD':'--','MW-PLS':'-.'}
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
    fig.savefig(OUT/('vary_block_size_three.'+extension),dpi=220,bbox_inches='tight')
plt.close(fig)

print("Block comparison written to",OUT)
