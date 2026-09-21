"""Draw the supplemental comparison from the saved default-tolerance fits.

The publication figure contains only PLS, OMD and MW-PLS. Numerical records
and their validation receipts are read without modification.
"""
from pathlib import Path
import csv
import json
import hashlib
import matplotlib

matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parent
DEST = ROOT / 'generated'
source = ROOT / 'data/fresh_summary.csv'
with source.open(newline='') as stream:
    rows = list(csv.DictReader(stream))
methods = [('PLS', 'PLS', '#2878b5'), ('OMD', 'OMD', '#e07b26'),
           ('MW_PLS', 'MW-PLS', '#269767')]
selected = [row for row in rows if row['profile'] in {m[0] for m in methods}]
assert len(selected) == 36
assert all(int(row['repetitions']) == 5 for row in selected)
receipt = json.loads((ROOT / 'data/fresh_review_validation.json').read_text())
fits = [row for row in receipt['attempts'] if row['profile'] in {m[0] for m in methods}]
assert len(fits) == 180 and all(row['accepted'] for row in fits)
plt.rcParams.update({'font.size': 8, 'axes.titlesize': 9, 'axes.labelsize': 8})
fig, axes = plt.subplots(1, 3, figsize=(7.35, 2.7), sharey=True)
titles = ['Periodic, k = 2: rank 8', 'Periodic, k = 2: polynomial spectrum',
          'Global, k = 4: rank 8']
sizes = [2**8, 2**12, 2**16, 2**20]
for case, ax in enumerate(axes):
    shown = methods if case < 2 else [('PLS', 'PLS = OMD = MW-PLS', '#283b4e')]
    for method, label, color in shown:
        group = sorted([r for r in selected if int(r['case_id']) == case and r['profile'] == method],
                       key=lambda r: int(r['T']))
        assert [int(r['T']) for r in group] == sizes
        ax.plot(sizes, [float(r['mean']) for r in group], 'o-', color=color,
                linewidth=1.6, markersize=3.5, label=label)
        ax.fill_between(sizes, [float(r['minimum']) for r in group],
                        [float(r['maximum']) for r in group], color=color, alpha=.12)
    ax.set(xscale='log', yscale='log', title=titles[case], xlabel='Number of measurements T',
           ylim=(.02, 2))
    ax.set_xticks(sizes, [r'$2^8$', r'$2^{12}$', r'$2^{16}$', r'$2^{20}$'])
    ax.grid(True, which='major', alpha=.2)
    ax.spines[['top', 'right']].set_visible(False)
    ax.legend(loc='lower left', fontsize=6.8, frameon=False)
axes[0].set_ylabel('Mean trace norm error')
fig.tight_layout(pad=.8, w_pad=.9)
DEST.mkdir(parents=True, exist_ok=True)
for extension in ['pdf', 'png']:
    fig.savefig(DEST / ('fresh_reconstruction_comparison.' + extension), dpi=220)
plt.close(fig)
print(json.dumps({'default_fits': len(fits), 'plotted_settings': len(selected),
                  'source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
                  'output': str(DEST / 'fresh_reconstruction_comparison.pdf')}, indent=2))
