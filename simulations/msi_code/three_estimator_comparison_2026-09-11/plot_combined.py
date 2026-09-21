"""Combine the three completed comparisons into one six-panel figure."""
import hashlib
import json
import os
from pathlib import Path

os.environ.setdefault("MPLCONFIGDIR", "/tmp/minimax-three-estimator-mpl")
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.lines import Line2D
import numpy as np

OUT = Path(__file__).resolve().parent
SOURCE = OUT / "selected_summary.json"
data = json.loads(SOURCE.read_text())
names = ["PLS", "OMD_stat", "MW_line_search_identity"]
assert data["status"] == "passed" and data["methods"] == names
assert len(data["rows"]) == 30 and len(data["memory"]) == 12
stats = {(r["case_index"], r["method"]): r for r in data["rows"]}
memory = {(r["d"], r["method"]): r for r in data["memory"]}
for r in data["rows"]:
    assert r["repetitions"] == 100 and r["timing_repeats"] == 3
    assert r["trace_norm_error_ci_low"] <= r["trace_norm_error"] <= r["trace_norm_error_ci_high"]
    assert 0 < r["seconds_q25"] <= r["seconds"] <= r["seconds_q75"]
for r in data["memory"]:
    assert r["profiles"] == 100 and 0 < r["q25_MiB"] <= r["median_MiB"] <= r["q75_MiB"]

colors = ["#0072B2", "#D55E00", "#009E73"]
markers = ["o", "s", "^"]
labels = ["PLS", "OMD (statistical)", "MW-PLS (statistical, identity start)"]
plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.labelcolor": "#263442", "text.color": "#263442",
                     "axes.titleweight": "bold", "svg.fonttype": "none"})
fig, axes = plt.subplots(3, 2, figsize=(13.2, 15.6))
fig.subplots_adjust(left=.085, right=.975, top=.855, bottom=.17, wspace=.25, hspace=.7)
fig.suptitle("Three estimators · Three controlled comparisons", fontsize=19, fontweight="bold", y=.985)
fig.text(.5, .956, "Completed MSI results · 100 independent paired datasets per configuration · True rank 8",
         ha="center", fontsize=11.5)
handles = [Line2D([], [], color=c, marker=m, lw=2, ms=6, label=l)
           for c, m, l in zip(colors, markers, labels)]
fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(.5, .937), ncol=3, frameon=False, fontsize=11)
runtime_ylim = (min(r["seconds_q25"] for r in data["rows"]) / 1.7,
                max(r["seconds_q75"] for r in data["rows"]) * 1.7)
plotted = []

def draw(ax, xs, ids, value, lower, upper, *, is_memory=False):
    for name, color, marker in zip(names, colors, markers):
        rs = [memory[(d, name)] for d in xs] if is_memory else [stats[(ci, name)] for ci in ids]
        ys = [r[value] for r in rs]
        lo = [r[lower] for r in rs]
        hi = [r[upper] for r in rs]
        ax.fill_between(xs, lo, hi, color=color, alpha=.17, linewidth=0)
        line, = ax.plot(xs, ys, color=color, marker=marker, lw=2, ms=6,
                        markeredgecolor="white", markeredgewidth=.6)
        np.testing.assert_array_equal(line.get_ydata(), ys)
        plotted.append({"method": name, "metric": value, "x": xs, "y": ys,
                        "band_lower": lo, "band_upper": hi})
    assert len(ax.lines) == 3
    ax.set_xscale("log", base=2)
    ax.set_xlim(min(xs) / 1.13, max(xs) * 1.13)
    ax.grid(axis="y", alpha=.2)
    ax.set_axisbelow(True)
    if value == "seconds":
        ax.set_yscale("log")
        ax.set_ylim(*runtime_ylim)
        ax.set_ylabel("Median solver time (seconds)")
    elif value == "trace_norm_error":
        ax.set_ylim(0, 2)
        ax.set_ylabel(r"Mean trace-norm error $\|\widehat\rho-\rho\|_{\rm tr}$")
    else:
        ax.set_ylim(bottom=0)
        ax.set_ylabel("Median peak process memory (MiB)")

specs = [
    ([0, 1, 2, 3, 4], [1024, 4096, 16384, 65536, 262144],
     ["1,024", "4,096", "16,384", "65,536", "262,144"], r"Measurements $T$",
     r"1. Vary measurements $T$     |     $n=8$, $d=256$, $k=2$; same state"),
    ([2, 5, 6], [2, 4, 8], ["2", "4", "8 (global)"], r"Block size $k$",
     r"2. Vary block size $k$     |     $n=8$, $d=256$, $T=16{,}384$; same state"),
    ([7, 8, 2, 9], [16, 64, 256, 1024], ["16\n4 qubits", "64\n6 qubits", "256\n8 qubits", "1,024\n10 qubits"],
     r"Dimension $d=2^n$", r"3. Vary dimension $d$     |     $k=2$, $T/d=64$; true rank 8"),
]
for row, (ids, xs, ticks, xlabel, title) in enumerate(specs):
    if row < 2:
        draw(axes[row, 0], xs, ids, "trace_norm_error", "trace_norm_error_ci_low", "trace_norm_error_ci_high")
        draw(axes[row, 1], xs, ids, "seconds", "seconds_q25", "seconds_q75")
        titles = ["Reconstruction error", "Solver runtime"]
    else:
        draw(axes[row, 0], xs, ids, "seconds", "seconds_q25", "seconds_q75")
        draw(axes[row, 1], xs, ids, "median_MiB", "q25_MiB", "q75_MiB", is_memory=True)
        titles = ["Solver runtime", "Peak process memory"]
    for col, ax in enumerate(axes[row]):
        ax.set_xticks(xs, ticks)
        ax.set_xlabel(xlabel)
        ax.set_title(f"({chr(97 + 2 * row + col)}) {titles[col]}", loc="left", fontsize=11.5, pad=8)
    y = axes[row, 0].get_position().y1 + .036
    fig.text(.085, y, title, fontsize=12.4, fontweight="bold", ha="left", va="bottom")

footer = (
    "Shading: 95% pointwise bootstrap intervals for mean error; IQR for runtime and fresh-process memory.\n"
    "Timings: median of three fresh solves after a discarded full warm-up; initialization included. Runtime panels share one log scale.\n"
    r"MW-PLS: line-search Frank–Wolfe from $I_d/d$, gap $\leq\min\{1,d/T\}$. OMD: statistical gap $\leq\min\{1,\sqrt{d/T}\}$." + "\n"
    "At k=n=8, PLS/OMD use the shared exact solution, also minimizing MW; the MW curve retains its generic iterative route.\n"
    "Four allocated CPU cores. Different objective-gap criteria; these fixed-state, small-block experiments do not establish minimaxity."
)
fig.text(.5, .025, footer, ha="center", va="bottom", fontsize=9.3, linespacing=1.65)
assert len(plotted) == 18
for ext in ["png", "svg"]:
    fig.savefig(OUT / f"three_comparisons_combined.{ext}", dpi=220, facecolor="white")
plt.close(fig)
audit = {"status": "passed", "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
         "panels": 6, "curves_per_panel": 3, "plotted_series": plotted,
         "common_runtime_limits_seconds": runtime_ylim,
         "scope": "Selected stored summaries are plotted without new estimation, smoothing, or resampling."}
(OUT / "combined_validation.json").write_text(json.dumps(audit, indent=2) + "\n")
print("Saved combined PNG/SVG; six panels each contain the three selected procedures.")
