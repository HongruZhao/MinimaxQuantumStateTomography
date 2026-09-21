"""Render the two current main-paper figures from MSI-matched summary tables.

The compact publication layout keeps the original axis geometry and omits
text already supplied by the manuscript captions. This is plotting only;
it does not revalidate raw fits or recompute bootstrap intervals.
"""
import csv
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

BASE = Path(__file__).resolve().parent
OUT = BASE / "generated"
OUT.mkdir(exist_ok=True)
SOURCE = BASE / "data/selected_summary.json"
METHODS = ["PLS", "OMD_stat", "MW_line_search_identity"]
LABELS = ["PLS", "OMD (statistical)", "MW-PLS (statistical, identity start)"]
COLORS = ["#0072B2", "#D55E00", "#009E73"]
MARKERS = ["o", "s", "^"]
T_IDS = [0, 1, 2, 3, 4]
K_IDS = [2, 5, 6]
D_IDS = [7, 8, 2, 9]
IDS = sorted(set(T_IDS + K_IDS + D_IDS))
source = json.loads(SOURCE.read_text())
assert source["status"] == "passed"
rows = [r for r in source["rows"] if r["method"] in METHODS and r["case_index"] in IDS]
mem = [r for r in source["memory"] if r["method"] in METHODS]
assert len(rows) == 30 and len(mem) == 12
stats = {(r["case_index"], r["method"]): r for r in rows}
memstats = {(r["d"], r["method"]): r for r in mem}

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.labelcolor": "#263442", "text.color": "#263442",
                     "axes.titleweight": "semibold", "svg.fonttype": "none"})

def canvas(title, subtitle):
    fig, axes = plt.subplots(1, 2, figsize=(13.2, 5.75))
    fig.subplots_adjust(left=.075, right=.98, bottom=1-(1-.26)*6.7/5.75, top=1-(1-.72)*6.7/5.75, wspace=.27)
    fig.suptitle(title, fontsize=18, fontweight="semibold", y=1-(1-.965)*6.7/5.75)
    handles = [Line2D([], [], color=c, marker=m, lw=2, ms=6, label=l)
               for c, m, l in zip(COLORS, MARKERS, LABELS)]
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(.5, 1-(1-.855)*6.7/5.75), ncol=3, frameon=False, fontsize=11)
    for ax in axes:
        ax.grid(axis="y", alpha=.2)
        ax.set_axisbelow(True)
        ax.tick_params(axis="both", labelsize=10)
    return fig, axes

def curves(ax, xs, ids, value, lower, upper, memory=False):
    for name, color, marker in zip(METHODS, COLORS, MARKERS):
        rs = [memstats[(d, name)] for d in xs] if memory else [stats[(ci, name)] for ci in ids]
        ax.fill_between(xs, [r[lower] for r in rs], [r[upper] for r in rs], color=color, alpha=.16, linewidth=0)
        ax.plot(xs, [r[value] for r in rs], color=color, marker=marker, lw=2, ms=6,
                markeredgecolor="white", markeredgewidth=.6)
    ax.set_xscale("log", base=2)
    ax.set_xlim(min(xs) / 1.13, max(xs) * 1.13)

def save(fig, stem, uncertainty, note=None):
    for ext in ["png", "svg"]:
        fig.savefig(OUT / f"{stem}.{ext}", dpi=200, facecolor="white")
    plt.close(fig)

xs = [stats[(ci, "PLS")]["T"] for ci in T_IDS]
fig, axes = canvas("Accuracy and runtime as measurements increase",
                   r"$n=8$ qubits  ·  $d=256$  ·  $k=2$  ·  same rank-eight state  ·  100 paired datasets per point")
curves(axes[0], xs, T_IDS, "trace_norm_error", "trace_norm_error_ci_low", "trace_norm_error_ci_high")
curves(axes[1], xs, T_IDS, "seconds", "seconds_q25", "seconds_q75")
axes[0].set_title("(a) Reconstruction error", loc="left", fontsize=12)
axes[0].set_ylabel(r"Mean trace-norm error $\|\widehat\rho-\rho\|_{\rm tr}$")
axes[0].set_ylim(0, 2)
axes[1].set_title("(b) Solver runtime", loc="left", fontsize=12)
axes[1].set_ylabel("Median solver time (seconds)")
axes[1].set_yscale("log")
for ax in axes:
    ax.set_xticks(xs, [f"{x:,}" for x in xs])
    ax.set_xlabel(r"Measurements $T$")
save(fig, "vary_measurements_three", "Shading: pointwise 95% bootstrap intervals for mean error; IQR of per-dataset median runtimes from three fresh timed solves.")

dims = [16, 64, 256, 1024]
fig, axes = canvas("Runtime and memory as dimension increases",
                   r"$k=2$  ·  $T/d=64$  ·  true rank $8$  ·  100 paired datasets and 100 fresh-process memory profiles per method/point")
curves(axes[0], dims, D_IDS, "seconds", "seconds_q25", "seconds_q75")
curves(axes[1], dims, D_IDS, "median_MiB", "q25_MiB", "q75_MiB", memory=True)
axes[0].set_title("(a) Solver runtime", loc="left", fontsize=12)
axes[0].set_ylabel("Median solver time (seconds)")
axes[0].set_yscale("log")
axes[1].set_title("(b) Peak process memory", loc="left", fontsize=12)
axes[1].set_ylabel("Median peak process memory (MiB)")
axes[1].set_ylim(bottom=0)
for ax in axes:
    ax.set_xticks(dims, ["16\n4 qubits", "64\n6 qubits", "256\n8 qubits", "1,024\n10 qubits"])
    ax.set_xlabel(r"Dimension $d=2^n$")
save(fig, "vary_dimension_three", "Shading: IQR across datasets for runtime and across fresh processes for peak memory. Timings follow a discarded full warm-up.")


print("Main paper figures written to", OUT)
