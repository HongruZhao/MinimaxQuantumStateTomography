"""Render three selected procedures from the completed MSI benchmark.

No optimization is rerun; the archived experiment is read-only.
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

OUT = Path(__file__).resolve().parent
ROOT = OUT.parent / "mw_pls_fw_benchmark_2026-09-10"
SOURCE = ROOT / "reports_final_2026-09-11" / "summary.json"
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

def check_method(name, s, d, T, k=2):
    assert s["converged"]
    if name == "MW_line_search_identity":
        assert s["initialization"] == "identity" and s["step_rule"] == "line_search"
        assert s["tol_factor"] == 1 and s["epsilon_Q"] == min(1, d / T)
        assert s["gap"] <= s["epsilon_Q"] and s["full_extreme_checks"] >= 1
    elif name == "OMD_stat" and 2**k == d:
        assert s["solver"] == "exact_global_forward" and s["eta"] == 0
        assert s["iterations"] == 0
    elif name == "OMD_stat":
        tol = min(1, np.sqrt(d / T))
        assert s["original_gap_tolerance"] == tol
        assert s["regularized_gap_tolerance"] == tol
        assert s["gap"] <= tol and s["regularized_gap"] <= tol

# Recheck the selected data and solver identities, including discarded warm-ups.
raw = {}
for ci in IDS:
    phase = "main_100_phase_a" if ci in {7, 8, 2, 5, 6, 9} else "main_100_phase_b"
    records = []
    for rep in range(100):
        r = json.loads((ROOT / phase / f"case_{ci:02d}" / f"rep_{rep:02d}" / "summary.json").read_text())
        ref = stats[(ci, "PLS")]
        assert (r["case_index"], r["rep"], r["true_rank"]) == (ci, rep, 8)
        assert all(r[key] == ref[key] for key in ["n", "k", "d", "T"])
        for name in METHODS:
            m = r["methods"][name]
            assert m["status"] == "complete"
            warm = [v for v in r["warmups"] if v["method"] == name]
            timed = [v for v in r["measured"] if v["method"] == name]
            assert len(warm) == 1 and len(timed) == 3
            for v in warm + timed:
                check_method(name, v["stats"], r["d"], r["T"], r["k"])
            assert np.isclose(m["median_seconds"], np.median([v["stats"]["wall_seconds"] for v in timed]), rtol=0, atol=1e-12)
        records.append(r)
    raw[ci] = records

boot = np.random.default_rng(20260919).integers(100, size=(10000, 100))
for r in rows:
    assert r["repetitions"] == 100 and r["timing_repeats"] == 3
    ms = [v["methods"][r["method"]] for v in raw[r["case_index"]]]
    errors = np.array([v["validation"]["trace_norm_error"] for v in ms])
    lo, hi = np.quantile(errors[boot].mean(1), [.025, .975])
    times = np.array([v["median_seconds"] for v in ms])
    expected = [errors.mean(), lo, hi, np.median(times), *np.quantile(times, [.25, .75])]
    fields = ["trace_norm_error", "trace_norm_error_ci_low", "trace_norm_error_ci_high", "seconds", "seconds_q25", "seconds_q75"]
    np.testing.assert_allclose([r[k] for k in fields], expected, rtol=0, atol=1e-12)

for r in mem:
    assert r["profiles"] == 100
    values = []
    ci = {4: 7, 6: 8, 8: 2, 10: 9}[r["n"]]
    for rep in range(100):
        path = ROOT / "main_100_phase_a_memory" / f"n{r['n']}_{r['method']}_rep{rep:03d}.json"
        v = json.loads(path.read_text())
        assert v["status"] == "complete" and v["input_sha256"] == raw[ci][rep]["input_sha256"]
        check_method(r["method"], v["stats"], r["d"], 64 * r["d"])
        values.append(v["peak_process_MiB"])
    np.testing.assert_allclose([r[k] for k in ["median_MiB", "q25_MiB", "q75_MiB"]],
                               [np.median(values), *np.quantile(values, [.25, .75])], rtol=0, atol=1e-12)

plt.rcParams.update({"font.family": "DejaVu Sans", "font.size": 11,
                     "axes.spines.top": False, "axes.spines.right": False,
                     "axes.labelcolor": "#263442", "text.color": "#263442",
                     "axes.titleweight": "semibold", "svg.fonttype": "none"})

def canvas(title, subtitle):
    fig, axes = plt.subplots(1, 2, figsize=(13.2, 6.7))
    fig.subplots_adjust(left=.075, right=.98, bottom=.26, top=.72, wspace=.27)
    fig.suptitle(title, fontsize=18, fontweight="semibold", y=.965)
    fig.text(.5, .89, subtitle, ha="center", fontsize=11.5)
    handles = [Line2D([], [], color=c, marker=m, lw=2, ms=6, label=l)
               for c, m, l in zip(COLORS, MARKERS, LABELS)]
    fig.legend(handles=handles, loc="upper center", bbox_to_anchor=(.5, .855), ncol=3, frameon=False, fontsize=11)
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
    footer = (uncertainty + "\n"
              r"MW-PLS: line-search Frank–Wolfe, initialized at $I_d/d$.  OMD gap $\leq\min\{1,\sqrt{d/T}\}$; MW gap $\leq\min\{1,d/T\}$." + "\n"
              "Stopping gaps concern different objectives. Four allocated CPU cores; initialization is included in solver time.")
    if note:
        footer += "\n" + note
    fig.text(.5, .055, footer, ha="center", va="bottom", fontsize=9.2, linespacing=1.65)
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

ks = [2, 4, 8]
fig, axes = canvas("Accuracy and runtime as block size changes",
                   r"$n=8$ qubits  ·  $d=256$  ·  $T=16{,}384$  ·  same rank-eight state  ·  100 paired datasets per point")
curves(axes[0], ks, K_IDS, "trace_norm_error", "trace_norm_error_ci_low", "trace_norm_error_ci_high")
curves(axes[1], ks, K_IDS, "seconds", "seconds_q25", "seconds_q75")
axes[0].set_title("(a) Reconstruction error", loc="left", fontsize=12)
axes[0].set_ylabel(r"Mean trace-norm error $\|\widehat\rho-\rho\|_{\rm tr}$")
axes[0].set_ylim(0, 2)
axes[1].set_title("(b) Solver runtime", loc="left", fontsize=12)
axes[1].set_ylabel("Median solver time (seconds)")
axes[1].set_yscale("log")
for ax in axes:
    ax.set_xticks(ks, ["2", "4", "8 (global)"])
    ax.set_xlabel(r"Block size $k$")
save(fig, "vary_block_size_three",
     "Shading: pointwise 95% bootstrap intervals for mean error; IQR of per-dataset median runtimes from three fresh timed solves.",
     "At k=n=8, PLS/OMD use the shared exact solution (also minimizing MW); MW-PLS reports the generic iterative route.")

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

selected = dict(status="passed", source=str(SOURCE), source_sha256=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                methods=METHODS, rows=rows, memory=mem)
(OUT / "selected_summary.json").write_text(json.dumps(selected, indent=2) + "\n")
with (OUT / "selected_summary.csv").open("w", newline="") as f:
    keys = list(dict.fromkeys(k for r in rows for k in r))
    writer = csv.DictWriter(f, fieldnames=keys)
    writer.writeheader()
    writer.writerows(rows)
audit = dict(status="passed", paired_datasets_checked=1000, selected_procedures=METHODS,
             warmups_checked=3000, timed_solves_checked=9000, memory_profiles_checked=1200,
             bootstrap_mean_intervals_reproduced=True, medians_and_IQRs_reproduced=True,
             mw_initialization="identity I_d/d", mw_step="line_search", mw_gap="min(1,d/T)",
             omd_original_and_regularized_gap="min(1,sqrt(d/T))", source_sha256=selected["source_sha256"],
             global_case="PLS/OMD share the analytic solution; MW-FW retains its generic identity-start iterative route.",
             scope="Read stored records and regenerate selected summaries/plots; no optimization replay or new simulation.")
(OUT / "validation.json").write_text(json.dumps(audit, indent=2) + "\n")
print(json.dumps(audit, indent=2))
