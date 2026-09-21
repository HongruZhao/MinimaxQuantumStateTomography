# Python simulations and reconstruction

`src/estimators.py` is the current common interface for PLS, OMD, and MW-PLS.
At k=n all three use `src/global_solution.py`. The exact 11,520-element
two-qubit Clifford sampling pool is included as `src/clifford_representatives.npz`.
All seventeen current files in `src/` are unchanged from the canonical code.

Use Python 3.10 for the production environment pinned in
`requirements-simulation.txt` (NumPy 1.23.5, SciPy 1.10.0). The analysis
requirements are listed separately. From this directory:

```sh
python -m pip install -r requirements-simulation.txt -r requirements-analysis.txt
python tests/review_regressions.py
python src/audit_solvers.py --output reports/local_solver_audit.json
python analysis/validate_saved_study.py
python analysis/plot_supplement_final.py
```

The first two checks test implementation behavior; they are numerical tests,
not Lean proofs or rigorous floating-point certificates. The saved-study check
validates source/input/output identities and recomputes numerical diagnostics.
The final plot uses only the three paper-tolerance estimator profiles and writes
the supplemental figure into its local figures directory. Accuracy-stress records
are retained as reproducibility inputs but are not plotted in the manuscripts.
The small original OMD implementation and stored fixture are needed only by
the regression test; they are not the current estimator.

New datasets can be generated with `src/run_convergence.py CONFIG TASK`, with
zero-based task index and any included convergence configuration. To rerun a
study, copy its configuration and give it a new `name`, since completed results
are intentionally not overwritten. The supplemental study uses
`analysis/run_review_simulation.py configs/review_fresh.json TASK`, TASK 0–14;
the saved runs are included. `analysis/refine_failed_accuracy.py` documents the
additional accuracy-stress computation used by the saved-study validator.

The legacy 100-repetition main-paper timing inputs are not included in this
source archive. `src/existing.py` and `src/run_global_benchmark.py` retain their
original MSI data paths and require that external dataset for an exact rerun.
The required publication figures are included in LaTeX. This archive does not
claim that every historical timing experiment can run offline from these files.
No remote cluster job is submitted by the build or verification instructions.
