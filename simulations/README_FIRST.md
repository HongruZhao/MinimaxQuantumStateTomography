# Code for all published simulations

Start with `PAPER_SIMULATION_CODE_MAP.csv` and `MSI_CHECKLIST.md`.

- `msi_code/`: unchanged source/job/dependency files freshly checked and
  exported from the seven MSI run folders used by the paper and supplement.
  Historical routines reproduce their historical runs; the active current
  implementation is under `estimator_review_fix_2026-09-20/src/`.
- `current_local/`: the current implementation, sampling pool, configurations,
  regression fixtures, and the already-local supplemental study. The core
  Python files are byte-identical to the live active MSI deployment.
- `publication_plotting/`: portable code and matched summary inputs for all
  four published simulation comparisons. The global endpoint uses the shared
  spectral rerun. The compact main-paper layout is explicit in this renderer.
- `metadata/`: fresh source/hash checks and aggregate recorded-run receipts.

## Regenerate the four figure comparisons

With NumPy, Matplotlib, and Pillow installed:

```sh
python3 publication_plotting/REPRODUCE_FIGURES.py
```

Outputs go to `publication_plotting/generated/`; the manuscripts are not
overwritten. This uses stored summaries; it does not rerun estimators or
bootstrap the original datasets. The full original MSI plotting/validation
scripts are preserved in `msi_code/` and require their recorded MSI data tree.
The main publication PNG metadata records Matplotlib 3.11.1; the supplement
PNG exports used 3.9.4. Numeric curves are reproducible across these versions;
identical font rendering is a stricter environment-dependent requirement.

## Check the current implementation

Read `current_local/README.md`, then run its documented regression, solver,
and saved-study checks. The release reran all 36 regression checks and the saved-study
validator successfully. It also regenerated all four figure comparisons. The pinned simulation environment uses NumPy
1.23.5 and SciPy 1.10.0. Larger-block original sampling additionally requires
Stim 1.15.0. Plotting/report tools also use Matplotlib, Pillow, pypdf, and
reportlab, as listed in the archived requirements.

## MSI reruns

The archived job scripts retain the account, partition, paths, and environment
used by their original runs. Check current availability before submitting them.
Use a new run directory and preserve the source/configuration hashes; do not
overwrite completed scientific records. Substantial computation belongs in
Slurm allocations, not on a login node.

The original large timing inputs and arrays remain on MSI and are not copied
into this source bundle. Exact larger-block observation replay requires saved
draws or empirical means because NumPy seeds alone do not fix Stim tableaux.
Packaging did not submit cluster jobs or rerun the historical timing benchmarks.
Local numerical checks and figure regeneration were rerun for this release.
