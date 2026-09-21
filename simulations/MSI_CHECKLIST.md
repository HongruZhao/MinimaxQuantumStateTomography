# MSI source and recorded-run checklist

Read-only check: 20 September 2026. No new Slurm jobs were submitted.

- [x] Active deployment is `estimator_review_fix_2026-09-20` through
  `current_three_estimators`.
- [x] Downloaded and hashed 125 source/job/dependency files from the seven
  identified publication run folders; 91 are Python files.
- [x] Parsed all 91 exported Python files successfully.
- [x] All 16 active Python modules match the current local implementation.
- [x] The finite Clifford pool and four current configurations match MSI hashes.
- [x] Original records contain 1000 paired datasets, 3000 selected warmups,
  9000 selected timed solves, and 1200 selected memory profiles.
- [x] Recorded stopping fields checked separately; see
  `metadata/recorded_stopping_checks.json` for counts and exact scope.
- [x] All 100 global rerun records are complete, with maximum pairwise
  estimator-output difference zero.
- [x] All 180 paper-tolerance supplement fits are recorded as accepted, and
  their recorded source hashes match the current deployment.
- [x] The five publication summary tables match MSI hashes exactly.
- [x] The final block-comparison PNG matches MSI exactly.
- [x] Two main PNGs are compact local publication exports, not byte-identical
  to the taller MSI images. Their numerical table matches, and all twelve
  curve paths are reproduced exactly by the supplied publication renderer.
- [x] Both supplement PNGs reproduce pixel-for-pixel locally with Matplotlib
  3.9.4. Font/bitmap output may differ with other plotting versions.
- [x] Twenty numerical values printed in the manuscripts were checked against
  the matched tables; see `metadata/manuscript_numerical_values.csv`.

The source-only remote export includes no downloaded datasets or individual
run records. Existing local supplement inputs and regression fixtures are
included in `current_local/`, as in the earlier delivery. The separate tight
accuracy profile has an initial capped record and a completed extension;
the published supplemental plot uses only the 180 paper-tolerance fits.

This verifies source identity, metadata, recorded stopping fields, and figure
correspondence. It is not a fresh solve, a full saved-array revalidation of
the historical timing benchmark, or an interval-arithmetic certificate.
Original MSI paths in archived code are retained so its hashes remain exact.
