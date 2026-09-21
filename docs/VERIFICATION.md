# Verification scope

The public entry point exposes six declarations implementing Theorem 3 and
Corollary 4 for OMD and measurement weighted PLS. Their dependency closure
contains 504 supporting Lean modules; none imports the supplement's storage
axiom. All proof sources are unchanged from the complete September 20 development.

The release was checked with Lean 4.33.0-rc2 and the exact dependency revisions
in `lake-manifest.json`. All 958 sources of the complete development, including
the new main entry point, were compiled from empty project object directories.
Only the pinned third-party dependency cache was reused. Each focused source
is matched by SHA-256 to its successful full-build record in this release.

`verification/MainAxiomAudit.lean` traverses the six main declarations'
transitive axiom dependencies. It rejects every axiom except `propext`,
`Classical.choice`, and `Quot.sound`, and exports their complete Lean types.
`verification/MAIN_ENDPOINTS.json` is the release output; reruns write to
`verification/rerun/main_endpoints.json`. The axiom audit preserves the stated
measurement, dimension, regularity, and approximate-fitting hypotheses.

The accompanying source scan rejects `sorry`, `admit`, `sorryAx`, and
`native_decide`, ignoring comments and strings. It also records explicit
project axiom declarations. The focused closure has none.

The full Zenodo archive includes all main-paper and supplement proof sources,
an export of every project declaration and its type and axioms, and the
statement correspondence tables. There is exactly one additional axiom in that
full archive: a uniform quadratic bound for storage used by the exact dense
Hermitian spectral primitive. Only the storage conclusions for Lemma S.7 and
Proposition S.14 depend on it. Its exact Lean declaration and mathematical
translation are recorded there.

Correspondence between manuscript text and Lean declarations is a reviewed
statement map. Lean checks the formal declarations and proofs, not a translation
of the PDF. Different proof routes and component identities are identified in
the full archive's crosswalk. Python experiment validation is reported separately.
