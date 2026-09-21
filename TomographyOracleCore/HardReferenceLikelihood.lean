import TomographyOracleCore.HardReferenceState

namespace TomographyOracleCore

open MatrixReduction
open scoped ComplexOrder

/-!
# Exact hard-state perturbation around the common reference

This module identifies the projector hard state minus its common full-rank
reference as the centered projector perturbation used by the one-copy
information calculation.  All statements are finite-dimensional matrix
identities; no probabilistic or information-theoretic premise is introduced.
-/

/-- On the tail block, the hard state differs from the uniform reference by
exactly `b` times the centered rank-`m` projector. -/
theorem hardProjectorTailBlock_sub_hardReferenceTailBlock {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    hardProjectorTailBlock P b - hardReferenceTailBlock k b =
      b • centeredProjectorTail P := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hardProjectorTailBlock, hardReferenceTailBlock,
      centeredProjectorTail, div_eq_mul_inv]
    ring
  · simp [hardProjectorTailBlock, hardReferenceTailBlock,
      centeredProjectorTail, hij, div_eq_mul_inv]
    ring

/-- In head/tail coordinates, the two hard and reference states have identical
head blocks and differ only by the centered tail perturbation. -/
theorem hardProjectorBlockMatrix_sub_hardReferenceBlockMatrix {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    hardProjectorBlockMatrix P b - hardReferenceBlockMatrix k b =
      Matrix.fromBlocks 0 0 0 (b • centeredProjectorTail P) := by
  ext i j
  cases i with
  | inl i =>
      cases j <;>
        simp [hardProjectorBlockMatrix, hardReferenceBlockMatrix]
  | inr i =>
      cases j with
      | inl j =>
          simp [hardProjectorBlockMatrix, hardReferenceBlockMatrix]
      | inr j =>
          have h := congrArg (fun M ↦ M i j)
            (hardProjectorTailBlock_sub_hardReferenceTailBlock P b)
          simpa [hardProjectorBlockMatrix, hardReferenceBlockMatrix] using h

/-- After the canonical reindexing to `Fin (k+2)`, the full hard/reference
difference is still the reindexed centered tail perturbation. -/
theorem hardProjectorMatrix_sub_hardReferenceMatrix {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    hardProjectorMatrix P b - hardReferenceMatrix k b =
      Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
        (Matrix.fromBlocks 0 0 0 (b • centeredProjectorTail P)) := by
  ext i j
  simp only [hardProjectorMatrix, hardReferenceMatrix, Matrix.sub_apply,
    Matrix.reindex_apply]
  have hblock := congrArg (fun M ↦
      M ((hardProjectorBlockEquiv k).symm i)
        ((hardProjectorBlockEquiv k).symm j))
    (hardProjectorBlockMatrix_sub_hardReferenceBlockMatrix P b)
  simpa only [Matrix.sub_apply, Matrix.submatrix_apply] using hblock

/-- The centered tail perturbation embedded into the manuscript ambient
coordinates, before multiplying by its scalar mass `b`. -/
noncomputable def embeddedCenteredProjectorTail {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
    (Matrix.fromBlocks 0 0 0 (centeredProjectorTail P))

/-- Equivalent scalar-multiple form of the full perturbation identity. -/
theorem hardProjectorMatrix_sub_hardReferenceMatrix_eq_smul {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    hardProjectorMatrix P b - hardReferenceMatrix k b =
      b • embeddedCenteredProjectorTail P := by
  rw [hardProjectorMatrix_sub_hardReferenceMatrix P b]
  have hblock :
      Matrix.fromBlocks 0 0 0 (b • centeredProjectorTail P) =
        b • (Matrix.fromBlocks 0 0 0 (centeredProjectorTail P) :
          Matrix (Fin 2 ⊕ Fin k) (Fin 2 ⊕ Fin k) ℂ) := by
    ext i j
    cases i <;> cases j <;> simp
  rw [hblock]
  ext i j
  simp [embeddedCenteredProjectorTail, Matrix.reindex_apply]

/-- Density-operator form of the exact hard/reference perturbation identity. -/
theorem hardProjectorDensityOperator_sub_hardReferenceDensityOperator
    {k m : ℕ} (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (hardProjectorDensityOperator P b hm hb0 hbquarter).matrix -
        (hardReferenceDensityOperator k b hk hb0 hbquarter).matrix =
      Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
        (Matrix.fromBlocks 0 0 0 (b • centeredProjectorTail P)) := by
  exact hardProjectorMatrix_sub_hardReferenceMatrix P b

/-- Density-operator form with the scalar mass factored outside the embedded
centered projector. -/
theorem hardProjectorDensityOperator_sub_hardReferenceDensityOperator_eq_smul
    {k m : ℕ} (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (hardProjectorDensityOperator P b hm hb0 hbquarter).matrix -
        (hardReferenceDensityOperator k b hk hb0 hbquarter).matrix =
      b • embeddedCenteredProjectorTail P := by
  exact hardProjectorMatrix_sub_hardReferenceMatrix_eq_smul P b

/-- Against an arbitrary effect matrix, the complex trace difference is the
mass `b` times the trace pairing with the embedded centered projector. -/
theorem trace_hardProjector_mul_sub_trace_hardReference_mul {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (effect : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
    (hardProjectorMatrix P b * effect).trace -
        (hardReferenceMatrix k b * effect).trace =
      b • (embeddedCenteredProjectorTail P * effect).trace := by
  calc
    (hardProjectorMatrix P b * effect).trace -
          (hardReferenceMatrix k b * effect).trace =
        ((hardProjectorMatrix P b - hardReferenceMatrix k b) * effect).trace := by
          rw [sub_mul, Matrix.trace_sub]
    _ = ((b • embeddedCenteredProjectorTail P) * effect).trace := by
      rw [hardProjectorMatrix_sub_hardReferenceMatrix_eq_smul P b]
    _ = b • (embeddedCenteredProjectorTail P * effect).trace := by
      rw [Matrix.smul_mul, Matrix.trace_smul]

/-- Real Born-trace form of the same identity.  This is the exact scalar
inside `ENNReal.ofReal` in the dominated-POVM Born density; no positivity or
truncation inequality is needed for this algebraic difference. -/
theorem bornTrace_hardProjector_sub_hardReference {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (effect : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
    (hardProjectorMatrix P b * effect).trace.re -
        (hardReferenceMatrix k b * effect).trace.re =
      b * (embeddedCenteredProjectorTail P * effect).trace.re := by
  have h := congrArg Complex.re
    (trace_hardProjector_mul_sub_trace_hardReference_mul P b effect)
  simpa using h

end TomographyOracleCore
