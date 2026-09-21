import TomographyOracleCore.HardProjectorState

namespace TomographyOracleCore

open MatrixReduction
open scoped ComplexOrder

/-!
# Reference state and centered projector perturbation

The lower information argument compares every rank-`m` hard state with the
same full-rank reference state.  This file constructs that state as a genuine
density operator and proves the exact trace and trace-square identities of
the centered tail perturbation.
-/

/-- Uniform tail block carrying total mass `b` on `k` coordinates. -/
noncomputable def hardReferenceTailBlock (k : ℕ) (b : ℝ) :
    Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal fun _ ↦ (b / (k : ℝ) : ℂ)

/-- Head/tail block form of the common reference state. -/
noncomputable def hardReferenceBlockMatrix (k : ℕ) (b : ℝ) :
    Matrix (Fin 2 ⊕ Fin k) (Fin 2 ⊕ Fin k) ℂ :=
  Matrix.fromBlocks (hardProjectorHeadBlock b) 0 0
    (hardReferenceTailBlock k b)

/-- Common reference matrix on the manuscript ambient space. -/
noncomputable def hardReferenceMatrix (k : ℕ) (b : ℝ) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
    (hardReferenceBlockMatrix k b)

theorem hardReferenceTailBlock_posSemidef
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b) :
    (hardReferenceTailBlock k b).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℂ) ≤ (b / (k : ℝ) : ℂ)
  rw [Complex.nonneg_iff]
  constructor
  · simpa using div_nonneg hb0 (Nat.cast_nonneg k)
  · simp

theorem hardReferenceBlockMatrix_isHermitian
    (k : ℕ) (b : ℝ) :
    (hardReferenceBlockMatrix k b).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact isSelfAdjoint_iff.mpr (by simp)
  · simp
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact isSelfAdjoint_iff.mpr (by simp)

theorem hardReferenceBlockMatrix_posSemidef
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (hardReferenceBlockMatrix k b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hardReferenceBlockMatrix_isHermitian k b)
  intro x
  have hstar : star x = Sum.elim (star (x ∘ Sum.inl))
      (star (x ∘ Sum.inr)) := by
    funext i
    cases i <;> simp
  rw [hardReferenceBlockMatrix, Matrix.fromBlocks_mulVec, hstar,
    sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, Pi.zero_apply, add_zero, zero_add]
  exact add_nonneg
    ((hardProjectorHeadBlock_posSemidef b hbquarter).dotProduct_mulVec_nonneg
      (x ∘ Sum.inl))
    ((hardReferenceTailBlock_posSemidef k b hb0).dotProduct_mulVec_nonneg
      (x ∘ Sum.inr))

theorem hardReferenceMatrix_posSemidef
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (hardReferenceMatrix k b).PosSemidef := by
  rw [hardReferenceMatrix, Matrix.reindex_apply]
  exact (hardReferenceBlockMatrix_posSemidef k b hb0 hbquarter).submatrix
    (hardProjectorBlockEquiv k).symm

theorem hardReferenceTailBlock_trace_eq
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k) :
    (hardReferenceTailBlock k b).trace = (b : ℂ) := by
  rw [hardReferenceTailBlock, Matrix.trace_diagonal]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  push_cast
  apply Complex.ext <;> simp [hk0]
  field_simp

theorem hardReferenceBlockMatrix_trace_eq_one
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k) :
    (hardReferenceBlockMatrix k b).trace = 1 := by
  unfold Matrix.trace hardReferenceBlockMatrix
  rw [Fintype.sum_sum_type]
  change (hardProjectorHeadBlock b).trace +
      (hardReferenceTailBlock k b).trace = 1
  rw [hardProjectorHeadBlock, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two]
  rw [hardReferenceTailBlock_trace_eq k b hk]
  unfold hardSpectrumHead
  apply Complex.ext <;> simp

theorem hardReferenceMatrix_trace_eq_one
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k) :
    (hardReferenceMatrix k b).trace = 1 := by
  rw [hardReferenceMatrix, matrix_trace_reindex_self,
    hardReferenceBlockMatrix_trace_eq_one k b hk]

/-- The common comparison state is a genuine density operator. -/
noncomputable def hardReferenceDensityOperator
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    DensityOperator (Fin (k + 2)) where
  matrix := hardReferenceMatrix k b
  posSemidef := hardReferenceMatrix_posSemidef k b hb0 hbquarter
  trace_eq_one := hardReferenceMatrix_trace_eq_one k b hk

/-- Centered rank-`m` projector on the `k`-dimensional tail. -/
noncomputable def centeredProjectorTail {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    Matrix (Fin k) (Fin k) ℂ :=
  ((m : ℝ)⁻¹) • P.matrix - ((k : ℝ)⁻¹) • (1 : Matrix (Fin k) (Fin k) ℂ)

theorem centeredProjectorTail_isHermitian {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    (centeredProjectorTail P).IsHermitian := by
  apply (P.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).sub
  exact Matrix.isHermitian_one.smul (isSelfAdjoint_iff.mpr (by simp))

/-- The centered projector has zero trace. -/
theorem centeredProjectorTail_trace_eq_zero {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m)
    (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (centeredProjectorTail P).trace = 0 := by
  rw [centeredProjectorTail, Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, rankMOrthogonalProjector_trace_eq_rank P,
    Matrix.trace_one]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  push_cast
  apply Complex.ext <;> simp [hm0, hk0]

/-- Exact Hilbert--Schmidt energy of the centered projector. -/
theorem centeredProjectorTail_trace_mul_self {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m)
    (hm : 1 ≤ m) (hk : 1 ≤ k) :
    (centeredProjectorTail P * centeredProjectorTail P).trace =
      ((1 / (m : ℝ) - 1 / (k : ℝ) : ℝ) : ℂ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  rw [centeredProjectorTail]
  simp only [sub_mul, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, one_mul, mul_one]
  rw [P.isIdempotent]
  rw [Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
    Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul,
    rankMOrthogonalProjector_trace_eq_rank P, Matrix.trace_one]
  push_cast
  apply Complex.ext <;> simp [hm0, hk0]
  field_simp

end TomographyOracleCore
