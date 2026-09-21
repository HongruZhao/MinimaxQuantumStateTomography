import TomographyOracleCore.HardReferenceState

namespace TomographyOracleCore

open MatrixReduction
open scoped BigOperators ComplexOrder

/-!
# Pointwise lower bound for the common reference Born density

The comparison state used by the lower information argument is diagonal in
the canonical head/tail basis.  This file records that diagonal form and
proves that its Born weight against every trace-one positive effect is at
least the uniform tail eigenvalue `b / k`.
-/

/-- Eigenvalue of the common reference state in head/tail block coordinates. -/
noncomputable def hardReferenceBlockWeight (k : ℕ) (b : ℝ) :
    Fin 2 ⊕ Fin k → ℝ :=
  Sum.elim (fun _ ↦ hardSpectrumHead b) (fun _ ↦ b / (k : ℝ))

/-- The common reference block matrix is literally diagonal. -/
theorem hardReferenceBlockMatrix_eq_diagonal (k : ℕ) (b : ℝ) :
    hardReferenceBlockMatrix k b =
      Matrix.diagonal (fun i ↦ (hardReferenceBlockWeight k b i : ℂ)) := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · by_cases hij : i = j <;>
        simp [hardReferenceBlockMatrix, hardProjectorHeadBlock,
          hardReferenceTailBlock, hardReferenceBlockWeight, hij]
    · simp [hardReferenceBlockMatrix, hardProjectorHeadBlock,
        hardReferenceTailBlock, hardReferenceBlockWeight]
  · rcases j with j | j
    · simp [hardReferenceBlockMatrix, hardProjectorHeadBlock,
        hardReferenceTailBlock, hardReferenceBlockWeight]
    · by_cases hij : i = j <;>
        simp [hardReferenceBlockMatrix, hardProjectorHeadBlock,
          hardReferenceTailBlock, hardReferenceBlockWeight, hij]

/-- Eigenvalue of the common reference state after reindexing to `Fin (k+2)`. -/
noncomputable def hardReferenceWeight (k : ℕ) (b : ℝ) :
    Fin (k + 2) → ℝ :=
  fun i ↦ hardReferenceBlockWeight k b ((hardProjectorBlockEquiv k).symm i)

/-- The ambient common reference matrix is diagonal in the reindexed basis. -/
theorem hardReferenceMatrix_eq_diagonal (k : ℕ) (b : ℝ) :
    hardReferenceMatrix k b =
      Matrix.diagonal (fun i ↦ (hardReferenceWeight k b i : ℂ)) := by
  ext i j
  simp only [hardReferenceMatrix, Matrix.reindex_apply,
    hardReferenceBlockMatrix_eq_diagonal, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst j
    simp [hardReferenceWeight]
  · have hpre : (hardProjectorBlockEquiv k).symm i ≠
        (hardProjectorBlockEquiv k).symm j := by
      exact fun h ↦ hij ((hardProjectorBlockEquiv k).symm.injective h)
    simp [hij, hpre]

/-- Every eigenvalue of the common reference state dominates `b / k`. -/
theorem hardReferenceWeight_tail_lower
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) (i : Fin (k + 2)) :
    b / (k : ℝ) ≤ hardReferenceWeight k b i := by
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hbdiv : b / (k : ℝ) ≤ b := div_le_self hb0 hkR
  unfold hardReferenceWeight hardReferenceBlockWeight
  generalize hi : (hardProjectorBlockEquiv k).symm i = q
  rcases q with q | q
  · simp only [Sum.elim_inl]
    unfold hardSpectrumHead
    linarith
  · simp

/-- Real trace of a diagonal matrix times an arbitrary matrix. -/
theorem trace_diagonal_mul_re
    {n : Type*} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (E : Matrix n n ℂ) :
    (Matrix.trace (Matrix.diagonal (fun i ↦ (w i : ℂ)) * E)).re =
      ∑ i, w i * (E i i).re := by
  simp [Matrix.trace]

/-- Diagonal entries of a complex positive-semidefinite matrix have
nonnegative real part. -/
theorem posSemidef_diag_re_nonnegative
    {n : Type*} [Fintype n] [DecidableEq n]
    {E : Matrix n n ℂ} (hE : E.PosSemidef) (i : n) :
    0 ≤ (E i i).re := by
  have hi := hE.diag_nonneg (i := i)
  exact (Complex.nonneg_iff.mp hi).1

/-- A real diagonal weight bounded below by `lambda` has trace pairing at
least `lambda` against every trace-one positive effect. -/
theorem le_trace_diagonal_mul_re_of_posSemidef_trace_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (w : n → ℝ) (lambda : ℝ) (E : Matrix n n ℂ)
    (hw : ∀ i, lambda ≤ w i)
    (hE : E.PosSemidef) (htrace : E.trace = 1) :
    lambda ≤
      (Matrix.trace (Matrix.diagonal (fun i ↦ (w i : ℂ)) * E)).re := by
  have htraceRe : (∑ i, (E i i).re) = 1 := by
    have h := congrArg Complex.re htrace
    simpa [Matrix.trace] using h
  rw [trace_diagonal_mul_re]
  calc
    lambda = lambda * (∑ i, (E i i).re) := by rw [htraceRe, mul_one]
    _ = ∑ i, lambda * (E i i).re := by rw [Finset.mul_sum]
    _ ≤ ∑ i, w i * (E i i).re := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hw i)
        (posSemidef_diag_re_nonnegative hE i)

/-- The reference Born weight is pointwise at least its uniform tail
eigenvalue. -/
theorem hardReferenceMatrix_born_re_tail_lower
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)
    (hE : E.PosSemidef) (htrace : E.trace = 1) :
    b / (k : ℝ) ≤ (Matrix.trace (hardReferenceMatrix k b * E)).re := by
  rw [hardReferenceMatrix_eq_diagonal]
  exact le_trace_diagonal_mul_re_of_posSemidef_trace_one
    (hardReferenceWeight k b) (b / (k : ℝ)) E
    (hardReferenceWeight_tail_lower k b hk hb0 hbquarter) hE htrace

end TomographyOracleCore
