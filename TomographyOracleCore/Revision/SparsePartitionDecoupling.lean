import TomographyOracleCore.Revision.BernoulliVectorMoments
import TomographyOracleCore.Revision.BernoulliSmallBall
import TomographyOracleCore.Revision.SparseSampleSuprema

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparsePartitionDecoupling

open FiniteProbabilityAverage BernoulliFiniteAverage BernoulliVectorMoments BernoulliSmallBall
open SparseCoefficientGeometry SparseSampleSuprema
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def fairLaw (N : ℕ) : Law (Fin N → Bool) := bernoulliLaw (1 / 2) (by constructor <;> norm_num) N

theorem selectedVectorSum_synthesis {N : ℕ} (X : Fin N → E) (y : Fin N → ℝ) (omega : Fin N → Bool) :
    selectedVectorSum (fun i => y i • X i) omega = synthesis X (restrict (selectedIndices omega) y) := by
  simp only [selectedVectorSum, synthesis]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : omega i <;> simp [selectedIndices, restrict, bitValue, h]

theorem full_sub_selectedVectorSum {N : ℕ} (X : Fin N → E) (y : Fin N → ℝ) (omega : Fin N → Bool) :
    (∑ i, y i • X i) - selectedVectorSum (fun i => y i • X i) omega =
      synthesis X (restrict (selectedIndices omega)ᶜ y) := by
  rw [selectedVectorSum_synthesis]
  change synthesis X y - _ = _
  rw [← synthesis_restrict_add_compl X y (selectedIndices omega)]
  abel

def averageCrossNorm {N : ℕ} (X : Fin N → E) (k : ℕ) : ℝ :=
  average (fairLaw N) (fun omega => crossNorm X k (selectedIndices omega))

theorem averageCrossNorm_nonneg {N : ℕ} (X : Fin N → E) (k : ℕ) : 0 ≤ averageCrossNorm X k :=
  average_nonneg _ (fun _ => crossNorm_nonneg _ _ _)

theorem norm_sq_le_diagonal_add_average_cross {N k : ℕ} (X : Fin N → E) (y : Fin N → ℝ)
    (hy : Admissible k Finset.univ y) :
    ‖synthesis X y‖ ^ 2 ≤ (∑ i, ‖y i • X i‖ ^ 2) + 4 * averageCrossNorm X k := by
  have hmean := average_selected_complement_inner (1 / 2) (by constructor <;> norm_num)
    (fun i => y i • X i)
  have hbound : average (fairLaw N) (fun omega =>
      ⟪selectedVectorSum (fun i => y i • X i) omega,
        (∑ i, y i • X i) - selectedVectorSum (fun i => y i • X i) omega⟫_ℝ) ≤
      averageCrossNorm X k := by
    apply average_mono
    intro omega
    rw [full_sub_selectedVectorSum, selectedVectorSum_synthesis]
    have hys := hy.restrict (selectedIndices omega)
    have hyc := hy.restrict (selectedIndices omega)ᶜ
    have hleft : Admissible k (selectedIndices omega) (restrict (selectedIndices omega) y) :=
      ⟨hys.1, hys.2.1, supported_restrict _ _⟩
    have hright : Admissible k (selectedIndices omega)ᶜ (restrict (selectedIndices omega)ᶜ y) :=
      ⟨hyc.1, hyc.2.1, supported_restrict _ _⟩
    exact (le_abs_self _).trans (abs_inner_le_crossNorm hleft hright)
  change average (fairLaw N) _ = (1 / 2 : ℝ) * (1 - 1 / 2) *
    (‖synthesis X y‖ ^ 2 - ∑ i, ‖y i • X i‖ ^ 2) at hmean
  nlinarith

/-- Averaging over every finite Bernoulli partition recovers the sparse energy.
Only the diagonal fixed-norm bound and the cross norms remain. -/
theorem sparseNorm_sq_le_diagonal_add_average_cross {N : ℕ} (X : Fin N → E) (k : ℕ)
    {q : ℝ} (hq : 0 ≤ q) (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q) :
    sparseNorm X k ^ 2 ≤ q + 4 * averageCrossNorm X k := by
  have hB : 0 ≤ q + 4 * averageCrossNorm X k := by
    nlinarith [averageCrossNorm_nonneg X k]
  have hnorm : sparseNorm X k ≤ Real.sqrt (q + 4 * averageCrossNorm X k) := by
    apply sparseNorm_le
    intro y hy
    have hdiag : (∑ i, ‖y i • X i‖ ^ 2) ≤ q := by
      calc
        _ = ∑ i, y i ^ 2 * ‖X i‖ ^ 2 := by simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
        _ ≤ ∑ i, y i ^ 2 * q := Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hfixed i) (sq_nonneg _))
        _ = coefficientNorm y ^ 2 * q := by rw [← Finset.sum_mul, coefficientNorm_sq]
        _ ≤ q := by
          have hc : coefficientNorm y ^ 2 ≤ 1 := by nlinarith [hy.1, coefficientNorm_nonneg y]
          simpa using mul_le_mul_of_nonneg_right hc hq
    have hsq : ‖synthesis X y‖ ^ 2 ≤ q + 4 * averageCrossNorm X k := by
      linarith [norm_sq_le_diagonal_add_average_cross X y hy]
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt hB]
    exact hsq
  have hs := (sq_le_sq₀ (sparseNorm_nonneg X k) (Real.sqrt_nonneg _)).mpr hnorm
  simpa only [Real.sq_sqrt hB] using hs

end
end TomographyOracleCore.Revision.SparsePartitionDecoupling
