import TomographyOracleCore.Revision.SparseDyadicEnergy
import TomographyOracleCore.Revision.SparseNormSplitting

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.SparseUniformEnergy

open SparseCoefficientGeometry SparseSampleSuprema SparseDyadicScales SparseRecursionWeights
open SparseGoodPartitionBound SparseDyadicEnergy SparseBadPartitionFraction SparseNormSplitting
open SparsePartitionDecoupling SparseDeterministicRecurrence FiniteProbabilityAverage BernoulliSmallBall
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def uniformEnergyConstant : ℝ := 4 * energyConstant
theorem uniformEnergyConstant_ge_one : 1 ≤ uniformEnergyConstant := by
  norm_num [uniformEnergyConstant, energyConstant, crossConstant, recursionConstant]
theorem uniformEnergyConstant_ge_small : 4 * (size 0 : ℝ) ≤ uniformEnergyConstant := by
  norm_num [uniformEnergyConstant, energyConstant, crossConstant, recursionConstant, size, block]

theorem sparseNorm_sq_le_small_bound {N : ℕ} (X : Fin N → E) (k : ℕ)
    {M q : ℝ} (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M) (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q) :
    sparseNorm X k ^ 2 ≤ q + 4 * (k : ℝ) * M := by
  have h := sparseNorm_sq_le_diagonal_add_average_cross X k hq hfixed
  have hav : averageCrossNorm X k ≤ (k : ℝ) * M := by
    rw [← average_const (fairLaw N) ((k : ℝ) * M)]
    exact average_mono _ (fun omega => crossNorm_le_card_mul_pair_bound k (selectedIndices omega) hM hentry)
  nlinarith

/-- A simultaneous sparse-energy estimate at every support size. The event is
independent of the support and of the coefficient vector. -/
theorem sparseNorm_sq_le_uniform {N : ℕ} (X : Fin N → E)
    {kappa s M q : ℝ} (hkappa : 0 < kappa) (hs : 0 < s) (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M)
    (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q) (hgood : X ∉ globalFailure kappa s N)
    (k : ℕ) (hkN : k ≤ N) :
    sparseNorm X k ^ 2 ≤ uniformEnergyConstant *
      (q + amplification N * M + kappa ^ 2 * s * Real.sqrt ((N : ℝ) * k)) := by
  have ha : 0 ≤ amplification N := le_trans (by norm_num) (amplification_ge_one N)
  have hC : 0 ≤ uniformEnergyConstant := le_trans (by norm_num) uniformEnergyConstant_ge_one
  have hS : 0 ≤ kappa ^ 2 * s * Real.sqrt ((N : ℝ) * k) := by positivity
  by_cases hk : size 0 ≤ k
  · obtain ⟨j, hjk, hkj⟩ := exists_lower_dyadic_size hk
    have h1 := sparseNorm_le_two_mul hkj X
    have h2 := sparseNorm_sq_le_on_good_event X hkappa hs hM hq hentry hfixed hgood j (hjk.trans hkN)
    have hsquare := (sq_le_sq₀ (sparseNorm_nonneg X k)
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sparseNorm_nonneg X (size j)))).mpr h1
    have hroot : Real.sqrt ((N : ℝ) * size j) ≤ Real.sqrt ((N : ℝ) * k) :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (by exact_mod_cast hjk) (Nat.cast_nonneg N))
    have hrootmul := mul_le_mul_of_nonneg_left hroot
      (show 0 ≤ energyConstant * (kappa ^ 2 * s) by have := energyConstant_pos; positivity)
    unfold uniformEnergyConstant
    nlinarith
  · have hsmall := sparseNorm_sq_le_small_bound X k hM hq hentry hfixed
    have hkR : (k : ℝ) ≤ size 0 := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge hk))
    have hmamp := mul_le_mul_of_nonneg_right (amplification_ge_one N) hM
    have hkC : 4 * (k : ℝ) ≤ uniformEnergyConstant := by linarith [uniformEnergyConstant_ge_small]
    have hm1 := mul_le_mul_of_nonneg_left (show M ≤ amplification N * M by simpa using hmamp)
      (show 0 ≤ 4 * (k : ℝ) by positivity)
    have hm2 := mul_le_mul_of_nonneg_right hkC (mul_nonneg ha hM)
    have hqC := mul_le_mul_of_nonneg_right uniformEnergyConstant_ge_one hq
    have hSC := mul_nonneg hC hS
    nlinarith

end
end TomographyOracleCore.Revision.SparseUniformEnergy
