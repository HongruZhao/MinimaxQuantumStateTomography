import TomographyOracleCore.Revision.PairMomentIntegration
import TomographyOracleCore.Revision.IntegralSixthJensen
import TomographyOracleCore.Revision.SparseRecursionWeights
import TomographyOracleCore.Revision.SparseEntropyRate

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.MaximumPairMoments

open MeasureTheory PeriodicForwardCovariance MaximumPairInner PairMomentIntegration
open IntegralSixthJensen SparseRecursionWeights
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ae_sample_fixedNorm (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    ∀ᵐ X : ι → E ∂Measure.pi (fun _ : ι => mu), ∀ i, ‖X i‖ ^ 2 = q :=
  Filter.eventually_all.mpr (fun i =>
    (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => mu) (i := i)).eventually hfixed)

theorem integrable_pairValue_pow (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    (p : Option (ι × ι)) (k : ℕ) :
    Integrable (fun X : ι → E => pairValue X p ^ k) (Measure.pi (fun _ : ι => mu)) := by
  apply (integrable_const (q ^ k)).mono' ((continuous_pairValue p).pow k).aestronglyMeasurable
  filter_upwards [ae_sample_fixedNorm hfixed] with X hX
  change ‖pairValue X p ^ k‖ ≤ q ^ k
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (pairValue_nonneg X p) k)]
  exact pow_le_pow_left₀ (pairValue_nonneg X p) (pairValue_le_fixedNorm X hq hX p) k

theorem integrable_maximumPair_pow (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    (k : ℕ) : Integrable (fun X : ι → E => maximumPair X ^ k) (Measure.pi (fun _ : ι => mu)) := by
  apply (integrable_const (q ^ k)).mono' (continuous_maximumPair.pow k).aestronglyMeasurable
  filter_upwards [ae_sample_fixedNorm hfixed] with X hX
  change ‖maximumPair X ^ k‖ ≤ q ^ k
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (maximumPair_nonneg X) k)]
  exact pow_le_pow_left₀ (maximumPair_nonneg X) (maximumPair_le_fixedNorm X hq hX) k

theorem integrable_maximumPair (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q) :
    Integrable (maximumPair : (ι → E) → ℝ) (Measure.pi (fun _ : ι => mu)) := by
  simpa only [pow_one] using integrable_maximumPair_pow (ι := ι) hfixed hq 1

theorem integral_pairValue_sixth_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hL6 : HasL6L2Marginals mu kappa) (p : Option (ι × ι)) :
    (∫ X : ι → E, pairValue X p ^ 6 ∂Measure.pi (fun _ : ι => mu)) ≤
      kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 := by
  cases p with
  | none => simp only [pairValue, zero_pow (by decide : 6 ≠ 0), integral_zero]; positivity
  | some p =>
    rcases p with ⟨i, j⟩
    by_cases hij : i = j
    · subst j
      simpa [pairValue] using
        (show (0 : ℝ) ≤ kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 by positivity)
    · simpa only [pairValue, if_neg hij] using integral_sample_pair_sixth_le hfixed hq hL6 i j hij

/-- The sixth moment of the maximum uses actual independence of distinct
sample coordinates, followed by a finite sum. -/
theorem integral_maximumPair_sixth_le {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hL6 : HasL6L2Marginals mu kappa) :
    (∫ X : Fin N → E, maximumPair X ^ 6 ∂Measure.pi (fun _ : Fin N => mu)) ≤
      2 * (N : ℝ) ^ 2 * kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 := by
  let K := kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  calc
    _ ≤ ∫ X : Fin N → E, ∑ p : Option (Fin N × Fin N), pairValue X p ^ 6
        ∂Measure.pi (fun _ : Fin N => mu) := by
      apply integral_mono (integrable_maximumPair_pow hfixed hq 6)
        (integrable_finsetSum _ (fun p _ => integrable_pairValue_pow hfixed hq p 6))
      exact maximumPair_sixth_le_sum
    _ = ∑ p : Option (Fin N × Fin N), ∫ X : Fin N → E, pairValue X p ^ 6
        ∂Measure.pi (fun _ : Fin N => mu) :=
      integral_finsetSum _ (fun p _ => integrable_pairValue_pow hfixed hq p 6)
    _ ≤ ∑ _p : Option (Fin N × Fin N), K := by
      exact Finset.sum_le_sum (fun p _ => integral_pairValue_sixth_le hfixed hq hL6 p)
    _ = ((N : ℝ) ^ 2 + 1) * K := by simp [pow_two]
    _ ≤ (2 * (N : ℝ) ^ 2) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
      nlinarith
    _ = _ := by dsimp [K]; ring

/-- The slight growth from dyadic sparse recursion is absorbed by the sixth
moment of the maximum pairwise inner product. -/
theorem integral_amplified_maximumPair_le {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa) :
    (∫ X : Fin N → E, amplification N * maximumPair X ∂Measure.pi (fun _ : Fin N => mu)) ≤
      2 * kappa * Real.sqrt (‖populationCovariance mu‖ * q * (N : ℝ)) := by
  let m := ∫ X : Fin N → E, maximumPair X ∂Measure.pi (fun _ : Fin N => mu)
  have hm : 0 ≤ m := integral_nonneg maximumPair_nonneg
  have ha : 0 ≤ amplification N := le_trans (by norm_num) (amplification_ge_one N)
  have hm6 : m ^ 6 ≤ 2 * (N : ℝ) ^ 2 * kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 :=
    (integral_sixth_ge_mean_sixth _ maximumPair (integrable_maximumPair hfixed hq)
      (integrable_maximumPair_pow hfixed hq 6) (Filter.Eventually.of_forall maximumPair_nonneg)).trans
      (integral_maximumPair_sixth_le hN hfixed hq hL6)
  rw [integral_const_mul]
  change amplification N * m ≤ _
  apply (pow_le_pow_iff_left₀ (mul_nonneg ha hm) (by positivity) (by decide : 6 ≠ 0)).mp
  calc
    (amplification N * m) ^ 6 = amplification N ^ 6 * m ^ 6 := mul_pow _ _ _
    _ ≤ (N : ℝ) * (2 * (N : ℝ) ^ 2 * kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3) :=
      mul_le_mul (amplification_sixth_le hN) hm6 (pow_nonneg hm 6) (Nat.cast_nonneg N)
    _ ≤ (2 * kappa * Real.sqrt (‖populationCovariance mu‖ * q * (N : ℝ))) ^ 6 := by
      rw [mul_pow, mul_pow, SparseEntropyRate.sqrt_sixth (by positivity)]
      have hn : 0 ≤ (N : ℝ) ^ 3 * kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 := by positivity
      nlinarith

end
end TomographyOracleCore.Revision.MaximumPairMoments
