import TomographyOracleCore.Revision.FixedNormPeaky
import TomographyOracleCore.Revision.FixedNormSpread
import TomographyOracleCore.Revision.FixedNormCovarianceIntegrability
import TomographyOracleCore.Candidate2FixedNormCovarianceFiniteSample

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace TomographyOracleCore.Revision.FixedNormBaiYinProof

open MeasureTheory PeriodicForwardCovariance PeriodicForwardCovariance.PeakySpread
open FixedNormPeaky FixedNormSpread FixedNormCovarianceBounds FixedNormCovarianceIntegrability
open PeakyUniformEnvelope CovarianceRateAlgebra SparseUniformEnergy GaussianUniformSpread
open MaximumPairMoments
open scoped BigOperators InnerProductSpace
noncomputable section

def covarianceConstant (kappa : ℝ) : ℝ :=
  (8 * uniformEnergyConstant ^ 2 + 23 + 4 * spreadC) * kappa ^ 4

theorem covarianceConstant_pos {kappa : ℝ} (hkappa : 1 ≤ kappa) : 0 < covarianceConstant kappa := by
  have hk : 0 < kappa := by linarith
  have hc : 0 ≤ spreadC := le_trans (by norm_num) spreadC_ge_one
  unfold covarianceConstant
  positivity

variable {ι : Type*} [Fintype ι]
  {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu] {q : ℝ}

theorem integral_normalizedSpreadEnvelope_le_rate {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 1 ≤ kappa) :
    (∫ X : Fin N → EuclideanSpace ℝ ι, normalizedSpreadEnvelope mu kappa q
      (clippingParameter ‖populationCovariance mu‖ q (N : ℝ)) X
      ∂Measure.pi (fun _ : Fin N => mu)) ≤
      (7 + 4 * spreadC) * kappa ^ 4 * varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
  have hs := norm_populationCovariance_pos hfixed hq
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hlambda := clippingParameter_pos hs hq hNR
  have h := integral_normalizedSpreadEnvelope_le hfixed hq hkappa hlambda hN
  have hfirst : 3 * (q / ‖populationCovariance mu‖) /
      (clippingParameter ‖populationCovariance mu‖ q (N : ℝ) * (N : ℝ)) =
      3 * varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
    rw [mul_div_assoc, rank_over_clipping_samples hs hq hNR]
  have hlast : (4 * spreadC * kappa ^ 3 + 4) *
      clippingParameter ‖populationCovariance mu‖ q (N : ℝ) * ‖populationCovariance mu‖ ^ 2 =
      (4 * spreadC * kappa ^ 3 + 4) * varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
    rw [mul_assoc, clippingParameter_mul_sq hs]
  rw [hfirst, hlast] at h
  have hk4 : (1 : ℝ) ≤ kappa ^ 4 := one_le_pow₀ hkappa
  have hk34 : kappa ^ 3 ≤ kappa ^ 4 := pow_le_pow_right₀ hkappa (by decide)
  have hc : 0 ≤ spreadC := le_trans (by norm_num) spreadC_ge_one
  have ht := varianceRate_nonneg ‖populationCovariance mu‖ q (N : ℝ)
  have h1 := mul_le_mul_of_nonneg_right hk4 (show 0 ≤ 7 * varianceRate ‖populationCovariance mu‖ q N by positivity)
  have h2 := mul_le_mul_of_nonneg_right hk34
    (show 0 ≤ 4 * spreadC * varianceRate ‖populationCovariance mu‖ q N by positivity)
  nlinarith

/-- The expected operator-norm covariance deviation for the actual finite
product sample. Every probability, net, moment, and smoothing step is proved
from the displayed fixed-norm and marginal assumptions. -/
theorem expected_covariance_error_le [Nonempty ι] {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (hregime : q ≤ (N : ℝ) * ‖populationCovariance mu‖) :
    (∫ X : Fin N → EuclideanSpace ℝ ι, ‖sampleCovariance X - populationCovariance mu‖
      ∂Measure.pi (fun _ : Fin N => mu)) ≤
      covarianceConstant kappa * ‖populationCovariance mu‖ *
        Real.sqrt ((q / ‖populationCovariance mu‖) / (N : ℝ)) := by
  let s := ‖populationCovariance mu‖
  let lambda := clippingParameter s q (N : ℝ)
  let P := peakyEnvelope q kappa s lambda (E := EuclideanSpace ℝ ι) (N := N)
  let R := normalizedSpreadEnvelope mu kappa q lambda (T := N)
  have hs : 0 < s := norm_populationCovariance_pos hfixed hq
  have hk0 : 0 ≤ kappa := by linarith
  have hkpos : 0 < kappa := by linarith
  have hlambda : 0 < lambda := clippingParameter_pos hs hq (Nat.cast_pos.mpr hN)
  have hPi : Integrable P (Measure.pi (fun _ : Fin N => mu)) :=
    integrable_peakyEnvelope hfixed hq.le hlambda.le
  have hRi : Integrable R (Measure.pi (fun _ : Fin N => mu)) :=
    integrable_normalizedSpreadEnvelope hfixed kappa lambda
  have hae : ∀ᵐ X : Fin N → EuclideanSpace ℝ ι ∂Measure.pi (fun _ : Fin N => mu),
      ‖sampleCovariance X - populationCovariance mu‖ ≤ P X + R X := by
    filter_upwards [ae_sample_fixedNorm hfixed,
      ae_all_directions_normalized_spread hfixed hq hk0 hL6 hlambda hN] with X hX hspread
    have hsymm : (sampleCovariance X - populationCovariance mu).toLinearMap.IsSymmetric :=
      (sampleCovariance_isSymmetric X).sub (populationCovariance_isSymmetric mu)
    obtain ⟨u, hu, hattain⟩ := exists_unit_norm_eq_abs_rayleighQuotient
      (sampleCovariance X - populationCovariance mu) hsymm
    have hdecomp := abs_covarianceError_rayleighQuotient_le_peaky_add_spread_of_norm_eq_one
      (fixedNorm_memLp hfixed 2) X u hu hlambda
    have hp := directionalPeakyMean_le_envelope hN hq.le hkpos hs hlambda X
      (fun i => (hX i).le) u hu.le
    have hr : |directionalSpreadMean lambda X u - (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu)| ≤ R X := by
      simpa only [directionalSpreadMean, spreadMean_eq_paper_normalization, directionalSquares]
        using hspread u hu.le
    rw [hattain]
    exact hdecomp.trans (add_le_add hp hr)
  have hP := integral_peakyEnvelope_le_rate hN hfixed hq hkappa hL6 hregime
  have hR := integral_normalizedSpreadEnvelope_le_rate hN hfixed hq hkappa
  calc
    _ ≤ ∫ X : Fin N → EuclideanSpace ℝ ι, P X + R X ∂Measure.pi (fun _ : Fin N => mu) :=
      integral_mono_ae (integrable_fixedNorm_covariance_error hfixed hN) (hPi.add hRi) hae
    _ = (∫ X, P X ∂Measure.pi (fun _ : Fin N => mu)) +
        (∫ X, R X ∂Measure.pi (fun _ : Fin N => mu)) := integral_add hPi hRi
    _ ≤ (8 * uniformEnergyConstant ^ 2 + 16) * kappa ^ 4 * varianceRate s q (N : ℝ) +
        (7 + 4 * spreadC) * kappa ^ 4 * varianceRate s q (N : ℝ) := add_le_add hP hR
    _ = covarianceConstant kappa * s * Real.sqrt ((q / s) / (N : ℝ)) := by
      rw [varianceRate_eq_effectiveRank hs hq.le (Nat.cast_nonneg N)]
      unfold covarianceConstant
      ring

end
end TomographyOracleCore.Revision.FixedNormBaiYinProof
