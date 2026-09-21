import TomographyOracleCore.Revision.PeakyEnvelopeMoments
import TomographyOracleCore.Revision.CovarianceRateAlgebra
import TomographyOracleCore.Revision.FixedNormCovarianceBounds

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace TomographyOracleCore.Revision.FixedNormPeaky

open MeasureTheory PeriodicForwardCovariance PeakyUniformEnvelope PeakyEnvelopeMoments
open CovarianceRateAlgebra SparseUniformEnergy FixedNormCovarianceBounds
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  [FiniteDimensional ℝ E] {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}

theorem integral_baseEnergy_le_rate {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (hregime : q ≤ (N : ℝ) * ‖populationCovariance mu‖) :
    (∫ X : Fin N → E, baseEnergy q X ∂Measure.pi (fun _ : Fin N => mu)) ≤
      3 * kappa * (N : ℝ) * varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
  have hs := norm_populationCovariance_pos hfixed hq
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hb := integral_baseEnergy_le hN hfixed hq.le (by linarith : 0 ≤ kappa) hL6
  rw [sqrt_total_eq hs.le hq.le hNR] at hb
  have hqT := q_le_totalRate hs.le hq.le hNR hregime
  have hkT := mul_le_mul_of_nonneg_right hkappa
    (mul_nonneg hNR.le (varianceRate_nonneg ‖populationCovariance mu‖ q N))
  nlinarith

theorem integral_goodPeakyEnvelope_le_rate {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (hregime : q ≤ (N : ℝ) * ‖populationCovariance mu‖) :
    (∫ X : Fin N → E, goodPeakyEnvelope q kappa ‖populationCovariance mu‖
      (clippingParameter ‖populationCovariance mu‖ q (N : ℝ)) X
      ∂Measure.pi (fun _ : Fin N => mu)) ≤
      8 * uniformEnergyConstant ^ 2 * kappa ^ 4 * varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
  have hs := norm_populationCovariance_pos hfixed hq
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hlambda := clippingParameter_pos hs hq hNR
  have hb := integral_baseEnergy_le_rate hN hfixed hq hkappa hL6 hregime
  have hv := integral_sqrt_baseEnergy_sq_le (N := N) hfixed hq.le hlambda.le
  have hv0 : 0 ≤ ∫ X : Fin N → E,
      Real.sqrt (clippingParameter ‖populationCovariance mu‖ q (N : ℝ) * baseEnergy q X)
        ∂Measure.pi (fun _ : Fin N => mu) := integral_nonneg (fun _ => Real.sqrt_nonneg _)
  have hnum := peaky_numerator_bound hNR hs.le hkappa hlambda.le
    (varianceRate_nonneg ‖populationCovariance mu‖ q N) hv0 (clippingParameter_mul_sq hs) hb hv
  rw [integral_goodPeakyEnvelope_eq hfixed hq.le kappa ‖populationCovariance mu‖ hlambda.le]
  calc
    _ ≤ uniformEnergyConstant ^ 2 *
        (8 * kappa ^ 4 * (N : ℝ) * varianceRate ‖populationCovariance mu‖ q (N : ℝ)) / (N : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum (sq_nonneg _)) hNR.le
    _ = _ := by field_simp

/-- The full expected uniform peaky bound has the sharp effective-rank rate.
Its proof includes the actual sparse event, its exceptional probability, and
the independent maximum-pair moment calculation. -/
theorem integral_peakyEnvelope_le_rate {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 1 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (hregime : q ≤ (N : ℝ) * ‖populationCovariance mu‖) :
    (∫ X : Fin N → E, peakyEnvelope q kappa ‖populationCovariance mu‖
      (clippingParameter ‖populationCovariance mu‖ q (N : ℝ)) X
      ∂Measure.pi (fun _ : Fin N => mu)) ≤
      (8 * uniformEnergyConstant ^ 2 + 16) * kappa ^ 4 *
        varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
  have hs := norm_populationCovariance_pos hfixed hq
  have hNR : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hlambda := clippingParameter_pos hs hq hNR
  have hfull := integral_peakyEnvelope_le_good_add_exception hN hfixed hq.le
    (by linarith : 0 < kappa) hL6 hs hlambda.le
  have hgood := integral_goodPeakyEnvelope_le_rate hN hfixed hq hkappa hL6 hregime
  have hexc : 16 * q / (N : ℝ) ^ 3 ≤ 16 * varianceRate ‖populationCovariance mu‖ q (N : ℝ) := by
    have h := mul_le_mul_of_nonneg_left (exceptional_rate_le hs.le hq.le hN1 hregime)
      (by norm_num : (0 : ℝ) ≤ 16)
    simpa only [mul_div_assoc] using h
  have hk4 : (1 : ℝ) ≤ kappa ^ 4 := one_le_pow₀ hkappa
  have hlast := mul_le_mul_of_nonneg_right hk4
    (show 0 ≤ 16 * varianceRate ‖populationCovariance mu‖ q (N : ℝ) by
      exact mul_nonneg (by norm_num) (varianceRate_nonneg _ _ _))
  nlinarith

end
end TomographyOracleCore.Revision.FixedNormPeaky
