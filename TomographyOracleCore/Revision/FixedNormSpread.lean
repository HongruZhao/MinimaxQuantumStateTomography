import TomographyOracleCore.Revision.GaussianSpreadEnvelope

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.FixedNormSpread

open MeasureTheory PeriodicForwardCovariance GaussianUniformSpread GaussianSpreadEnvelope
open FixedNormCovarianceBounds EuclideanGaussianObservable
open TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
open scoped NNReal BigOperators InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

def smoothingVariance (mu : Measure (EuclideanSpace ℝ ι)) (q : ℝ) : ℝ≥0 :=
  (‖populationCovariance mu‖ / q).toNNReal

theorem smoothingVariance_coe (mu : Measure (EuclideanSpace ℝ ι)) {q : ℝ} (hq : 0 < q) :
    (smoothingVariance mu q : ℝ) = ‖populationCovariance mu‖ / q :=
  Real.coe_toNNReal _ (div_nonneg (norm_nonneg _) hq.le)

def normalizedSpreadEnvelope (mu : Measure (EuclideanSpace ℝ ι)) (kappa q lambda : ℝ)
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) : ℝ :=
  spreadEnvelope mu kappa q lambda (smoothingVariance mu q) sample / (lambda * (T : ℝ))

variable {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu] {q : ℝ}

theorem integrable_normalizedSpreadEnvelope (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (kappa lambda : ℝ) {T : ℕ} :
    Integrable (normalizedSpreadEnvelope mu kappa q lambda : (Fin T → EuclideanSpace ℝ ι) → ℝ)
      (Measure.pi (fun _ : Fin T => mu)) :=
  (integrable_spreadEnvelope hfixed kappa lambda (smoothingVariance mu q)).div_const _

theorem normalizedSpreadEnvelope_nonneg (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) {lambda : ℝ} (hlambda : 0 ≤ lambda)
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) :
    0 ≤ normalizedSpreadEnvelope mu kappa q lambda sample :=
  div_nonneg (spreadEnvelope_nonneg hfixed hkappa lambda _ sample) (mul_nonneg hlambda (Nat.cast_nonneg T))

theorem integral_normalizedSpreadEnvelope (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    (kappa : ℝ) {lambda : ℝ} (hlambda : 0 < lambda) {T : ℕ} (hT : 0 < T) :
    (∫ sample : Fin T → EuclideanSpace ℝ ι, normalizedSpreadEnvelope mu kappa q lambda sample
      ∂Measure.pi (fun _ : Fin T => mu)) =
      (q / ‖populationCovariance mu‖ + 2) / (lambda * (T : ℝ)) +
        lambda * (2 * spreadC * kappa ^ 3 + 2 * spreadC + 4) * ‖populationCovariance mu‖ ^ 2 := by
  have hs := norm_populationCovariance_pos hfixed hq
  have hTR : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold normalizedSpreadEnvelope
  rw [integral_div, integral_spreadEnvelope hfixed, smoothingVariance_coe mu hq]
  unfold spreadVarianceBound
  rw [smoothingVariance_coe mu hq]
  field_simp [hlambda.ne', hTR, hq.ne', hs.ne']
  ring

theorem integral_normalizedSpreadEnvelope_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 1 ≤ kappa) {lambda : ℝ} (hlambda : 0 < lambda) {T : ℕ} (hT : 0 < T) :
    (∫ sample : Fin T → EuclideanSpace ℝ ι, normalizedSpreadEnvelope mu kappa q lambda sample
      ∂Measure.pi (fun _ : Fin T => mu)) ≤
      3 * (q / ‖populationCovariance mu‖) / (lambda * (T : ℝ)) +
        (4 * spreadC * kappa ^ 3 + 4) * lambda * ‖populationCovariance mu‖ ^ 2 := by
  rw [integral_normalizedSpreadEnvelope hfixed hq kappa hlambda hT]
  have hr := effectiveRank_ge_one hfixed hq
  have hc0 : 0 ≤ spreadC := le_trans (by norm_num) spreadC_ge_one
  have hk3 : 1 ≤ kappa ^ 3 := by simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hkappa 3
  have hfrac := div_le_div_of_nonneg_right
    (show q / ‖populationCovariance mu‖ + 2 ≤ 3 * (q / ‖populationCovariance mu‖) by linarith)
    (show 0 ≤ lambda * (T : ℝ) by positivity)
  have hcoeff : 2 * spreadC * kappa ^ 3 + 2 * spreadC + 4 ≤ 4 * spreadC * kappa ^ 3 + 4 := by
    nlinarith [mul_nonneg hc0 (sub_nonneg.2 hk3)]
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoeff hlambda.le)
    (sq_nonneg ‖populationCovariance mu‖)
  nlinarith

/-- A dimension-free expected envelope for the actual clipped covariance
process, proved solely from fixed norm and sixth-to-second marginal moments. -/
theorem ae_all_directions_normalized_spread (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    {lambda : ℝ} (hlambda : 0 < lambda) {T : ℕ} (hT : 0 < T) :
    ∀ᵐ sample : Fin T → EuclideanSpace ℝ ι ∂Measure.pi (fun _ : Fin T => mu),
      ∀ u : EuclideanSpace ℝ ι, ‖u‖ ≤ 1 →
      |(lambda * (T : ℝ))⁻¹ * (∑ i, clippedPsi (lambda * ⟪sample i, u⟫_ℝ ^ 2)) -
        (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu)| ≤ normalizedSpreadEnvelope mu kappa q lambda sample := by
  have hs := norm_populationCovariance_pos hfixed hq
  have hv : 0 < (smoothingVariance mu q : ℝ) := by rw [smoothingVariance_coe mu hq]; positivity
  have hden : 0 < lambda * (T : ℝ) := by positivity
  filter_upwards [ae_all_directions_clipped_bound hfixed hkappa hL6 lambda (smoothingVariance mu q) hv
    (T := T)] with sample hsample
  intro u hu
  have h := div_le_div_of_nonneg_right (hsample u hu) hden.le
  have heq : |(lambda * (T : ℝ))⁻¹ * (∑ i, clippedPsi (lambda * ⟪sample i, u⟫_ℝ ^ 2)) -
        (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu)| =
      |(∑ i, clippedPsi (lambda * ⟪sample i, u⟫_ℝ ^ 2)) -
        lambda * (T : ℝ) * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu)| / (lambda * (T : ℝ)) := by
    rw [← abs_of_pos hden, ← abs_div]
    congr 1
    field_simp
    rw [abs_of_pos hden]
  rw [heq]
  exact h

end
end TomographyOracleCore.Revision.FixedNormSpread
