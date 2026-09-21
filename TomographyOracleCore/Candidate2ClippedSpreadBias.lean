import TomographyOracleCore.Candidate2ClippedSpreadLipschitz

/-!
# Population bias of the clipped spread process

This file proves the elementary bias estimate used in the spread half of the
dimension-free Bai--Yin argument.  For a nonnegative observation `y`, clipping
removes a nonnegative amount bounded by `lambda^2 * y^3`.  For squared
directional marginals this is a sixth-moment envelope, and the verified
`L6--L2` hypothesis converts it to the population covariance scale.

No empirical-process concentration or uniform supremum estimate is asserted
here.
-/

open MeasureTheory InnerProductSpace
open scoped RealInnerProductSpace ENNReal

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

/-- Clipping removes a nonnegative amount from a nonnegative observation. -/
theorem sub_clippedSpread_nonneg
    {lambda y : ℝ} (hlambda : 0 < lambda) (hy : 0 ≤ y) :
    0 ≤ y - clippedSpread lambda y := by
  exact sub_nonneg.mpr (clippedSpread_le_self hlambda hy)

/-- The clipping bias has the same sixth-moment envelope as the peaky term. -/
theorem sub_clippedSpread_le_lambda_sq_mul_cube
    {lambda y : ℝ} (hlambda : 0 < lambda) (hy : 0 ≤ y) :
    y - clippedSpread lambda y ≤ lambda ^ 2 * y ^ 3 := by
  have hdecomp := self_le_peakyTerm_add_clippedSpread hlambda hy
  have hpeaky := peakyTerm_le_lambda_sq_mul_cube hlambda hy
  linarith

/-- Absolute-value form of the scalar clipping-bias bound. -/
theorem abs_sub_clippedSpread_le_lambda_sq_mul_cube
    {lambda y : ℝ} (hlambda : 0 < lambda) (hy : 0 ≤ y) :
    |y - clippedSpread lambda y| ≤ lambda ^ 2 * y ^ 3 := by
  rw [abs_of_nonneg (sub_clippedSpread_nonneg hlambda hy)]
  exact sub_clippedSpread_le_lambda_sq_mul_cube hlambda hy

/-- The population amount removed by directional clipping. -/
def directionalClippingBias
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (mu : Measure E) (lambda : ℝ) (u : E) : ℝ :=
  ∫ x, ⟪x, u⟫_ℝ ^ 2 - clippedSpread lambda (⟪x, u⟫_ℝ ^ 2) ∂mu

/-- A finite fixed-norm law has an integrable sixth power in every real
direction.  This discharges the only integrability premise in the population
bias estimate for the concrete Candidate 2 vector law. -/
theorem fixedNorm_integrable_directionalSixth
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {mu : Measure E} [IsFiniteMeasure mu] {q : ℝ}
    (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (u : E) :
    Integrable (fun x => |⟪x, u⟫_ℝ| ^ 6) mu := by
  have hid6 : MemLp id (6 : ℝ≥0∞) mu := fixedNorm_memLp hnorm 6
  have hinner6 : MemLp (fun x => ⟪x, u⟫_ℝ) (6 : ℝ≥0∞) mu :=
    hid6.inner_const u
  simpa only [Real.norm_eq_abs] using
    hinner6.integrable_norm_pow (by norm_num : (6 : ℕ) ≠ 0)

/-- Directional clipping bias is nonnegative. -/
theorem directionalClippingBias_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E]
    (mu : Measure E) {lambda : ℝ} (hlambda : 0 < lambda) (u : E) :
    0 ≤ directionalClippingBias mu lambda u := by
  unfold directionalClippingBias
  exact integral_nonneg fun x =>
    sub_clippedSpread_nonneg hlambda (sq_nonneg _)

/-- The population clipping bias is bounded by the directional sixth moment.
The `MemLp` premise supplies exactly the integrability needed for the integral
comparison; fixed-norm Candidate 2 laws satisfy it for every exponent. -/
theorem directionalClippingBias_le_sixthMoment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {mu : Measure E} (u : E)
    (hsix : Integrable (fun x => |⟪x, u⟫_ℝ| ^ 6) mu)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    directionalClippingBias mu lambda u ≤
      lambda ^ 2 * ∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu := by
  have hupper : Integrable (fun x => lambda ^ 2 * |⟪x, u⟫_ℝ| ^ 6) mu :=
    hsix.const_mul (lambda ^ 2)
  unfold directionalClippingBias
  calc
    (∫ x, ⟪x, u⟫_ℝ ^ 2 -
        clippedSpread lambda (⟪x, u⟫_ℝ ^ 2) ∂mu) ≤
        ∫ x, lambda ^ 2 * |⟪x, u⟫_ℝ| ^ 6 ∂mu := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x =>
          sub_clippedSpread_nonneg hlambda (sq_nonneg _)
      · exact hupper
      · filter_upwards [] with x
        have hpoint := sub_clippedSpread_le_lambda_sq_mul_cube
          hlambda (sq_nonneg ⟪x, u⟫_ℝ)
        calc
          ⟪x, u⟫_ℝ ^ 2 - clippedSpread lambda (⟪x, u⟫_ℝ ^ 2) ≤
              lambda ^ 2 * (⟪x, u⟫_ℝ ^ 2) ^ 3 := hpoint
          _ = lambda ^ 2 * |⟪x, u⟫_ℝ| ^ 6 := by
            have habs : |⟪x, u⟫_ℝ| ^ 6 = ⟪x, u⟫_ℝ ^ 6 := by
              rw [← abs_pow]
              exact abs_of_nonneg (by positivity)
            rw [habs]
            ring
    _ = lambda ^ 2 * ∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu := by
      rw [integral_const_mul]

/-- Under the verified `L6--L2` marginal hypothesis, the directional clipping
bias has the explicit covariance-normalized bound used in Candidate 2. -/
theorem directionalClippingBias_le_covarianceScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu2 : MemLp id 2 mu) (u : E)
    (hsix : Integrable (fun x => |⟪x, u⟫_ℝ| ^ 6) mu)
    {kappa lambda : ℝ} (hL6 : HasL6L2Marginals mu kappa)
    (hlambda : 0 < lambda) :
    directionalClippingBias mu lambda u ≤
      lambda ^ 2 * kappa ^ 6 *
        (‖populationCovariance mu‖ * ‖u‖ ^ 2) ^ 3 := by
  calc
    directionalClippingBias mu lambda u ≤
        lambda ^ 2 * ∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu :=
      directionalClippingBias_le_sixthMoment u hsix hlambda
    _ ≤ lambda ^ 2 *
        (kappa ^ 6 * (‖populationCovariance mu‖ * ‖u‖ ^ 2) ^ 3) := by
      exact mul_le_mul_of_nonneg_left
        (sixthMoment_le_populationCovariance_norm_mul_sq hmu2 hL6 u)
        (sq_nonneg lambda)
    _ = lambda ^ 2 * kappa ^ 6 *
        (‖populationCovariance mu‖ * ‖u‖ ^ 2) ^ 3 := by ring

/-- Unit-direction specialization of the covariance-scale clipping bias. -/
theorem directionalClippingBias_le_covarianceScale_of_norm_eq_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu2 : MemLp id 2 mu) (u : E)
    (hsix : Integrable (fun x => |⟪x, u⟫_ℝ| ^ 6) mu)
    {kappa lambda : ℝ} (hL6 : HasL6L2Marginals mu kappa)
    (hlambda : 0 < lambda) (hu : ‖u‖ = 1) :
    directionalClippingBias mu lambda u ≤
      lambda ^ 2 * kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 := by
  simpa [hu] using directionalClippingBias_le_covarianceScale
    hmu2 u hsix hL6 hlambda

/-- Fixed-norm, unit-direction specialization with no separate integrability
premise. -/
theorem fixedNorm_directionalClippingBias_le_covarianceScale
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [SecondCountableTopology E]
    {mu : Measure E} [IsFiniteMeasure mu] {q : ℝ}
    (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa lambda : ℝ} (hL6 : HasL6L2Marginals mu kappa)
    (hlambda : 0 < lambda) (u : E) (hu : ‖u‖ = 1) :
    directionalClippingBias mu lambda u ≤
      lambda ^ 2 * kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 := by
  exact directionalClippingBias_le_covarianceScale_of_norm_eq_one
    (fixedNorm_memLp hnorm 2) u
    (fixedNorm_integrable_directionalSixth hnorm u)
    hL6 hlambda hu

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
