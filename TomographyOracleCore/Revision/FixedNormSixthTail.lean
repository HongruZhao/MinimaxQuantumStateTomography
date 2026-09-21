import TomographyOracleCore.Revision.FixedNormMarginalMoments

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.FixedNormSixthTail

open MeasureTheory PeriodicForwardCovariance FixedNormMarginalMoments
open scoped InnerProductSpace ENNReal
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}

theorem measureReal_marginal_tail_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hL6 : HasL6L2Marginals mu kappa) {t : ℝ} (ht : 0 < t) (v : E) :
    mu.real {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤ kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 / t ^ 6 := by
  by_cases hv : v = 0
  · simp only [hv, norm_zero, mul_zero, inner_zero_right, abs_zero, lt_self_iff_false, Set.setOf_false,
      measureReal_empty]
    positivity
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have heps : 0 < (t * ‖v‖) ^ 6 := by positivity
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x : E => (by positivity : 0 ≤ |⟪x, v⟫_ℝ| ^ 6)))
    (integrable_abs_inner_pow hfixed v 6) ((t * ‖v‖) ^ 6)
  have hmoment := sixthMoment_le_populationCovariance_norm_mul_sq (fixedNorm_memLp hfixed 2) hL6 v
  calc
    mu.real {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤
        mu.real {x | (t * ‖v‖) ^ 6 ≤ |⟪x, v⟫_ℝ| ^ 6} := by
      exact measureReal_mono (fun x hx =>
        pow_le_pow_left₀ (mul_nonneg ht.le (norm_nonneg _)) hx.le 6) (measure_ne_top _ _)
    _ ≤ (∫ x, |⟪x, v⟫_ℝ| ^ 6 ∂mu) / (t * ‖v‖) ^ 6 :=
      (le_div_iff₀ heps).mpr (by nlinarith)
    _ ≤ (kappa ^ 6 * (‖populationCovariance mu‖ * ‖v‖ ^ 2) ^ 3) / (t * ‖v‖) ^ 6 :=
      div_le_div_of_nonneg_right hmoment heps.le
    _ = _ := by field_simp

theorem measure_marginal_tail_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hL6 : HasL6L2Marginals mu kappa) {t : ℝ} (ht : 0 < t) (v : E) :
    mu {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤
      ENNReal.ofReal (kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 / t ^ 6) := by
  have h := ENNReal.ofReal_le_ofReal (measureReal_marginal_tail_le hfixed hL6 ht v)
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

end
end TomographyOracleCore.Revision.FixedNormSixthTail
