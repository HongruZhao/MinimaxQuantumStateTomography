import TomographyOracleCore.Revision.ClippingLogCalculus

namespace TomographyOracleCore.Revision.ClippingLogSmoothing

open MeasureTheory Real Set ClippingLogCalculus
open TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω) [IsProbabilityMeasure mu]

theorem integrable_logQuadratic (Z : Ω → ℝ) (hZ : Integrable Z mu)
    (hZ2 : Integrable (fun omega => Z omega ^ 2) mu) :
    Integrable (fun omega => logQuadratic (Z omega)) mu := by
  apply ((integrable_const (1 : ℝ)).add hZ.norm |>.add hZ2).mono'
    (continuous_logQuadratic.comp_aestronglyMeasurable hZ.aestronglyMeasurable)
  filter_upwards [] with omega
  simp only [Pi.add_apply, Real.norm_eq_abs]
  apply abs_le.2
  have hlo := logQuadratic_lower (Z omega)
  have hhi := logQuadratic_upper (Z omega)
  constructor <;> nlinarith [sq_nonneg (Z omega), abs_nonneg (Z omega), le_abs_self (Z omega)]

/-- A corrected elementary smoothing inequality. The cap has a factor two;
the cap with coefficient one printed in the cited auxiliary lemma fails
for general two-point random variables. This version suffices for the same
covariance rate with a larger universal constant. -/
theorem clipped_integral_le_log_integral_add_min (Z : Ω → ℝ)
    (hZ : Integrable Z mu) (hZ2 : Integrable (fun omega => Z omega ^ 2) mu) :
    clippedPsi (∫ omega, Z omega ∂mu) ≤
      (∫ omega, logQuadratic (Z omega) ∂mu) +
        2 * min 1 (∫ omega, Z omega ^ 2 ∂mu) := by
  have hi := integrable_logQuadratic mu Z hZ hZ2
  have hg : Continuous convexCorrection := continuous_logQuadratic.add (continuous_id.pow 2)
  have hj := convexOn_convexCorrection.map_integral_le hg.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hZ (hi.add hZ2)
  change logQuadratic (∫ omega, Z omega ∂mu) + (∫ omega, Z omega ∂mu) ^ 2 ≤
    ∫ omega, logQuadratic (Z omega) + Z omega ^ 2 ∂mu at hj
  rw [integral_add hi hZ2] at hj
  have hfirst : clippedPsi (∫ omega, Z omega ∂mu) ≤
      (∫ omega, logQuadratic (Z omega) ∂mu) + (∫ omega, Z omega ^ 2 ∂mu) := by
    have hp := clippedPsi_le_logQuadratic (∫ omega, Z omega ∂mu)
    nlinarith [sq_nonneg (∫ omega, Z omega ∂mu)]
  have hlower : -1 ≤ ∫ omega, logQuadratic (Z omega) ∂mu := by
    simpa using integral_mono (integrable_const (-1 : ℝ)) hi (fun omega => logQuadratic_lower (Z omega))
  have hsecond : clippedPsi (∫ omega, Z omega ∂mu) ≤
      (∫ omega, logQuadratic (Z omega) ∂mu) + 2 := by
    have := clippedPsi_le_one (∫ omega, Z omega ∂mu)
    linarith
  by_cases hsmall : (∫ omega, Z omega ^ 2 ∂mu) ≤ 1
  · rw [min_eq_right hsmall]
    have hn : 0 ≤ ∫ omega, Z omega ^ 2 ∂mu := integral_nonneg fun omega => sq_nonneg _
    linarith
  · rw [min_eq_left (le_of_not_ge hsmall), mul_one]
    exact hsecond

theorem quadratic_mul_min_sq_le (z : ℝ) : quadratic z * min 1 (z ^ 2) ≤ 3 * z ^ 2 := by
  let b := min 1 (z ^ 2)
  have hb0 : 0 ≤ b := le_min (by norm_num) (sq_nonneg _)
  have hb1 : b ≤ 1 := min_le_left _ _
  have hb2 : b ≤ z ^ 2 := min_le_right _ _
  have hbsq : b ^ 2 ≤ b := by nlinarith [mul_nonneg hb0 (sub_nonneg.2 hb1)]
  have hzb : z * b ≤ z ^ 2 := by nlinarith [sq_nonneg (z - b)]
  have hz2b : z ^ 2 * b ≤ z ^ 2 := by nlinarith [mul_nonneg (sq_nonneg z) (sub_nonneg.2 hb1)]
  change quadratic z * b ≤ _
  unfold quadratic
  nlinarith

theorem exp_mul_le_chord (a b : ℝ) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    Real.exp (a * b) ≤ 1 + (Real.exp a - 1) * b := by
  have h := convexOn_exp.2 (show (0 : ℝ) ∈ Set.univ from Set.mem_univ _)
    (show a ∈ Set.univ from Set.mem_univ _) (sub_nonneg.2 hb1) hb0 (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at h
  rw [mul_comm b a] at h
  nlinarith

def smoothingCoefficient (a : ℝ) : ℝ := 1 + 3 * (Real.exp a - 1)

theorem smoothingCoefficient_ge_one {a : ℝ} (ha : 0 ≤ a) : 1 ≤ smoothingCoefficient a := by
  have := Real.one_le_exp_iff.2 ha
  unfold smoothingCoefficient
  linarith

/-- Absorbing the bounded quadratic correction into the logarithm costs
only a universal increase of its quadratic coefficient. -/
theorem logQuadratic_add_min_le_log (a z : ℝ) (ha : 0 ≤ a) :
    logQuadratic z + a * min 1 (z ^ 2) ≤
      Real.log (1 + z + smoothingCoefficient a * z ^ 2) := by
  have he : 0 ≤ Real.exp a - 1 := sub_nonneg.2 (Real.one_le_exp_iff.2 ha)
  have hco := smoothingCoefficient_ge_one ha
  have hpos : 0 < 1 + z + smoothingCoefficient a * z ^ 2 := by
    have hp := quadratic_pos z
    have := mul_nonneg (sub_nonneg.2 hco) (sq_nonneg z)
    unfold quadratic at hp
    nlinarith
  have h1 := exp_mul_le_chord a (min 1 (z ^ 2)) (le_min (by norm_num) (sq_nonneg _))
    (min_le_left _ _)
  have h2 := mul_le_mul_of_nonneg_left h1 (quadratic_pos z).le
  have h3 := mul_le_mul_of_nonneg_left (quadratic_mul_min_sq_le z) he
  have hprod : quadratic z * Real.exp (a * min 1 (z ^ 2)) ≤
      1 + z + smoothingCoefficient a * z ^ 2 := by
    unfold smoothingCoefficient quadratic at *
    nlinarith
  have hlog := Real.log_le_log (mul_pos (quadratic_pos z) (Real.exp_pos _)) hprod
  rw [Real.log_mul (quadratic_pos z).ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  exact hlog

end
end TomographyOracleCore.Revision.ClippingLogSmoothing
