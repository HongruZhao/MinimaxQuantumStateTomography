import TomographyOracleCore.Revision.ClippingLogSmoothing

namespace TomographyOracleCore.Revision.QuadraticLogIntegrability

open MeasureTheory ClippingLogCalculus
noncomputable section

def quadraticLog (c z : ℝ) : ℝ := Real.log (1 + z + c * z ^ 2)

theorem polynomial_lower (c z : ℝ) (hc : 1 ≤ c) : (3 / 4 : ℝ) ≤ 1 + z + c * z ^ 2 := by
  have h := quadratic_lower z
  have := mul_nonneg (sub_nonneg.2 hc) (sq_nonneg z)
  unfold quadratic at h
  nlinarith

theorem polynomial_pos (c z : ℝ) (hc : 1 ≤ c) : 0 < 1 + z + c * z ^ 2 :=
  lt_of_lt_of_le (by norm_num) (polynomial_lower c z hc)

theorem continuous_quadraticLog (c : ℝ) (hc : 1 ≤ c) : Continuous (quadraticLog c) := by
  unfold quadraticLog
  apply Continuous.log (by fun_prop)
  intro z
  exact (polynomial_pos c z hc).ne'

theorem quadraticLog_lower (c z : ℝ) (hc : 1 ≤ c) : -1 ≤ quadraticLog c z := by
  apply (logQuadratic_lower z).trans
  apply Real.log_le_log (quadratic_pos z)
  unfold quadratic
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (sq_nonneg z)]

theorem quadraticLog_upper (c z : ℝ) (hc : 1 ≤ c) : quadraticLog c z ≤ z + c * z ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (polynomial_pos c z hc)
  change quadraticLog c z ≤ 1 + z + c * z ^ 2 - 1 at h
  linarith

theorem integrable_quadraticLog {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (c : ℝ) (hc : 1 ≤ c)
    (Z : Ω → ℝ) (hZ : Integrable Z mu) (hZ2 : Integrable (fun omega => Z omega ^ 2) mu) :
    Integrable (fun omega => quadraticLog c (Z omega)) mu := by
  apply ((integrable_const (1 : ℝ)).add hZ.norm |>.add (hZ2.const_mul c)).mono'
    ((continuous_quadraticLog c hc).comp_aestronglyMeasurable hZ.aestronglyMeasurable)
  filter_upwards [] with omega
  simp only [Pi.add_apply, Real.norm_eq_abs]
  apply abs_le.2
  have hlo := quadraticLog_lower c (Z omega) hc
  have hhi := quadraticLog_upper c (Z omega) hc
  have hcz : 0 ≤ c * Z omega ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  constructor <;> nlinarith [abs_nonneg (Z omega), le_abs_self (Z omega)]

theorem integrable_min_one_sq {Ω : Type*} [MeasurableSpace Ω]
    (mu : Measure Ω) [IsProbabilityMeasure mu] (Z : Ω → ℝ) (hZ : AEStronglyMeasurable Z mu) :
    Integrable (fun omega => min 1 (Z omega ^ 2)) mu := by
  apply (integrable_const (1 : ℝ)).mono'
    ((show Continuous (fun z : ℝ => min 1 (z ^ 2)) by fun_prop).comp_aestronglyMeasurable hZ)
  filter_upwards [] with omega
  rw [Real.norm_eq_abs, abs_of_nonneg (le_min (by norm_num) (sq_nonneg _))]
  exact min_le_left _ _

end
end TomographyOracleCore.Revision.QuadraticLogIntegrability
