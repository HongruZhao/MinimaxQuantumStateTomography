import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.IntegralCauchySchwarz

open MeasureTheory
noncomputable section

/-- Cauchy--Schwarz directly from the nonnegativity of the integral of a
square, with only the three required integrability assumptions. -/
theorem integral_mul_sq_le {Ω : Type*} [MeasurableSpace Ω] (mu : Measure Ω)
    (f g : Ω → ℝ) (hf : Integrable (fun x => f x ^ 2) mu)
    (hg : Integrable (fun x => g x ^ 2) mu) (hfg : Integrable (fun x => f x * g x) mu) :
    (∫ x, f x * g x ∂mu) ^ 2 ≤ (∫ x, f x ^ 2 ∂mu) * (∫ x, g x ^ 2 ∂mu) := by
  let a := ∫ x, f x ^ 2 ∂mu
  let b := ∫ x, f x * g x ∂mu
  let c := ∫ x, g x ^ 2 ∂mu
  have ha : 0 ≤ a := integral_nonneg fun _ => sq_nonneg _
  have hc : 0 ≤ c := integral_nonneg fun _ => sq_nonneg _
  have hquad (t : ℝ) : 0 ≤ a - 2 * t * b + t ^ 2 * c := by
    have h : 0 ≤ ∫ x, (f x - t * g x) ^ 2 ∂mu :=
      integral_nonneg (fun x => sq_nonneg (f x - t * g x))
    have heq : (∫ x, (f x - t * g x) ^ 2 ∂mu) = a - 2 * t * b + t ^ 2 * c := by
      calc
        _ = ∫ x, f x ^ 2 - (2 * t) * (f x * g x) + t ^ 2 * g x ^ 2 ∂mu := by
          apply integral_congr_ae
          filter_upwards [] with x
          ring
        _ = _ := by
          have hadd := integral_add (hf.sub (hfg.const_mul (2 * t))) (hg.const_mul (t ^ 2))
          simp only [Pi.sub_apply] at hadd
          rw [hadd]
          rw [integral_sub hf (hfg.const_mul (2 * t)), integral_const_mul, integral_const_mul]
    rwa [heq] at h
  change b ^ 2 ≤ a * c
  by_cases hc0 : c = 0
  · have hz := hquad ((a + 1) / (2 * b))
    by_cases hb : b = 0
    · simp [hb, hc0]
    have heq : a - 2 * ((a + 1) / (2 * b)) * b + ((a + 1) / (2 * b)) ^ 2 * c = -1 := by
      rw [hc0]
      field_simp
      ring
    rw [heq] at hz
    linarith
  · have h := mul_nonneg (hquad (b / c)) hc
    field_simp at h
    nlinarith

end
end TomographyOracleCore.Revision.IntegralCauchySchwarz
