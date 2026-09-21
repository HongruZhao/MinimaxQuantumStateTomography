import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

namespace TomographyOracleCore.Revision.IntegralSixthJensen

open MeasureTheory
noncomputable section

theorem sixth_young {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    6 * m ^ 5 * x ≤ x ^ 6 + 5 * m ^ 6 := by
  have h := mul_nonneg (sq_nonneg (x - m))
    (show 0 ≤ x ^ 4 + 2 * m * x ^ 3 + 3 * m ^ 2 * x ^ 2 + 4 * m ^ 3 * x + 5 * m ^ 4 by positivity)
  nlinarith

/-- Sixth-moment Jensen inequality proved by a nonnegative polynomial identity. -/
theorem integral_sixth_ge_mean_sixth {α : Type*} [MeasurableSpace α]
    (mu : Measure α) [IsProbabilityMeasure mu] (f : α → ℝ)
    (hf : Integrable f mu) (hf6 : Integrable (fun x => f x ^ 6) mu)
    (hf0 : ∀ᵐ x ∂mu, 0 ≤ f x) :
    (∫ x, f x ∂mu) ^ 6 ≤ ∫ x, f x ^ 6 ∂mu := by
  let m := ∫ x, f x ∂mu
  have hm : 0 ≤ m := integral_nonneg_of_ae hf0
  have hpoint : ∀ᵐ x ∂mu, 6 * m ^ 5 * f x ≤ f x ^ 6 + 5 * m ^ 6 := by
    filter_upwards [hf0] with x hx
    exact sixth_young hx hm
  have h := integral_mono_ae (hf.const_mul (6 * m ^ 5))
    (hf6.add (integrable_const (5 * m ^ 6))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_const_mul, integral_add hf6 (integrable_const _), integral_const] at h
  change 6 * m ^ 5 * m ≤ (∫ x, f x ^ 6 ∂mu) + _ at h
  simp at h
  change m ^ 6 ≤ _
  nlinarith

end
end TomographyOracleCore.Revision.IntegralSixthJensen
