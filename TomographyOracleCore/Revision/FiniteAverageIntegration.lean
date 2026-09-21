import TomographyOracleCore.Revision.FiniteProbabilityAverage
import Mathlib.MeasureTheory.Integral.Bochner.Basic

namespace TomographyOracleCore.Revision.FiniteAverageIntegration

open MeasureTheory FiniteProbabilityAverage
open scoped BigOperators
noncomputable section
variable {α Ω : Type*} [MeasurableSpace α] [Fintype Ω] {mu : Measure α}

theorem integrable_average (P : Law Ω) (f : Ω → α → ℝ) (hf : ∀ w, Integrable (f w) mu) :
    Integrable (fun x => average P (fun w => f w x)) mu := by
  unfold average
  exact integrable_finset_sum _ (fun w _ => (hf w).const_mul _)

theorem measurable_average (P : Law Ω) (f : Ω → α → ℝ) (hf : ∀ w, Measurable (f w)) :
    Measurable (fun x => average P (fun w => f w x)) := by
  unfold average
  fun_prop

theorem integral_average (P : Law Ω) (f : Ω → α → ℝ) (hf : ∀ w, Integrable (f w) mu) :
    (∫ x, average P (fun w => f w x) ∂mu) = average P (fun w => ∫ x, f w x ∂mu) := by
  unfold average
  rw [integral_finsetSum Finset.univ (fun w _ => (hf w).const_mul _)]
  apply Finset.sum_congr rfl
  intro w hw
  exact integral_const_mul _ _

end
end TomographyOracleCore.Revision.FiniteAverageIntegration
