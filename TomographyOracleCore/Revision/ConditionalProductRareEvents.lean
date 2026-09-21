import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.ConditionalProductRareEvents

open MeasureTheory
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section

variable {α ι E : Type*} [MeasurableSpace α] [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def allRowsEvent (F : α → E) (J : Finset ι) (t : ℝ) : Set (α × (ι → E)) :=
  {z | ∀ i ∈ J, t * ‖F z.1‖ < |⟪z.2 i, F z.1⟫_ℝ|}

theorem measurableSet_allRowsEvent {F : α → E} (hF : Measurable F) (J : Finset ι) (t : ℝ) :
    MeasurableSet (allRowsEvent F J t) := by
  have hi (i : ι) : MeasurableSet {z : α × (ι → E) |
      t * ‖F z.1‖ < |⟪z.2 i, F z.1⟫_ℝ|} := by
    have hm : Measurable (fun z : α × (ι → E) => ⟪z.2 i, F z.1⟫_ℝ) := by fun_prop
    simpa only [Real.norm_eq_abs, Function.comp_apply] using
      measurableSet_lt ((hF.comp measurable_fst).norm.const_mul t) hm.norm
  have heq : allRowsEvent F J t = ⋂ i ∈ J, {z : α × (ι → E) |
      t * ‖F z.1‖ < |⟪z.2 i, F z.1⟫_ℝ|} := by ext; simp [allRowsEvent]
  rw [heq]
  exact MeasurableSet.biInter J.countable_toSet (fun i hiJ => hi i)

/-- Conditioning on an arbitrary measurable vector leaves independent
coordinate tests. This is a direct finite-product and Tonelli calculation. -/
theorem measure_allRowsEvent_le (mu : Measure E) [IsProbabilityMeasure mu]
    (nu : Measure α) [IsProbabilityMeasure nu] {F : α → E} (hF : Measurable F)
    (J : Finset ι) (t : ℝ) (p : ℝ≥0∞)
    (htail : ∀ v : E, mu {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤ p) :
    (nu.prod (Measure.pi (fun _ : ι => mu))) (allRowsEvent F J t) ≤ p ^ J.card := by
  rw [Measure.prod_apply (measurableSet_allRowsEvent hF J t)]
  calc
    _ ≤ ∫⁻ _a, p ^ J.card ∂nu := by
      apply lintegral_mono
      intro a
      change (Measure.pi (fun _ : ι => mu)) (Prod.mk a ⁻¹' allRowsEvent F J t) ≤ p ^ J.card
      have heq : Prod.mk a ⁻¹' allRowsEvent F J t =
          (J : Set ι).pi (fun _ => {x : E | t * ‖F a‖ < |⟪x, F a⟫_ℝ|}) := by
        ext x; simp [allRowsEvent, Set.mem_pi]
      rw [heq, Measure.pi_pi_finset]
      calc
        _ ≤ ∏ _i ∈ J, p := Finset.prod_le_prod' (fun i hi => htail (F a))
        _ = _ := by simp
    _ = _ := by simp

end
end TomographyOracleCore.Revision.ConditionalProductRareEvents
