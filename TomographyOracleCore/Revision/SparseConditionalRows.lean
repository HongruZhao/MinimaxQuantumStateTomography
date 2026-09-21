import TomographyOracleCore.Revision.ConditionalProductRareEvents
import TomographyOracleCore.Revision.FixedNormSixthTail
import TomographyOracleCore.Revision.SparseCoefficientGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseConditionalRows

open MeasureTheory PeriodicForwardCovariance SparseCoefficientGeometry ConditionalProductRareEvents
open FixedNormSixthTail
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def sampleRowsEvent (y : ι → ℝ) (R : Finset ι) (t : ℝ) : Set (ι → E) :=
  {X | ∀ i ∈ R, t * ‖synthesis X y‖ < |⟪X i, synthesis X y⟫_ℝ|}

theorem measurableSet_sampleRowsEvent (y : ι → ℝ) (R : Finset ι) (t : ℝ) :
    MeasurableSet (sampleRowsEvent (E := E) y R t) := by
  have hs : Measurable (fun X : ι → E => synthesis X y) := by unfold synthesis; fun_prop
  have hi (i : ι) : MeasurableSet {X : ι → E |
      t * ‖synthesis X y‖ < |⟪X i, synthesis X y⟫_ℝ|} := by
    have hm : Measurable (fun X : ι → E => ⟪X i, synthesis X y⟫_ℝ) := by fun_prop
    simpa only [Real.norm_eq_abs] using measurableSet_lt (hs.norm.const_mul t) hm.norm
  have heq : sampleRowsEvent (E := E) y R t = ⋂ i ∈ R,
      {X : ι → E | t * ‖synthesis X y‖ < |⟪X i, synthesis X y⟫_ℝ|} := by
    ext; simp [sampleRowsEvent]
  rw [heq]
  exact MeasurableSet.biInter R.countable_toSet (fun i hiR => hi i)

theorem measure_sampleRowsEvent_le (mu : Measure E) [IsProbabilityMeasure mu]
    (I : Finset ι) (y : ι → ℝ) (hy : Supported y I) (R : Finset ι) (hRI : R ⊆ Iᶜ)
    (t : ℝ) (p : ℝ≥0∞)
    (htail : ∀ v : E, mu {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤ p) :
    (Measure.pi (fun _ : ι => mu)) (sampleRowsEvent y R t) ≤ p ^ R.card := by
  classical
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : ι => E) (fun i => i ∈ I)
  let F : (I → E) → E := fun x => ∑ i : I, y i • x i
  let J : Finset {i : ι // i ∉ I} := R.subtype (fun i => i ∉ I)
  have hF : Measurable F := by dsimp [F]; fun_prop
  have hJc : J.card = R.card := by
    rw [Finset.card_subtype]
    congr 1
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact Finset.mem_compl.mp (hRI hi)
  have heq : e ⁻¹' allRowsEvent F J t = sampleRowsEvent y R t := by
    ext X
    have hs : F (e X).1 = synthesis X y := synthesis_eq_sum_subtype X y I hy
    change (∀ i ∈ J, t * ‖F (e X).1‖ < |⟪(e X).2 i, F (e X).1⟫_ℝ|) ↔
      ∀ i ∈ R, t * ‖synthesis X y‖ < |⟪X i, synthesis X y⟫_ℝ|
    rw [hs]
    constructor
    · intro h i hi
      exact h ⟨i, Finset.mem_compl.mp (hRI hi)⟩ (by simpa [J] using hi)
    · intro h i hi
      exact h i (by simpa [J] using hi)
  have hmp := measurePreserving_piEquivPiSubtypeProd (fun _ : ι => mu) (fun i => i ∈ I)
  rw [← heq, hmp.measure_preimage_equiv]
  have h := measure_allRowsEvent_le mu (Measure.pi (fun _ : I => mu)) hF J t p htail
  have hfi : Finset.Subtype.fintype I = Subtype.fintype (fun i : ι => i ∈ I) := Subsingleton.elim _ _
  rw [hfi] at h
  simpa only [hJc] using h

theorem measureReal_sampleRowsEvent_le (mu : Measure E) [IsProbabilityMeasure mu]
    (I : Finset ι) (y : ι → ℝ) (hy : Supported y I) (R : Finset ι) (hRI : R ⊆ Iᶜ)
    (t : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (htail : ∀ v : E, mu {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤ ENNReal.ofReal p) :
    (Measure.pi (fun _ : ι => mu)).real (sampleRowsEvent y R t) ≤ p ^ R.card := by
  have h := measure_sampleRowsEvent_le mu I y hy R hRI t (ENNReal.ofReal p) htail
  apply ENNReal.toReal_le_of_le_ofReal (pow_nonneg hp _)
  simpa only [ENNReal.ofReal_pow hp] using h

end
end TomographyOracleCore.Revision.SparseConditionalRows
