import TomographyOracleCore.Revision.SparseConditionalRows
import TomographyOracleCore.Revision.SparseDeterministicRecurrence

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseNetFailure

open MeasureTheory PeriodicForwardCovariance SparseCoefficientGeometry SparseSampleSuprema
open SparseConditionalRows SparseDeterministicRecurrence
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def netFailure (I : Finset ι) (net : Finset (ι → ℝ)) (r : ℕ) (t : ℝ) : Set (ι → E) :=
  ⋃ v ∈ net, ⋃ R ∈ Iᶜ.powersetCard r, sampleRowsEvent v R t

theorem measurableSet_netFailure (I : Finset ι) (net : Finset (ι → ℝ)) (r : ℕ) (t : ℝ) :
    MeasurableSet (netFailure (E := E) I net r t) := by
  unfold netFailure
  exact MeasurableSet.biUnion net.countable_toSet (fun v hv =>
    MeasurableSet.biUnion (Iᶜ.powersetCard r).countable_toSet (fun R hR =>
      measurableSet_sampleRowsEvent v R t))

theorem measureReal_netFailure_le (mu : Measure E) [IsProbabilityMeasure mu]
    (I : Finset ι) (net : Finset (ι → ℝ)) (r : ℕ) (t : ℝ)
    (hnet : ∀ v ∈ net, Supported v I) {p : ℝ} (hp : 0 ≤ p)
    (htail : ∀ v : E, mu {x | t * ‖v‖ < |⟪x, v⟫_ℝ|} ≤ ENNReal.ofReal p) :
    (Measure.pi (fun _ : ι => mu)).real (netFailure I net r t) ≤
      (net.card : ℝ) * (Fintype.card ι).choose r * p ^ r := by
  unfold netFailure
  calc
    _ ≤ ∑ v ∈ net, (Measure.pi (fun _ : ι => mu)).real
        (⋃ R ∈ Iᶜ.powersetCard r, sampleRowsEvent v R t) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ v ∈ net, ∑ R ∈ Iᶜ.powersetCard r,
        (Measure.pi (fun _ : ι => mu)).real (sampleRowsEvent v R t) := by
      apply Finset.sum_le_sum
      intro v hv
      exact measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _v ∈ net, ∑ _R ∈ Iᶜ.powersetCard r, p ^ r := by
      apply Finset.sum_le_sum
      intro v hv
      apply Finset.sum_le_sum
      intro R hR
      have hRp := Finset.mem_powersetCard.mp hR
      simpa only [hRp.2] using measureReal_sampleRowsEvent_le mu I v (hnet v hv) R hRp.1 t hp htail
    _ = (net.card : ℝ) * Iᶜ.card.choose r * p ^ r := by simp [Finset.card_powersetCard]; ring
    _ ≤ _ := by
      have hc : (Iᶜ.card.choose r : ℝ) ≤ (Fintype.card ι).choose r := by
        exact_mod_cast Nat.choose_le_choose r (Finset.card_le_univ Iᶜ)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _))
        (pow_nonneg hp _)

/-- On the complement of the explicit finite union, every net point has
fewer than r correlations exceeding its own norm-scaled threshold. -/
theorem largeRows_card_lt_of_not_mem {I : Finset ι} {net : Finset (ι → ℝ)} {r : ℕ} {t : ℝ}
    {X : ι → E} (hX : X ∉ netFailure I net r t) {v : ι → ℝ} (hv : v ∈ net) :
    (largeRows X v Iᶜ (t * ‖synthesis X v‖)).card < r := by
  by_contra h
  obtain ⟨R, hRsub, hRc⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  have hRm : R ∈ Iᶜ.powersetCard r :=
    Finset.mem_powersetCard.mpr ⟨hRsub.trans (Finset.filter_subset _ _), hRc⟩
  have hRe : X ∈ sampleRowsEvent v R t := by
    intro i hi
    have hri := (Finset.mem_filter.mp (hRsub hi)).2
    simpa only [real_inner_comm] using hri
  exact hX (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr ⟨hv,
    Set.mem_iUnion.mpr ⟨R, Set.mem_iUnion.mpr ⟨hRm, hRe⟩⟩⟩⟩)

end
end TomographyOracleCore.Revision.SparseNetFailure
