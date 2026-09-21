import TomographyOracleCore.Revision.SparseLevelProbability

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.SparsePartitionFailure

open MeasureTheory PeriodicForwardCovariance SparseLevelProbability SparseDyadicScales
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def partitionFailure (kappa s : ℝ) (I : Finset ι) : Set (ι → E) :=
  ⋃ j ∈ Finset.range (Fintype.card ι), levelFailure kappa s I j ∪ levelFailure kappa s Iᶜ j

theorem measurableSet_partitionFailure (kappa s : ℝ) (I : Finset ι) :
    MeasurableSet (partitionFailure (E := E) kappa s I) := by
  unfold partitionFailure
  exact MeasurableSet.biUnion (Finset.range (Fintype.card ι)).countable_toSet (fun j hj =>
    (measurableSet_levelFailure kappa s I j).union (measurableSet_levelFailure kappa s Iᶜ j))

theorem measureReal_partitionFailure_le [CompleteSpace E] {mu : Measure E} [IsProbabilityMeasure mu]
    (hN : 0 < Fintype.card ι) {q kappa : ℝ}
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hkappa : 0 < kappa)
    (hL6 : HasL6L2Marginals mu kappa) (hs : 0 < ‖populationCovariance mu‖) (I : Finset ι) :
    (Measure.pi (fun _ : ι => mu)).real (partitionFailure kappa ‖populationCovariance mu‖ I) ≤
      2 / (Fintype.card ι : ℝ) ^ 3 := by
  have hNR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hN
  unfold partitionFailure
  calc
    _ ≤ ∑ j ∈ Finset.range (Fintype.card ι), (Measure.pi (fun _ : ι => mu)).real
        (levelFailure kappa ‖populationCovariance mu‖ I j ∪
          levelFailure kappa ‖populationCovariance mu‖ Iᶜ j) := measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _j ∈ Finset.range (Fintype.card ι), (2 : ℝ) / (Fintype.card ι : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro j hj
      have h1 := measureReal_levelFailure_le hfixed hkappa hL6 hs I j
      have h2 := measureReal_levelFailure_le hfixed hkappa hL6 hs Iᶜ j
      have hu := measureReal_union_le (μ := Measure.pi (fun _ : ι => mu))
        (levelFailure kappa ‖populationCovariance mu‖ I j)
        (levelFailure kappa ‖populationCovariance mu‖ Iᶜ j)
      convert hu.trans (add_le_add h1 h2) using 1 <;> ring
    _ = _ := by simp; field_simp

theorem good_partition_levels {kappa s : ℝ} {I : Finset ι} {X : ι → E}
    (hX : X ∉ partitionFailure kappa s I) (j : ℕ) (hN : size j ≤ Fintype.card ι) :
    X ∉ levelFailure kappa s I j ∧ X ∉ levelFailure kappa s Iᶜ j := by
  have hj : j ∈ Finset.range (Fintype.card ι) :=
    Finset.mem_range.mpr ((index_lt_size j).trans_le hN)
  constructor
  · intro h
    exact hX (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, Or.inl h⟩⟩)
  · intro h
    exact hX (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, Or.inr h⟩⟩)

end
end TomographyOracleCore.Revision.SparsePartitionFailure
