import TomographyOracleCore.Revision.SupportedCoefficientNets
import TomographyOracleCore.Revision.SparseSampleSuprema

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseCoefficientNets

open SparseCoefficientGeometry SparseSampleSuprema SupportedCoefficientNets
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A net for all sparse coefficient vectors in a prescribed partition. Its
approximation also keeps the difference sparse, which is needed for the
restricted operator-norm estimate. -/
theorem exists_sparse_net (I : Finset ι) {h : ℕ} (hh : h ≤ Fintype.card ι)
    {eta : ℝ} (heta : 0 < eta) :
    ∃ net : Finset (ι → ℝ),
      (∀ v ∈ net, Admissible h I v) ∧
      (∀ y : ι → ℝ, Admissible h I y →
        ∃ v ∈ net, coefficientNorm (fun i => y i - v i) ≤ eta ∧
          (support (fun i => y i - v i)).card ≤ h) ∧
      (net.card : ℝ) ≤ (Fintype.card ι).choose h * (1 + 2 / eta) ^ h := by
  classical
  choose nets hunit hcover hcard using fun S : Finset ι => exists_supported_net S heta
  let supports := (Finset.univ : Finset ι).powersetCard h
  let net := supports.biUnion (fun S => (nets S).image (restrict I))
  refine ⟨net, ?_, ?_, ?_⟩
  · intro v hv
    obtain ⟨S, hS, hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    have hc : S.card = h := (Finset.mem_powersetCard.mp hS).2
    have hwS := (hunit S w hw).1
    refine ⟨(coefficientNorm_restrict_le I w).trans (hunit S w hw).2, ?_, supported_restrict _ _⟩
    calc
      (support (restrict I w)).card ≤ (support w).card := Finset.card_le_card (support_restrict_subset _ _)
      _ ≤ S.card := Finset.card_le_card ((support_subset_iff _ _).mpr hwS)
      _ = h := hc
  · intro y hy
    obtain ⟨S, hyS, hSuniv, hc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (support y)) hy.2.1 (by simpa using hh)
    have hys : Supported y S := (support_subset_iff _ _).mp hyS
    obtain ⟨v, hv, hd⟩ := hcover S y hys hy.1
    have hvS := (hunit S v hv).1
    refine ⟨restrict I v, Finset.mem_biUnion.mpr ⟨S,
      Finset.mem_powersetCard.mpr ⟨hSuniv, hc⟩, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩, ?_, ?_⟩
    · have h := (coefficientNorm_restrict_le I (fun i => y i - v i)).trans hd
      rw [restrict_sub, restrict_eq_self hy.2.2] at h
      exact h
    · have hs : Supported (fun i => y i - restrict I v i) S :=
        supported_sub hys (supported_restrict_of_supported hvS I)
      exact (Finset.card_le_card ((support_subset_iff _ _).mpr hs)).trans hc.le
  · calc
      (net.card : ℝ) ≤ ∑ S ∈ supports, (((nets S).image (restrict I)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ S ∈ supports, (1 + 2 / eta) ^ h := by
        apply Finset.sum_le_sum
        intro S hS
        have hc : S.card = h := (Finset.mem_powersetCard.mp hS).2
        have hci : (((nets S).image (restrict I)).card : ℝ) ≤ (nets S).card := by
          exact_mod_cast Finset.card_image_le
        exact hci.trans (by simpa only [hc] using hcard S)
      _ = _ := by simp [supports, Finset.card_powersetCard]

end
end TomographyOracleCore.Revision.SparseCoefficientNets
