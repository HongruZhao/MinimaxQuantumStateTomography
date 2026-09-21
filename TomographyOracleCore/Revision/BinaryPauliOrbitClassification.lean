import TomographyOracleCore.Revision.BinarySymplecticExtension
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Complete invariants of finite Pauli-label families

Linear relations and pairwise symplectic products suffice to identify an
orbit of the concrete transvection-generated group. The extension theorem
used here was proved by explicit transvections, with no added axiom.
-/

namespace TomographyOracleCore.Revision.BinaryPauliOrbitClassification

open BinarySymplecticExtension
open scoped BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Equal Gram matrices give equal pairings for every pair of linear
combinations, over the binary field as over any field. -/
theorem pairing_linearCombination_eq
    (K : ℕ) (x y : ι → PauliLabel K)
    (hform : ∀ i j, pauliSymplecticForm K (x i) (x j) =
      pauliSymplecticForm K (y i) (y j))
    (a b : ι → ZMod 2) :
    pauliSymplecticForm K
        (Fintype.linearCombination (ZMod 2) x a)
        (Fintype.linearCombination (ZMod 2) x b) =
      pauliSymplecticForm K
        (Fintype.linearCombination (ZMod 2) y a)
        (Fintype.linearCombination (ZMod 2) y b) := by
  simp only [Fintype.linearCombination_apply, map_sum, LinearMap.sum_apply,
    map_smul, LinearMap.smul_apply, hform]

/-- Every isometry between two label families, including dependent
families, is implemented by the concrete transvection-generated group. -/
theorem exists_map_family_of_relations_and_pairings
    (K : ℕ) (x y : ι → PauliLabel K)
    (hrelations : ∀ a : ι → ZMod 2,
      Fintype.linearCombination (ZMod 2) x a = 0 ↔
        Fintype.linearCombination (ZMod 2) y a = 0)
    (hform : ∀ i j, pauliSymplecticForm K (x i) (x j) =
      pauliSymplecticForm K (y i) (y j)) :
    ∃ g : binaryTransvectionGroup K, ∀ i, g.1.1 (x i) = y i := by
  classical
  let Lx := Fintype.linearCombination (ZMod 2) x
  let Ly := Fintype.linearCombination (ZMod 2) y
  have hker : Lx.ker ≤ Ly.ker := fun a ha => (hrelations a).mp ha
  let f : Lx.range →ₗ[ZMod 2] PauliLabel K :=
    (Lx.ker.liftQ Ly hker).comp Lx.quotKerEquivRange.symm.toLinearMap
  have hf_image (a : ι → ZMod 2) (ha : Lx a ∈ Lx.range) :
      f ⟨Lx a, ha⟩ = Ly a := by
    simp [f]
  have hf : Function.Injective f := by
    intro u v huv
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    erw [hf_image, hf_image] at huv
    apply Subtype.ext
    have hz : Ly (a - b) = 0 := by rw [map_sub, huv, sub_self]
    have hz' := (hrelations (a - b)).mpr hz
    exact sub_eq_zero.mp (by simpa only [← map_sub] using hz')
  have hf_form (u v : Lx.range) :
      pauliSymplecticForm K (f u) (f v) = pauliSymplecticForm K u.val v.val := by
    rcases u with ⟨u, hu⟩
    rcases v with ⟨v, hv⟩
    obtain ⟨a, rfl⟩ := hu
    obtain ⟨b, rfl⟩ := hv
    erw [hf_image, hf_image]
    exact (pairing_linearCombination_eq K x y hform a b).symm
  obtain ⟨g, hg⟩ :=
    exists_extension_of_injective_form_preserving K Lx.range f hf hf_form
  refine ⟨g, ?_⟩
  intro i
  have hi := hg ⟨Lx (Pi.single i 1), LinearMap.mem_range_self Lx _⟩
  rw [hf_image] at hi
  simpa [Lx, Ly] using hi

end

end TomographyOracleCore.Revision.BinaryPauliOrbitClassification
