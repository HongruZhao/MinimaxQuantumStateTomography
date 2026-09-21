import TomographyOracleCore.Revision.SparseCoefficientGeometry

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.SparseSampleSuprema

open SparseCoefficientGeometry
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def Admissible (k : ℕ) (I : Finset ι) (y : ι → ℝ) : Prop :=
  coefficientNorm y ≤ 1 ∧ (support y).card ≤ k ∧ Supported y I

theorem admissible_zero (k : ℕ) (I : Finset ι) : Admissible k I 0 := by
  simp [Admissible]
theorem Admissible.mono {k l : ℕ} {I J : Finset ι} {y : ι → ℝ}
    (hy : Admissible k I y) (hkl : k ≤ l) (hIJ : I ⊆ J) : Admissible l J y := by
  refine ⟨hy.1, hy.2.1.trans hkl, ?_⟩
  intro i hi
  exact hy.2.2 i (fun h => hi (hIJ h))
theorem Admissible.restrict {k : ℕ} {I : Finset ι} {y : ι → ℝ}
    (hy : Admissible k I y) (J : Finset ι) : Admissible k I (restrict J y) := by
  refine ⟨(coefficientNorm_restrict_le J y).trans hy.1,
    (Finset.card_le_card (support_restrict_subset J y)).trans hy.2.1, ?_⟩
  intro i hi
  by_cases hj : i ∈ J <;> simp [SparseCoefficientGeometry.restrict, hj, hy.2.2 i hi]
theorem Admissible.restrict_card {k m : ℕ} {I : Finset ι} {y : ι → ℝ}
    (hy : Admissible k I y) (J : Finset ι) (hJ : J.card ≤ m) :
    Admissible m I (SparseCoefficientGeometry.restrict J y) := by
  refine ⟨(coefficientNorm_restrict_le J y).trans hy.1, ?_, (hy.restrict J).2.2⟩
  exact (Finset.card_le_card ((support_subset_iff _ _).mpr (supported_restrict J y))).trans hJ

def sparseNorm (X : ι → E) (k : ℕ) : ℝ :=
  sSup {a : ℝ | ∃ y : ι → ℝ, Admissible k Finset.univ y ∧ a = ‖synthesis X y‖}

def crossNorm (X : ι → E) (k : ℕ) (I : Finset ι) : ℝ :=
  sSup {a : ℝ | ∃ y z : ι → ℝ,
    Admissible k I y ∧ Admissible k Iᶜ z ∧ a = |⟪synthesis X y, synthesis X z⟫_ℝ|}

theorem sparse_values_bdd (X : ι → E) (k : ℕ) :
    BddAbove {a : ℝ | ∃ y : ι → ℝ, Admissible k Finset.univ y ∧ a = ‖synthesis X y‖} := by
  refine ⟨Real.sqrt (∑ i, ‖X i‖ ^ 2), ?_⟩
  rintro a ⟨y, hy, rfl⟩
  exact (synthesis_norm_le X y).trans (by
    simpa using mul_le_mul_of_nonneg_right hy.1 (Real.sqrt_nonneg (∑ i, ‖X i‖ ^ 2)))
theorem sparse_values_nonempty (X : ι → E) (k : ℕ) :
    {a : ℝ | ∃ y : ι → ℝ, Admissible k Finset.univ y ∧ a = ‖synthesis X y‖}.Nonempty :=
  ⟨0, 0, admissible_zero _ _, by simp⟩
theorem sparseNorm_nonneg (X : ι → E) (k : ℕ) : 0 ≤ sparseNorm X k :=
  le_csSup (sparse_values_bdd X k) ⟨0, admissible_zero _ _, by simp⟩
theorem synthesis_norm_le_sparseNorm {X : ι → E} {k : ℕ} {I : Finset ι} {y : ι → ℝ}
    (hy : Admissible k I y) : ‖synthesis X y‖ ≤ sparseNorm X k :=
  le_csSup (sparse_values_bdd X k) ⟨y, hy.mono le_rfl (Finset.subset_univ _), rfl⟩
theorem sparseNorm_le {X : ι → E} {k : ℕ} {B : ℝ}
    (h : ∀ y, Admissible k Finset.univ y → ‖synthesis X y‖ ≤ B) : sparseNorm X k ≤ B := by
  apply csSup_le (sparse_values_nonempty X k)
  rintro a ⟨y, hy, rfl⟩
  exact h y hy
theorem sparseNorm_mono (X : ι → E) {k l : ℕ} (hkl : k ≤ l) :
    sparseNorm X k ≤ sparseNorm X l :=
  sparseNorm_le (fun _ hy => synthesis_norm_le_sparseNorm (hy.mono hkl (Finset.Subset.refl _)))

theorem cross_values_bdd (X : ι → E) (k : ℕ) (I : Finset ι) :
    BddAbove {a : ℝ | ∃ y z : ι → ℝ,
      Admissible k I y ∧ Admissible k Iᶜ z ∧ a = |⟪synthesis X y, synthesis X z⟫_ℝ|} := by
  refine ⟨sparseNorm X k ^ 2, ?_⟩
  rintro a ⟨y, z, hy, hz, rfl⟩
  calc
    _ ≤ ‖synthesis X y‖ * ‖synthesis X z‖ := abs_real_inner_le_norm _ _
    _ ≤ sparseNorm X k * sparseNorm X k := mul_le_mul
      (synthesis_norm_le_sparseNorm hy) (synthesis_norm_le_sparseNorm hz)
      (norm_nonneg _) (sparseNorm_nonneg _ _)
    _ = _ := by ring
theorem cross_values_nonempty (X : ι → E) (k : ℕ) (I : Finset ι) :
    {a : ℝ | ∃ y z : ι → ℝ,
      Admissible k I y ∧ Admissible k Iᶜ z ∧ a = |⟪synthesis X y, synthesis X z⟫_ℝ|}.Nonempty :=
  ⟨0, 0, 0, admissible_zero _ _, admissible_zero _ _, by simp⟩
theorem crossNorm_nonneg (X : ι → E) (k : ℕ) (I : Finset ι) : 0 ≤ crossNorm X k I :=
  le_csSup (cross_values_bdd X k I) ⟨0, 0, admissible_zero _ _, admissible_zero _ _, by simp⟩
theorem abs_inner_le_crossNorm {X : ι → E} {k : ℕ} {I : Finset ι} {y z : ι → ℝ}
    (hy : Admissible k I y) (hz : Admissible k Iᶜ z) :
    |⟪synthesis X y, synthesis X z⟫_ℝ| ≤ crossNorm X k I :=
  le_csSup (cross_values_bdd X k I) ⟨y, z, hy, hz, rfl⟩
theorem crossNorm_le {X : ι → E} {k : ℕ} {I : Finset ι} {B : ℝ}
    (h : ∀ y z, Admissible k I y → Admissible k Iᶜ z →
      |⟪synthesis X y, synthesis X z⟫_ℝ| ≤ B) : crossNorm X k I ≤ B := by
  apply csSup_le (cross_values_nonempty X k I)
  rintro a ⟨y, z, hy, hz, rfl⟩
  exact h y z hy hz
theorem crossNorm_le_sparseNorm_sq (X : ι → E) (k : ℕ) (I : Finset ι) :
    crossNorm X k I ≤ sparseNorm X k ^ 2 := by
  apply crossNorm_le
  intro y z hy hz
  calc
    _ ≤ ‖synthesis X y‖ * ‖synthesis X z‖ := abs_real_inner_le_norm _ _
    _ ≤ sparseNorm X k * sparseNorm X k := mul_le_mul
      (synthesis_norm_le_sparseNorm hy) (synthesis_norm_le_sparseNorm hz)
      (norm_nonneg _) (sparseNorm_nonneg _ _)
    _ = _ := by ring
theorem crossNorm_mono (X : ι → E) {k l : ℕ} (hkl : k ≤ l) (I : Finset ι) :
    crossNorm X k I ≤ crossNorm X l I := by
  apply crossNorm_le
  intro y z hy hz
  exact abs_inner_le_crossNorm (hy.mono hkl (Finset.Subset.refl _))
    (hz.mono hkl (Finset.Subset.refl _))
theorem crossNorm_compl (X : ι → E) (k : ℕ) (I : Finset ι) :
    crossNorm X k Iᶜ = crossNorm X k I := by
  apply le_antisymm
  · apply crossNorm_le
    intro y z hy hz
    have hz' : Admissible k I z := by simpa using hz
    rw [real_inner_comm]
    exact abs_inner_le_crossNorm hz' hy
  · apply crossNorm_le
    intro y z hy hz
    have hy' : Admissible k Iᶜᶜ y := by simpa using hy
    rw [real_inner_comm]
    exact abs_inner_le_crossNorm hz hy'

/-- Homogeneous sparse synthesis bound, including the zero vector. -/
theorem synthesis_norm_le_sparseNorm_mul {X : ι → E} {k : ℕ} (y : ι → ℝ)
    (hy : (support y).card ≤ k) :
    ‖synthesis X y‖ ≤ coefficientNorm y * sparseNorm X k := by
  by_cases h0 : coefficientNorm y = 0
  · have : y = 0 := (coefficientNorm_eq_zero_iff y).mp h0
    simp [this]
  have hn : 0 < coefficientNorm y := lt_of_le_of_ne (coefficientNorm_nonneg y) (Ne.symm h0)
  let z := fun i => (coefficientNorm y)⁻¹ * y i
  have hz : Admissible k Finset.univ z := by
    refine ⟨?_, (Finset.card_le_card (support_smul_subset _ _)).trans hy, supported_univ _⟩
    simp [z, coefficientNorm_smul, abs_of_pos hn, h0]
  have h := synthesis_norm_le_sparseNorm (X := X) hz
  rw [show synthesis X z = (coefficientNorm y)⁻¹ • synthesis X y by
    exact synthesis_smul X _ y, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hn] at h
  exact (inv_mul_le_iff₀ hn).mp h

end
end TomographyOracleCore.Revision.SparseSampleSuprema
