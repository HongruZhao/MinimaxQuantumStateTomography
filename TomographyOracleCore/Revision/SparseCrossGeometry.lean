import TomographyOracleCore.Revision.SparseSampleSuprema

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseCrossGeometry

open SparseCoefficientGeometry SparseSampleSuprema
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem admissible_normalized {k : ℕ} {I : Finset ι} (y : ι → ℝ)
    (hy : (support y).card ≤ k) (hyI : Supported y I) :
    Admissible k I (fun i => (coefficientNorm y)⁻¹ * y i) :=
  ⟨coefficientNorm_normalized_le y,
    (Finset.card_le_card (support_smul_subset _ _)).trans hy, supported_smul _ hyI⟩

theorem abs_inner_le_crossNorm_homogeneous {X : ι → E} {k : ℕ} {I : Finset ι}
    (y z : ι → ℝ) (hy : (support y).card ≤ k) (hyI : Supported y I)
    (hz : (support z).card ≤ k) (hzI : Supported z Iᶜ) :
    |⟪synthesis X y, synthesis X z⟫_ℝ| ≤
      coefficientNorm y * coefficientNorm z * crossNorm X k I := by
  by_cases hy0 : coefficientNorm y = 0
  · have : y = 0 := (coefficientNorm_eq_zero_iff y).mp hy0
    simp [this]
  by_cases hz0 : coefficientNorm z = 0
  · have : z = 0 := (coefficientNorm_eq_zero_iff z).mp hz0
    simp [this]
  have h := abs_inner_le_crossNorm (X := X) (admissible_normalized y hy hyI)
    (admissible_normalized z hz hzI)
  rw [synthesis_smul, synthesis_smul, real_inner_smul_left, real_inner_smul_right,
    abs_mul, abs_mul, abs_inv, abs_inv,
    abs_of_nonneg (coefficientNorm_nonneg y), abs_of_nonneg (coefficientNorm_nonneg z)] at h
  have hny : 0 < coefficientNorm y := lt_of_le_of_ne (coefficientNorm_nonneg y) (Ne.symm hy0)
  have hnz : 0 < coefficientNorm z := lt_of_le_of_ne (coefficientNorm_nonneg z) (Ne.symm hz0)
  have h' := (inv_mul_le_iff₀ hny).mp h
  have h'' := (inv_mul_le_iff₀ hnz).mp h'
  nlinarith

/-- Duality for the restricted vector of sample correlations. -/
theorem restricted_correlations_norm_le {X : ι → E} {k : ℕ} {I : Finset ι}
    (y : ι → ℝ) (hy : (support y).card ≤ k) (hyI : Supported y I)
    (J : Finset ι) (hJ : J.card ≤ k) (hJI : J ⊆ Iᶜ) :
    coefficientNorm (restrict J (fun j => ⟪synthesis X y, X j⟫_ℝ)) ≤
      coefficientNorm y * crossNorm X k I := by
  let w := restrict J (fun j => ⟪synthesis X y, X j⟫_ℝ)
  have hwJ : Supported w J := supported_restrict _ _
  have hw : (support w).card ≤ k :=
    (Finset.card_le_card ((support_subset_iff _ _).mpr hwJ)).trans hJ
  have hwI : Supported w Iᶜ := by
    intro i hi
    exact hwJ i (fun h => hi (hJI h))
  by_cases h0 : coefficientNorm w = 0
  · change coefficientNorm w ≤ _
    rw [h0]
    exact mul_nonneg (coefficientNorm_nonneg _) (crossNorm_nonneg _ _ _)
  have hn : 0 < coefficientNorm w := lt_of_le_of_ne (coefficientNorm_nonneg w) (Ne.symm h0)
  let z := fun i => (coefficientNorm w)⁻¹ * w i
  have hz : Admissible k Iᶜ z := admissible_normalized w hw hwI
  have heq : ⟪synthesis X y, synthesis X z⟫_ℝ = coefficientNorm w := by
    rw [inner_synthesis_right]
    calc
      (∑ i, z i * ⟪synthesis X y, X i⟫_ℝ) =
          (coefficientNorm w)⁻¹ * ∑ i, w i ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [z, w]
        by_cases hij : i ∈ J <;> simp [restrict, hij] <;> ring
      _ = coefficientNorm w := by rw [← coefficientNorm_sq]; field_simp
  have h := abs_inner_le_crossNorm_homogeneous (X := X) y z hy hyI hz.2.1 hz.2.2
  rw [heq, abs_of_nonneg (coefficientNorm_nonneg w)] at h
  change coefficientNorm w ≤ _
  exact h.trans (by
    have := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hz.1 (coefficientNorm_nonneg y)) (crossNorm_nonneg X k I)
    simpa using this)

theorem admissible_sum_abs_le {k : ℕ} {I : Finset ι} {y : ι → ℝ}
    (hy : Admissible k I y) : (∑ i, |y i|) ≤ Real.sqrt (k : ℝ) := by
  calc
    _ ≤ Real.sqrt ((support y).card : ℝ) * coefficientNorm y := sum_abs_le_sqrt_card_mul_norm y
    _ ≤ Real.sqrt ((support y).card : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hy.1 (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (k : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hy.2.1)

end
end TomographyOracleCore.Revision.SparseCrossGeometry
