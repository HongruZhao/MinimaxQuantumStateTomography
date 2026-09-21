import TomographyOracleCore.Revision.SparseUniformEnergy

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseDirectionalEnergy

open SparseCoefficientGeometry SparseSampleSuprema
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Duality turns the sparse synthesis norm into a bound for every restricted
directional energy. -/
theorem directional_energy_le_sparseNorm_sq (X : ι → E) (I : Finset ι) (u : E) (hu : ‖u‖ ≤ 1) :
    (∑ i ∈ I, ⟪X i, u⟫_ℝ ^ 2) ≤ sparseNorm X I.card ^ 2 := by
  let w := restrict I (fun i => ⟪X i, u⟫_ℝ)
  have hwc : (support w).card ≤ I.card :=
    Finset.card_le_card ((support_subset_iff _ _).mpr (supported_restrict I _))
  have hw2 : coefficientNorm w ^ 2 = ∑ i ∈ I, ⟪X i, u⟫_ℝ ^ 2 := coefficientNorm_restrict_sq _ _
  have heq : ⟪synthesis X w, u⟫_ℝ = coefficientNorm w ^ 2 := by
    rw [inner_synthesis_left, coefficientNorm_sq]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [w]
    by_cases hiI : i ∈ I <;> simp [restrict, hiI] <;> ring
  have hn := synthesis_norm_le_sparseNorm_mul (X := X) w hwc
  have hi := (le_abs_self ⟪synthesis X w, u⟫_ℝ).trans (abs_real_inner_le_norm _ _)
  have hmul := mul_le_mul_of_nonneg_left hu (norm_nonneg (synthesis X w))
  rw [heq] at hi
  have hc : coefficientNorm w ^ 2 ≤ coefficientNorm w * sparseNorm X I.card := by nlinarith
  have hcn : 0 ≤ coefficientNorm w := coefficientNorm_nonneg _
  have hsn := sparseNorm_nonneg X I.card
  have hle : coefficientNorm w ≤ sparseNorm X I.card := by
    by_cases hw0 : coefficientNorm w = 0
    · rw [hw0]; exact hsn
    have hwp : 0 < coefficientNorm w := lt_of_le_of_ne hcn (Ne.symm hw0)
    have hmul' : coefficientNorm w * coefficientNorm w ≤ coefficientNorm w * sparseNorm X I.card := by nlinarith
    exact (mul_le_mul_iff_right₀ hwp).mp hmul'
  rw [← hw2]
  exact (sq_le_sq₀ hcn hsn).mpr hle

end
end TomographyOracleCore.Revision.SparseDirectionalEnergy
