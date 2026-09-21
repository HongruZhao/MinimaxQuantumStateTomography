import TomographyOracleCore.Revision.BornFourthMoment

namespace TomographyOracleCore.Revision.BornMomentHomogeneity

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

variable {D : ℕ}

theorem integral_inner_norm_pow_smul
    (mu : Measure (EuclideanSpace ℂ (Fin D))) (p : ℕ)
    (u : EuclideanSpace ℂ (Fin D)) (c : ℝ) (hc : 0 ≤ c) :
    (∫ x, ‖⟪x, (c : ℂ) • u⟫_ℂ‖ ^ p ∂mu) =
      c ^ p * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ p ∂mu) := by
  simp_rw [inner_smul_right, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hc, mul_pow]
  exact integral_const_mul _ _

/-- Homogeneity extends a unit-direction estimate to every direction.
No concentration or moment assumption is involved. -/
theorem integral_inner_norm_pow_bounds_of_unit
    (mu : Measure (EuclideanSpace ℂ (Fin D))) (p : ℕ) (hp : 0 < p)
    (lower upper : ℝ)
    (hunit : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      lower ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ p ∂mu) ∧
        (∫ x, ‖⟪x, u⟫_ℂ‖ ^ p ∂mu) ≤ upper)
    (u : EuclideanSpace ℂ (Fin D)) :
    lower * ‖u‖ ^ p ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ p ∂mu) ∧
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ p ∂mu) ≤ upper * ‖u‖ ^ p := by
  by_cases hu0 : u = 0
  · subst u
    simp [Nat.ne_of_gt hp]
  have hn0 : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  let v : EuclideanSpace ℂ (Fin D) := ((‖u‖⁻¹ : ℝ) : ℂ) • u
  have hv : ‖v‖ = 1 := by
    simp [v, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), hn0]
  have huv : (‖u‖ : ℂ) • v = u := by
    simp [v, smul_smul, ← Complex.ofReal_mul, hn0]
  have hs : (∫ x, ‖⟪x, u⟫_ℂ‖ ^ p ∂mu) =
      ‖u‖ ^ p * (∫ x, ‖⟪x, v⟫_ℂ‖ ^ p ∂mu) := by
    nth_rewrite 1 [← huv]
    exact integral_inner_norm_pow_smul mu p v ‖u‖ (norm_nonneg u)
  rw [hs]
  obtain ⟨hl, hh⟩ := hunit v hv
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hl (pow_nonneg (norm_nonneg u) p)
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (pow_nonneg (norm_nonneg u) p)

end

end TomographyOracleCore.Revision.BornMomentHomogeneity
