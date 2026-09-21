import TomographyOracleCore.RelativeDesignTwoUnitaryGluing

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

/-!
# Reversing a relative completely-positive sandwich

This is the order-algebra step in Schuster--Haferkamp--Huang (B.22).
It turns a comparison of the exact Haar twirl with the approximate-Haar
reference into the orientation needed by the gluing iteration.
-/

/-- If `E` is within relative CP error `epsilon` of `H`, with
`epsilon ≤ 1/2`, then `H` is within error `epsilon / (1 - epsilon)` of
`E`.  Both maps are given as concrete completely-positive maps, so every
nonnegative rescaling used in the reversal remains completely positive. -/
theorem relativeCPApproximation_reverse
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (E H : A →CP A) (epsilon : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon ≤ 1 / 2)
    (h : RelativeCPApproximation epsilon E.toLinearMap H.toLinearMap) :
    RelativeCPApproximation (epsilon / (1 - epsilon))
      H.toLinearMap E.toLinearMap := by
  have hden : 0 < 1 - epsilon := by linarith
  have hplus : 0 < 1 + epsilon := by linarith
  have hinvDen0 : 0 ≤ (1 - epsilon)⁻¹ := (inv_pos.mpr hden).le
  have hinvPlus0 : 0 ≤ (1 + epsilon)⁻¹ := (inv_pos.mpr hplus).le
  have hlowerCoeff :
      1 - epsilon / (1 - epsilon) ≤ (1 + epsilon)⁻¹ := by
    rw [inv_eq_one_div]
    field_simp
    nlinarith [sq_nonneg epsilon]
  have hupperCoeff :
      (1 - epsilon)⁻¹ = 1 + epsilon / (1 - epsilon) := by
    rw [div_eq_mul_inv]
    field_simp
    ring
  constructor
  · have hscaled := h.upper.real_smul (1 + epsilon)⁻¹ hinvPlus0
    have hscaled' : CompletelyPositiveLE
        ((((1 + epsilon)⁻¹ : ℝ) : ℂ) • E.toLinearMap)
        H.toLinearMap := by
      convert hscaled using 1
      ext X
      simp only [LinearMap.smul_apply, smul_smul]
      push_cast
      rw [inv_mul_cancel₀]
      · simp
      · exact_mod_cast hplus.ne'
    exact (CompletelyPositiveLE.real_smul_mono E hlowerCoeff).trans hscaled'
  · have hscaled := h.lower.real_smul (1 - epsilon)⁻¹ hinvDen0
    have hscaled' : CompletelyPositiveLE H.toLinearMap
        ((((1 - epsilon)⁻¹ : ℝ) : ℂ) • E.toLinearMap) := by
      convert hscaled using 1
      ext X
      simp only [LinearMap.smul_apply, smul_smul]
      push_cast
      rw [inv_mul_cancel₀]
      · simp
      · exact_mod_cast hden.ne'
    simpa only [hupperCoeff] using hscaled'

end

end TomographyOracleCore
