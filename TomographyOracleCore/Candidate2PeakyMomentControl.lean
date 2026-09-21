import TomographyOracleCore.Candidate2PeakySpreadDecomposition

/-!
# Sixth-moment control of the peaky covariance term

This module records the elementary pointwise step that turns the peaky part
of the Abdalla--Zhivotovskiy decomposition into a sixth marginal moment.  It
does not assert the remaining uniform probabilistic supremum estimate.
-/

open InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

/-- Below the truncation threshold, the peaky contribution vanishes. -/
theorem peakyTerm_eq_zero_of_le_one
    {lambda y : ℝ} (h : lambda * y ≤ 1) :
    peakyTerm lambda y = 0 := by
  rw [peakyTerm, if_neg (not_lt.mpr h)]

/-- The peaky contribution is bounded by the cubic observation with the
exact `lambda^2` factor.  For covariance observations `y = <X,u>^2`, this is
precisely a sixth-moment envelope. -/
theorem peakyTerm_le_lambda_sq_mul_cube
    {lambda y : ℝ} (hlambda : 0 < lambda) (hy : 0 ≤ y) :
    peakyTerm lambda y ≤ lambda ^ 2 * y ^ 3 := by
  by_cases htail : 1 < lambda * y
  · rw [peakyTerm, if_pos htail]
    have hprod : 0 ≤ lambda * y := mul_nonneg hlambda.le hy
    have hsquare : 1 ≤ (lambda * y) ^ 2 := by nlinarith
    calc
      y = y * 1 := by ring
      _ ≤ y * (lambda * y) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare hy
      _ = lambda ^ 2 * y ^ 3 := by ring
  · rw [peakyTerm, if_neg htail]
    positivity

/-- Finite-sample peaky mean is controlled by the empirical cubic moment. -/
theorem peakyMean_le_lambda_sq_mul_empiricalCube
    {T : ℕ} {lambda : ℝ} {y : Fin T → ℝ}
    (hlambda : 0 < lambda) (hy : ∀ i, 0 ≤ y i) :
    peakyMean lambda y ≤
      lambda ^ 2 * empiricalMean (fun i ↦ y i ^ 3) := by
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  unfold peakyMean empiricalMean
  calc
    (T : ℝ)⁻¹ * ∑ i, peakyTerm lambda (y i) ≤
        (T : ℝ)⁻¹ * ∑ i, lambda ^ 2 * y i ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦
          peakyTerm_le_lambda_sq_mul_cube hlambda (hy i)) hweight
    _ = lambda ^ 2 * ((T : ℝ)⁻¹ * ∑ i, y i ^ 3) := by
      rw [← Finset.mul_sum]
      ring

/-- Directional covariance specialization: the peaky term is bounded by the
empirical sixth absolute marginal moment. -/
theorem directionalPeakyMean_le_empiricalSixthMoment
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {T : ℕ} {lambda : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (u : E) :
    directionalPeakyMean lambda X u ≤
      lambda ^ 2 * empiricalMean (fun i ↦ |⟪X i, u⟫_ℝ| ^ 6) := by
  have h := peakyMean_le_lambda_sq_mul_empiricalCube
    (T := T) (lambda := lambda)
    (y := directionalSquares X u) hlambda
    (directionalSquares_nonneg X u)
  calc
    directionalPeakyMean lambda X u ≤
        lambda ^ 2 * empiricalMean
          (fun i ↦ (⟪X i, u⟫_ℝ ^ 2) ^ 3) := by
      simpa only [directionalPeakyMean, directionalSquares] using h
    _ = lambda ^ 2 * empiricalMean
        (fun i ↦ |⟪X i, u⟫_ℝ| ^ 6) := by
      congr 2
      funext i
      have habs : |⟪X i, u⟫_ℝ| ^ 6 = ⟪X i, u⟫_ℝ ^ 6 := by
        rw [← abs_pow]
        exact abs_of_nonneg (by positivity)
      rw [habs]
      ring

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
