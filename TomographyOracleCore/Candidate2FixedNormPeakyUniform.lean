import TomographyOracleCore.Candidate2PeakyMomentControl

/-!
# Deterministic fixed-norm control of the peaky covariance process

This file supplies a fully uniform fallback for the peaky half of the
Candidate-2 covariance decomposition.  If every observed vector has squared
norm at most `q`, then every unit-direction empirical sixth moment is at most
`q^3`; consequently the peaky term is at most `lambda^2 * q^3`.

The bound is elementary and dimension dependent when `q` grows with the
ambient dimension.  It is therefore not presented as the final sharp
effective-rank estimate.
-/

open InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Under a uniform squared-norm cap, every unit-direction empirical sixth
moment is bounded by the cube of that cap. -/
theorem empiricalMean_abs_inner_sixth_le_cube_of_norm_sq_le
    {T : ℕ} (hT : 0 < T) {q : ℝ}
    (X : Fin T → E) (hnorm : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u : E) (hu : ‖u‖ = 1) :
    empiricalMean (fun i ↦ |⟪X i, u⟫_ℝ| ^ 6) ≤ q ^ 3 := by
  have hpoint : ∀ i : Fin T, |⟪X i, u⟫_ℝ| ^ 6 ≤ q ^ 3 := by
    intro i
    have hinner : |⟪X i, u⟫_ℝ| ≤ ‖X i‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    have hinnerSq : |⟪X i, u⟫_ℝ| ^ 2 ≤ q := by
      calc
        |⟪X i, u⟫_ℝ| ^ 2 ≤ (‖X i‖ * ‖u‖) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hinner 2
        _ = ‖X i‖ ^ 2 := by rw [hu]; ring
        _ ≤ q := hnorm i
    calc
      |⟪X i, u⟫_ℝ| ^ 6 = (|⟪X i, u⟫_ℝ| ^ 2) ^ 3 := by ring
      _ ≤ q ^ 3 :=
        pow_le_pow_left₀ (sq_nonneg |⟪X i, u⟫_ℝ|) hinnerSq 3
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  unfold empiricalMean
  calc
    (T : ℝ)⁻¹ * ∑ i, |⟪X i, u⟫_ℝ| ^ 6 ≤
        (T : ℝ)⁻¹ * ∑ _i : Fin T, q ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _hi ↦ hpoint i) hweight
    _ = q ^ 3 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne']

/-- Uniform deterministic control of the directional peaky process under a
sample norm cap. -/
theorem directionalPeakyMean_le_lambda_sq_mul_cube_of_norm_sq_le
    {T : ℕ} (hT : 0 < T) {lambda q : ℝ}
    (hlambda : 0 < lambda)
    (X : Fin T → E) (hnorm : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u : E) (hu : ‖u‖ = 1) :
    directionalPeakyMean lambda X u ≤ lambda ^ 2 * q ^ 3 := by
  calc
    directionalPeakyMean lambda X u ≤
        lambda ^ 2 * empiricalMean (fun i ↦ |⟪X i, u⟫_ℝ| ^ 6) :=
      directionalPeakyMean_le_empiricalSixthMoment hlambda X u
    _ ≤ lambda ^ 2 * q ^ 3 :=
      mul_le_mul_of_nonneg_left
        (empiricalMean_abs_inner_sixth_le_cube_of_norm_sq_le
          hT X hnorm u hu)
        (sq_nonneg lambda)

/-- Fixed-norm specialization of the deterministic peaky--spread covariance
decomposition.  This is a complete fallback inequality, not the sharper
effective-rank concentration endpoint. -/
theorem abs_covarianceError_rayleighQuotient_le_fixedNormPeaky_add_spread
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : MeasureTheory.Measure E} (hmu : MeasureTheory.MemLp id 2 mu)
    {T : ℕ} (hT : 0 < T) (X : Fin T → E)
    {lambda q : ℝ} (hlambda : 0 < lambda)
    (hnorm : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u : E) (hu : ‖u‖ = 1) :
    |(sampleCovariance X - populationCovariance mu).rayleighQuotient u| ≤
      lambda ^ 2 * q ^ 3 +
        |directionalSpreadMean lambda X u -
          ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu| := by
  have hdecomp :=
    abs_covarianceError_rayleighQuotient_le_peaky_add_spread_of_norm_eq_one
      hmu X u hu hlambda
  have hpeaky :=
    directionalPeakyMean_le_lambda_sq_mul_cube_of_norm_sq_le
      hT hlambda X hnorm u hu
  linarith

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
