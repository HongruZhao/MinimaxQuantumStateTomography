import TomographyOracleCore.Candidate2PeakyMomentControl

/-!
# Deterministic Lipschitz control of the clipped spread process

This file proves the deterministic approximation step needed before a finite
net can be used on the clipped part of the Candidate 2 covariance process.
The scalar clipping map is a contraction.  Consequently, on a sample whose
squared norms are bounded by `q`, the centered clipped directional process is
Lipschitz on the unit sphere with constant

`2 * (q + ‖populationCovariance mu‖)`.

The final theorem transfers a bound from a nearby unit direction to an
arbitrary unit direction.  It does not construct a net and does not prove the
remaining probabilistic maximum bound on the net.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

/-- The clipping function is the usual projection of the real line onto
`[-1, 1]`. -/
theorem clippedPsi_eq_max_min (x : ℝ) :
    clippedPsi x = max (-1) (min x 1) := by
  by_cases hleft : x < -1
  · rw [clippedPsi, if_pos hleft, min_eq_left (by linarith),
      max_eq_left hleft.le]
  · by_cases hright : 1 < x
    · rw [clippedPsi, if_neg hleft, if_pos hright,
        min_eq_right hright.le]
      norm_num
    · rw [clippedPsi, if_neg hleft, if_neg hright,
        min_eq_left (not_lt.mp hright), max_eq_right (not_lt.mp hleft)]

/-- Scalar clipping is a contraction for the absolute-value metric. -/
theorem abs_clippedPsi_sub_clippedPsi_le (a b : ℝ) :
    |clippedPsi a - clippedPsi b| ≤ |a - b| := by
  rw [clippedPsi_eq_max_min, clippedPsi_eq_max_min,
    max_comm (-1), max_comm (-1)]
  calc
    |max (min a 1) (-1) - max (min b 1) (-1)| ≤
        |min a 1 - min b 1| :=
      abs_max_sub_max_le_abs _ _ _
    _ ≤ |a - b| := by
      simpa using (abs_min_sub_min_le_max a 1 b 1)

/-- After the inverse-threshold rescaling, the clipped spread contribution is
still a contraction in its nonnegative scalar observation (in fact the proof
works for arbitrary real observations). -/
theorem abs_clippedSpread_sub_clippedSpread_le
    {lambda : ℝ} (hlambda : 0 < lambda) (a b : ℝ) :
    |clippedSpread lambda a - clippedSpread lambda b| ≤ |a - b| := by
  unfold clippedSpread
  rw [← mul_sub, abs_mul]
  calc
    |lambda⁻¹| * |clippedPsi (lambda * a) - clippedPsi (lambda * b)| ≤
        |lambda⁻¹| * |lambda * a - lambda * b| :=
      mul_le_mul_of_nonneg_left
        (abs_clippedPsi_sub_clippedPsi_le (lambda * a) (lambda * b))
        (abs_nonneg _)
    _ = |a - b| := by
      rw [abs_inv, abs_of_pos hlambda, ← mul_sub, abs_mul,
        abs_of_pos hlambda, ← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]

/-- Averaging clipped observations is contractive for the empirical `L1`
distance. -/
theorem abs_spreadMean_sub_spreadMean_le_empiricalMean_abs_sub
    {T : ℕ} {lambda : ℝ} (hlambda : 0 < lambda)
    (y z : Fin T → ℝ) :
    |spreadMean lambda y - spreadMean lambda z| ≤
      empiricalMean (fun i ↦ |y i - z i|) := by
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  unfold spreadMean empiricalMean
  rw [← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg hweight]
  calc
    (T : ℝ)⁻¹ * |∑ i, (clippedSpread lambda (y i) -
        clippedSpread lambda (z i))| ≤
        (T : ℝ)⁻¹ * ∑ i,
          |clippedSpread lambda (y i) - clippedSpread lambda (z i)| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.abs_sum_le_sum_abs _ _) hweight
    _ ≤ (T : ℝ)⁻¹ * ∑ i, |y i - z i| := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦
          abs_clippedSpread_sub_clippedSpread_le hlambda (y i) (z i))
        hweight

section Directional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared real marginals vary quadratically in the sample vector and
linearly in the distance between two directions. -/
theorem abs_sq_inner_sub_sq_inner_le
    (x u v : E) :
    |⟪x, u⟫_ℝ ^ 2 - ⟪x, v⟫_ℝ ^ 2| ≤
      ‖x‖ ^ 2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by
  have hsum : |⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ| ≤
      ‖x‖ * (‖u‖ + ‖v‖) := by
    calc
      |⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ| ≤
          |⟪x, u⟫_ℝ| + |⟪x, v⟫_ℝ| := abs_add_le _ _
      _ ≤ ‖x‖ * ‖u‖ + ‖x‖ * ‖v‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
      _ = ‖x‖ * (‖u‖ + ‖v‖) := by ring
  have hdiff : |⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ| ≤
      ‖x‖ * ‖u - v‖ := by
    rw [← inner_sub_right]
    exact abs_real_inner_le_norm _ _
  rw [sq_sub_sq, abs_mul]
  calc
    |⟪x, u⟫_ℝ + ⟪x, v⟫_ℝ| *
        |⟪x, u⟫_ℝ - ⟪x, v⟫_ℝ| ≤
        (‖x‖ * (‖u‖ + ‖v‖)) * (‖x‖ * ‖u - v‖) := by
      exact mul_le_mul hsum hdiff (abs_nonneg _) (by positivity)
    _ = ‖x‖ ^ 2 * (‖u‖ + ‖v‖) * ‖u - v‖ := by ring

/-- On the unit sphere and for a vector of squared norm at most `q`, squared
marginals are `2q`-Lipschitz. -/
theorem abs_sq_inner_sub_sq_inner_le_of_unit
    {q : ℝ} {x u v : E} (hx : ‖x‖ ^ 2 ≤ q)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |⟪x, u⟫_ℝ ^ 2 - ⟪x, v⟫_ℝ ^ 2| ≤
      2 * q * ‖u - v‖ := by
  calc
    |⟪x, u⟫_ℝ ^ 2 - ⟪x, v⟫_ℝ ^ 2| ≤
        ‖x‖ ^ 2 * (‖u‖ + ‖v‖) * ‖u - v‖ :=
      abs_sq_inner_sub_sq_inner_le x u v
    _ = 2 * ‖x‖ ^ 2 * ‖u - v‖ := by rw [hu, hv]; ring
    _ ≤ 2 * q * ‖u - v‖ := by
      gcongr

/-- The empirical clipped directional process is `2q`-Lipschitz on the unit
sphere when all sample vectors have squared norm at most `q`. -/
theorem abs_directionalSpreadMean_sub_directionalSpreadMean_le
    {T : ℕ} (hT : 0 < T) {q lambda : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (hX : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |directionalSpreadMean lambda X u -
        directionalSpreadMean lambda X v| ≤
      2 * q * ‖u - v‖ := by
  have hcontract :=
    abs_spreadMean_sub_spreadMean_le_empiricalMean_abs_sub
      (T := T) hlambda (directionalSquares X u) (directionalSquares X v)
  calc
    |directionalSpreadMean lambda X u -
        directionalSpreadMean lambda X v| ≤
        empiricalMean (fun i ↦
          |directionalSquares X u i - directionalSquares X v i|) := by
      simpa only [directionalSpreadMean] using hcontract
    _ ≤ empiricalMean (fun _i : Fin T ↦ 2 * q * ‖u - v‖) := by
      unfold empiricalMean
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦ by
          simpa only [directionalSquares] using
            abs_sq_inner_sub_sq_inner_le_of_unit (hX i) hu hv)
        (inv_nonneg.mpr (Nat.cast_nonneg T))
    _ = 2 * q * ‖u - v‖ := by
      simp [empiricalMean, hT.ne']

/-- Quadratic forms of a bounded operator are `2 ‖A‖`-Lipschitz on the unit
sphere.  No self-adjointness assumption is needed for this estimate. -/
theorem abs_inner_apply_self_sub_inner_apply_self_le_of_unit
    (A : E →L[ℝ] E) (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |⟪A u, u⟫_ℝ - ⟪A v, v⟫_ℝ| ≤
      2 * ‖A‖ * ‖u - v‖ := by
  have hid :
      ⟪A u, u⟫_ℝ - ⟪A v, v⟫_ℝ =
        ⟪A (u - v), u⟫_ℝ + ⟪A v, u - v⟫_ℝ := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    |⟪A (u - v), u⟫_ℝ + ⟪A v, u - v⟫_ℝ| ≤
        |⟪A (u - v), u⟫_ℝ| + |⟪A v, u - v⟫_ℝ| :=
      abs_add_le _ _
    _ ≤ ‖A (u - v)‖ * ‖u‖ + ‖A v‖ * ‖u - v‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (‖A‖ * ‖u - v‖) * ‖u‖ +
        (‖A‖ * ‖v‖) * ‖u - v‖ := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (A.le_opNorm (u - v)) (norm_nonneg u))
        (mul_le_mul_of_nonneg_right (A.le_opNorm v) (norm_nonneg (u - v)))
    _ = 2 * ‖A‖ * ‖u - v‖ := by rw [hu, hv]; ring

/-- The centered clipped spread process used in the covariance decomposition. -/
def centeredDirectionalSpread
    [MeasurableSpace E] [BorelSpace E]
    (mu : Measure E) {T : ℕ} (lambda : ℝ)
    (X : Fin T → E) (u : E) : ℝ :=
  directionalSpreadMean lambda X u - ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu

/-- Deterministic Lipschitz control of the centered clipped spread process on
the unit sphere. -/
theorem abs_centeredDirectionalSpread_sub_le
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu)
    {T : ℕ} (hT : 0 < T) {q lambda : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (hX : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |centeredDirectionalSpread mu lambda X u -
        centeredDirectionalSpread mu lambda X v| ≤
      2 * (q + ‖populationCovariance mu‖) * ‖u - v‖ := by
  have hsample :=
    abs_directionalSpreadMean_sub_directionalSpreadMean_le
      hT hlambda X hX u v hu hv
  have hpopulation :
      |(∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) - ∫ x, ⟪x, v⟫_ℝ ^ 2 ∂mu| ≤
        2 * ‖populationCovariance mu‖ * ‖u - v‖ := by
    rw [← inner_populationCovariance_apply_self_eq_integral_sq hmu,
      ← inner_populationCovariance_apply_self_eq_integral_sq hmu]
    exact abs_inner_apply_self_sub_inner_apply_self_le_of_unit
      (populationCovariance mu) u v hu hv
  unfold centeredDirectionalSpread
  calc
    |(directionalSpreadMean lambda X u - ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) -
        (directionalSpreadMean lambda X v - ∫ x, ⟪x, v⟫_ℝ ^ 2 ∂mu)| =
        |(directionalSpreadMean lambda X u - directionalSpreadMean lambda X v) -
          ((∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) - ∫ x, ⟪x, v⟫_ℝ ^ 2 ∂mu)| := by
      congr 1
      ring
    _ ≤ |directionalSpreadMean lambda X u - directionalSpreadMean lambda X v| +
        |(∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) - ∫ x, ⟪x, v⟫_ℝ ^ 2 ∂mu| :=
      abs_sub _ _
    _ ≤ 2 * q * ‖u - v‖ +
        2 * ‖populationCovariance mu‖ * ‖u - v‖ := add_le_add hsample hpopulation
    _ = 2 * (q + ‖populationCovariance mu‖) * ‖u - v‖ := by ring

/-- One-point finite-net transfer: controlling the centered spread process at
a nearby unit direction controls it at the original unit direction, with the
explicit deterministic approximation penalty. -/
theorem abs_centeredDirectionalSpread_le_of_nearby_unit
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu)
    {T : ℕ} (hT : 0 < T) {q lambda eta : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (hX : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (huv : ‖u - v‖ ≤ eta) :
    |centeredDirectionalSpread mu lambda X u| ≤
      |centeredDirectionalSpread mu lambda X v| +
        2 * (q + ‖populationCovariance mu‖) * eta := by
  have hlip := abs_centeredDirectionalSpread_sub_le
    hmu hT hlambda X hX u v hu hv
  let i0 : Fin T := ⟨0, hT⟩
  have hq : 0 ≤ q :=
    le_trans (sq_nonneg ‖X i0‖) (hX i0)
  calc
    |centeredDirectionalSpread mu lambda X u| ≤
        |centeredDirectionalSpread mu lambda X v| +
          |centeredDirectionalSpread mu lambda X u -
            centeredDirectionalSpread mu lambda X v| := by
      calc
        |centeredDirectionalSpread mu lambda X u| =
            |centeredDirectionalSpread mu lambda X v +
              (centeredDirectionalSpread mu lambda X u -
                centeredDirectionalSpread mu lambda X v)| := by
          congr 1
          ring
        _ ≤ |centeredDirectionalSpread mu lambda X v| +
            |centeredDirectionalSpread mu lambda X u -
              centeredDirectionalSpread mu lambda X v| := abs_add_le _ _
    _ ≤ |centeredDirectionalSpread mu lambda X v| +
        2 * (q + ‖populationCovariance mu‖) * ‖u - v‖ :=
      add_le_add_right hlip _
    _ ≤ |centeredDirectionalSpread mu lambda X v| +
        2 * (q + ‖populationCovariance mu‖) * eta := by
      gcongr

end Directional

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
