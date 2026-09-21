import TomographyOracleCore.ExactTargets

namespace TomographyOracleCore

/-!
# Scaling the sampling decay rate by a noise constant

This file proves the deterministic rate comparison needed after a physical
raw-estimator theorem has bounded its effective noise by
`C * sqrt (D / T)`.  It contains no measurement, moment, estimator, or risk
assumption.

No declaration in this file is an axiom.
-/

open scoped ENNReal

/-- For an exponent in `[0,1]`, scaling a nonnegative base by `C` costs at
most `max 1 C`. -/
theorem rpow_le_max_one_self
    (C q : ℝ) (hC : 0 ≤ C) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    C ^ q ≤ max 1 C := by
  by_cases hC1 : C ≤ 1
  · exact (Real.rpow_le_one hC hC1 hq0).trans (le_max_left 1 C)
  · have hOneC : 1 ≤ C := le_of_not_ge hC1
    exact (Real.rpow_le_self_of_one_le hOneC hq1).trans
      (le_max_right 1 C)

/-- Explicit sampling-rate comparison for a constant multiple of the
canonical noise scale.  The factor `max 1 C` simultaneously controls the
loss cap, the fractional-power regime, and the full-rank regime. -/
theorem decayUpperRate_const_mul_sqrt_le_spectralDecayMinimaxRate
    (D : ℕ) (T L alpha C : ℝ)
    (hD : 1 ≤ D) (hT : 0 < T) (hL : 1 ≤ L)
    (halpha : 1 < alpha) (hC : 0 ≤ C) :
    decayUpperRate D L
        (C * Real.sqrt ((D : ℝ) / T)) alpha ≤
      max 1 C * spectralDecayMinimaxRate D T L alpha := by
  let eta : ℝ := Real.sqrt ((D : ℝ) / T)
  let q : ℝ := (alpha - 1) / alpha
  let K : ℝ := max 1 C
  have hDReal : 0 < (D : ℝ) := by exact_mod_cast hD
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (div_le_one halpha0).2 (by linarith)
  have hetaPos : 0 < eta := by
    dsimp [eta]
    exact Real.sqrt_pos.2 (div_pos hDReal hT)
  have heta : 0 ≤ eta := hetaPos.le
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact le_trans zero_le_one (le_max_left 1 C)
  have hK1 : 1 ≤ K := by
    dsimp [K]
    exact le_max_left 1 C
  have hCK : C ≤ K := by
    dsimp [K]
    exact le_max_right 1 C
  have hCpow : C ^ q ≤ K := by
    dsimp [K]
    exact rpow_le_max_one_self C q hC hq0 hq1
  have hLpow : 0 ≤ L ^ alpha⁻¹ :=
    Real.rpow_nonneg (le_trans zero_le_one hL) _
  have hetaPow : 0 ≤ eta ^ q := Real.rpow_nonneg heta _
  have hpoly :
      L ^ alpha⁻¹ * (C * eta) ^ q ≤
        K * (L ^ alpha⁻¹ * eta ^ q) := by
    rw [Real.mul_rpow hC heta]
    calc
      L ^ alpha⁻¹ * (C ^ q * eta ^ q) =
          C ^ q * (L ^ alpha⁻¹ * eta ^ q) := by ring
      _ ≤ K * (L ^ alpha⁻¹ * eta ^ q) :=
        mul_le_mul_of_nonneg_right hCpow (mul_nonneg hLpow hetaPow)
  have hendpoint :
      (C * eta) * (D : ℝ) ≤ K * (eta * (D : ℝ)) := by
    calc
      (C * eta) * (D : ℝ) = C * (eta * (D : ℝ)) := by ring
      _ ≤ K * (eta * (D : ℝ)) :=
        mul_le_mul_of_nonneg_right hCK
          (mul_nonneg heta (Nat.cast_nonneg D))
  rw [spectralDecayMinimaxRate,
    ← decayUpperRate_sqrt_dimension_div_samples D T L alpha hT
      halpha0.ne']
  change decayUpperRate D L (C * eta) alpha ≤
    K * decayUpperRate D L eta alpha
  unfold decayUpperRate
  rw [mul_min_of_nonneg _ _ hK0, mul_min_of_nonneg _ _ hK0]
  simp only [mul_one]
  exact min_le_min hK1 (min_le_min hpoly hendpoint)

/-- `ENNReal.ofReal` form of the sampling-rate comparison, including the
factor `12` produced by the deterministic decay-oracle theorem. -/
theorem ofReal_twelve_decayUpperRate_const_mul_sqrt_le
    (D : ℕ) (T L alpha C : ℝ)
    (hD : 1 ≤ D) (hT : 0 < T) (hL : 1 ≤ L)
    (halpha : 1 < alpha) (hC : 0 ≤ C) :
    ENNReal.ofReal
        (12 * decayUpperRate D L
          (C * Real.sqrt ((D : ℝ) / T)) alpha) ≤
      ENNReal.ofReal
        (12 * max 1 C * spectralDecayMinimaxRate D T L alpha) := by
  apply ENNReal.ofReal_le_ofReal
  calc
    12 * decayUpperRate D L
        (C * Real.sqrt ((D : ℝ) / T)) alpha ≤
      12 * (max 1 C * spectralDecayMinimaxRate D T L alpha) :=
        mul_le_mul_of_nonneg_left
          (decayUpperRate_const_mul_sqrt_le_spectralDecayMinimaxRate
            D T L alpha C hD hT hL halpha hC)
          (by norm_num)
    _ = 12 * max 1 C * spectralDecayMinimaxRate D T L alpha := by ring

end TomographyOracleCore
