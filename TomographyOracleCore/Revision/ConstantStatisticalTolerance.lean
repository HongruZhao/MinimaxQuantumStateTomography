import TomographyOracleCore.Revision.ConstantDimensionSchedule
import TomographyOracleCore.Revision.MatrixSolverInexactSampleSchedule
import Mathlib.Data.Nat.Sqrt
namespace TomographyOracleCore.Revision.MatrixSolver
set_option maxHeartbeats 1000000

/-- The integer ceiling of sqrt(S/D), using only integer arithmetic. -/
def integerSqrtRatioCeil (D S : ℕ) : ℕ := Nat.sqrt ((S - 1) / D) + 1

theorem integerSqrtRatioCeil_covers {D S : ℕ} (hD : 0 < D) (hS : 0 < S) :
    S ≤ D * integerSqrtRatioCeil D S ^ 2 := by
  have hs := Nat.lt_succ_sqrt' ((S - 1) / D)
  change (S - 1) / D < integerSqrtRatioCeil D S ^ 2 at hs
  have hm := Nat.mul_le_mul_left D (Nat.succ_le_of_lt hs)
  rw [Nat.mul_succ] at hm
  have he := Nat.div_add_mod (S - 1) D
  have hr := Nat.mod_lt (S - 1) hD
  omega

theorem integerSqrtRatioCeil_le_iff {D S k : ℕ} (hD : 0 < D) (hS : 0 < S) :
    integerSqrtRatioCeil D S ≤ k ↔ S ≤ D * k ^ 2 := by
  constructor
  · intro hk
    exact (integerSqrtRatioCeil_covers hD hS).trans
      (Nat.mul_le_mul_left D (Nat.pow_le_pow_left hk 2))
  · intro hcover
    have hq : (S - 1) / D < k ^ 2 := by
      by_contra hn
      have hge : k ^ 2 ≤ (S - 1) / D := by omega
      have hm := Nat.mul_le_mul_left D hge
      have hd := Nat.mul_div_le (S - 1) D
      omega
    have hs := Nat.sqrt_lt'.mpr hq
    unfold integerSqrtRatioCeil
    omega

/-- A fixed numerator 64 keeps rational rounding close to statistical accuracy. -/
def statisticalToleranceDenominator (D T : ℕ) : ℕ :=
  max 64 (integerSqrtRatioCeil D (4096 * T))

def statisticalRationalTolerance (D T : ℕ) : ℚ :=
  64 / (statisticalToleranceDenominator D T : ℚ)

theorem statisticalToleranceDenominator_ge (D T : ℕ) :
    64 ≤ statisticalToleranceDenominator D T := le_max_left _ _

theorem statisticalToleranceDenominator_pos (D T : ℕ) :
    0 < statisticalToleranceDenominator D T := by
  have := statisticalToleranceDenominator_ge D T
  omega

theorem statisticalRationalTolerance_pos (D T : ℕ) :
    0 < statisticalRationalTolerance D T := by
  unfold statisticalRationalTolerance
  have := statisticalToleranceDenominator_pos D T
  positivity

theorem statisticalRationalTolerance_le_one (D T : ℕ) :
    statisticalRationalTolerance D T ≤ 1 := by
  apply (div_le_one₀ (by exact_mod_cast statisticalToleranceDenominator_pos D T)).mpr
  exact_mod_cast statisticalToleranceDenominator_ge D T

/-- Exact optimality within the rational family 64/k: the denominator is minimal. -/
theorem statisticalToleranceDenominator_le_iff {D T k : ℕ}
    (hD : 0 < D) (hT : 0 < T) :
    statisticalToleranceDenominator D T ≤ k ↔ 64 ≤ k ∧ 4096 * T ≤ D * k ^ 2 := by
  rw [statisticalToleranceDenominator, max_le_iff,
    integerSqrtRatioCeil_le_iff hD (by omega)]

theorem statisticalToleranceDenominator_covers {D T : ℕ} (hD : 0 < D) (hT : 0 < T) :
    4096 * T ≤ D * statisticalToleranceDenominator D T ^ 2 :=
  ((statisticalToleranceDenominator_le_iff hD hT).mp le_rfl).2

/-- Squared inverse tolerance costs at most (65/64)^2 after rational rounding. -/
theorem statisticalToleranceDenominator_budget {D T : ℕ} :
    D * statisticalToleranceDenominator D T ^ 2 ≤ 4225 * max D T := by
  let m := Nat.sqrt ((4096 * T - 1) / D)
  have hm := Nat.sqrt_le' ((4096 * T - 1) / D)
  change m ^ 2 ≤ (4096 * T - 1) / D at hm
  change D * (max 64 (m + 1)) ^ 2 ≤ _
  by_cases hm64 : m < 64
  · rw [max_eq_left (by omega : m + 1 ≤ 64)]
    have := le_max_left D T
    nlinarith
  · rw [max_eq_right (by omega : 64 ≤ m + 1)]
    have hmsq := Nat.mul_le_mul_left m (show 64 ≤ m by omega)
    have hround : 4096 * (m + 1) ^ 2 ≤ 4225 * m ^ 2 := by nlinarith
    have hroundD := Nat.mul_le_mul_left D hround
    have hmD := Nat.mul_le_mul_left D hm
    have hdiv := Nat.mul_div_le (4096 * T - 1) D
    have hsub := Nat.sub_le (4096 * T) 1
    have hTmax := le_max_right D T
    nlinarith

theorem statisticalRationalTolerance_le_statistical {D T : ℕ}
    (hD : 0 < D) (hT : 0 < T) :
    (statisticalRationalTolerance D T : ℝ) ≤ Real.sqrt ((D : ℝ) / (T : ℝ)) := by
  have hk : (0 : ℝ) < statisticalToleranceDenominator D T := by
    exact_mod_cast statisticalToleranceDenominator_pos D T
  have ht : (0 : ℝ) < T := by exact_mod_cast hT
  have hcover : 4096 * (T : ℝ) ≤ (D : ℝ) * (statisticalToleranceDenominator D T : ℝ) ^ 2 := by
    exact_mod_cast statisticalToleranceDenominator_covers hD hT
  have hsq : (64 / (statisticalToleranceDenominator D T : ℝ)) ^ 2 ≤ (D : ℝ) / (T : ℝ) := by
    rw [div_pow]
    exact (div_le_div_iff₀ (sq_pos_of_pos hk) ht).mpr (by norm_num; exact hcover)
  have hle := (Real.le_sqrt (by positivity : (0 : ℝ) ≤ 64 / statisticalToleranceDenominator D T)
    (by positivity : (0 : ℝ) ≤ (D : ℝ) / T)).mpr hsq
  simpa only [statisticalRationalTolerance, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using hle

/-- The new tolerance never asks for greater precision than the previous 1/T. -/
theorem rationalSampleTolerance_le_statisticalRationalTolerance {D T : ℕ}
    (hD : 0 < D) (hT : 0 < T) :
    rationalSampleTolerance T ≤ statisticalRationalTolerance D T := by
  have ht2 : T ≤ T ^ 2 := by nlinarith
  have hd := Nat.mul_le_mul_right (T ^ 2) hD
  have hk : statisticalToleranceDenominator D T ≤ 64 * T := by
    apply (statisticalToleranceDenominator_le_iff hD hT).mpr
    constructor <;> nlinarith
  have hkq : (statisticalToleranceDenominator D T : ℚ) ≤ 64 * (T : ℚ) := by exact_mod_cast hk
  unfold rationalSampleTolerance statisticalRationalTolerance
  apply (div_le_div_iff₀ (by exact_mod_cast hT)
    (by exact_mod_cast statisticalToleranceDenominator_pos D T)).mpr
  simpa using hkq

/-- Exact outer count at the rational statistical tolerance. -/
theorem dimensionRationalOuterCount_statistical (D T : ℕ) :
    dimensionRationalOuterCount D (statisticalRationalTolerance D T) =
      Nat.ceil (13 * ((D : ℚ) + 1) * (statisticalToleranceDenominator D T : ℚ) ^ 2 / 4096) := by
  rw [dimensionRationalOuterCount_formula]
  have hk : (statisticalToleranceDenominator D T : ℚ) ≠ 0 := by
    exact_mod_cast (statisticalToleranceDenominator_pos D T).ne'
  congr 1
  unfold statisticalRationalTolerance
  field_simp
  <;> ring

/-- Exact inner count at the rational statistical tolerance. -/
theorem dimensionRationalInnerCount_statistical (D T : ℕ) :
    dimensionRationalInnerCount D (statisticalRationalTolerance D T) =
      Nat.ceil (101400 * ((D : ℚ) + 1) ^ 2 *
        (statisticalToleranceDenominator D T : ℚ) ^ 4 / 16777216) := by
  rw [dimensionRationalInnerCount_formula D (statisticalRationalTolerance_pos D T).ne']
  have hk : (statisticalToleranceDenominator D T : ℚ) ≠ 0 := by
    exact_mod_cast (statisticalToleranceDenominator_pos D T).ne'
  congr 1
  unfold statisticalRationalTolerance
  field_simp
  <;> ring

private theorem statistical_outer_numerator_le (D T : ℕ) (hD : 64 ≤ D) :
    13 * (D + 1) * statisticalToleranceDenominator D T ^ 2 ≤ 14 * 4096 * max D T := by
  have hbudget := statisticalToleranceDenominator_budget (D := D) (T := T)
  have hmul := Nat.mul_le_mul_left (13 * (D + 1)) hbudget
  have hconst : 13 * 4225 * (D + 1) ≤ 14 * 4096 * D := by omega
  have hprod := Nat.mul_le_mul_right (max D T) hconst
  have hfinal : D * (13 * (D + 1) * statisticalToleranceDenominator D T ^ 2) ≤
      D * (14 * 4096 * max D T) := by nlinarith
  exact Nat.le_of_mul_le_mul_left hfinal (by omega)

/-- The actual outer loop needs at most fourteen times max(D,T) iterations. -/
theorem dimensionRationalOuterCount_statistical_le (D T : ℕ) (hD : 64 ≤ D) :
    dimensionRationalOuterCount D (statisticalRationalTolerance D T) ≤ 14 * max D T := by
  rw [dimensionRationalOuterCount_statistical]
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 4096)).mpr
  have hb := statistical_outer_numerator_le D T hD
  exact_mod_cast (by nlinarith : 13 * (D + 1) * statisticalToleranceDenominator D T ^ 2 ≤
    (14 * max D T) * 4096)

/-- The actual inner projection loop is quadratic in max(D,T). -/
theorem dimensionRationalInnerCount_statistical_le (D T : ℕ) (hD : 64 ≤ D) :
    dimensionRationalInnerCount D (statisticalRationalTolerance D T) ≤
      117600 * (max D T) ^ 2 := by
  rw [dimensionRationalInnerCount_statistical]
  apply Nat.ceil_le.mpr
  apply (div_le_iff₀ (by norm_num : (0 : ℚ) < 16777216)).mpr
  have hs := Nat.pow_le_pow_left (statistical_outer_numerator_le D T hD) 2
  have hb : 101400 * (D + 1) ^ 2 * statisticalToleranceDenominator D T ^ 4 ≤
      (117600 * (max D T) ^ 2) * 16777216 := by nlinarith
  exact_mod_cast hb

end TomographyOracleCore.Revision.MatrixSolver
