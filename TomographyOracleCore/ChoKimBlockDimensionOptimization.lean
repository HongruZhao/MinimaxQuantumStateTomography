import TomographyOracleCore.ChoKimPeriodicNearExactVariance
import TomographyOracleCore.StatisticalScaleArithmetic

namespace TomographyOracleCore

/-!
# Dimension consequences of the periodic Cho--Kim condition

The explicit periodic block-growth condition already forces at least sixteen
qubits.  This module isolates that deterministic reduction and the elementary
exponential estimates used by the dimension-sharp confidence calculation.
-/

/-- The overlap dimension forced by the explicit Cho--Kim growth condition is
strictly larger than `128`. -/
theorem ChoKimBlockCondition.oneTwentyEight_lt_overlap
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    (128 : ℝ) < choKimOverlapDimension K := by
  have hlog : 0 < Real.log 2 := log_two_pos
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hKreal : (K : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast h.block_le_qubits hn
  have hq0 : 0 ≤ choKimOverlapDimension K :=
    (choKimOverlapDimension_pos K).le
  have hKq :
      (K : ℝ) * choKimOverlapDimension K ≤
        (n : ℝ) * choKimOverlapDimension K :=
    mul_le_mul_of_nonneg_right hKreal hq0
  have hcancel :
      92 / Real.log 2 ≤ choKimOverlapDimension K := by
    exact (mul_le_mul_iff_of_pos_left hnreal).mp (by
      simpa [mul_comm, choKimOverlapDimension] using
        h.explicit_growth.trans hKq)
  have h128 : (128 : ℝ) < 92 / Real.log 2 := by
    apply (lt_div_iff₀ hlog).2
    nlinarith [Real.log_two_lt_d9]
  exact h128.trans_le hcancel

/-- The explicit Cho--Kim block condition forces at least sixteen qubits. -/
theorem ChoKimBlockCondition.sixteen_le_qubits
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    16 ≤ n := by
  have hoverlap := h.oneTwentyEight_lt_overlap hn
  have hhalf : 8 ≤ K / 2 := by
    by_contra hnot
    have hle : K / 2 ≤ 7 := by omega
    have hp : (2 : ℝ) ^ (K / 2) ≤ (2 : ℝ) ^ 7 :=
      pow_le_pow_right₀ (by norm_num) hle
    norm_num [choKimOverlapDimension] at hoverlap hp
    linarith
  have hK : 16 ≤ K := by
    calc
      16 = 2 * 8 := by norm_num
      _ ≤ 2 * (K / 2) := Nat.mul_le_mul_left 2 hhalf
      _ ≤ K := Nat.mul_div_le K 2
  exact hK.trans (h.block_le_qubits hn)

/-- Consequently, the Hilbert-space dimension is at least `2^16 = 65536`. -/
theorem ChoKimBlockCondition.sixtyFiveThousandFiveHundredThirtySix_le_dimension
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    65536 ≤ 2 ^ n := by
  have hn16 := h.sixteen_le_qubits hn
  norm_num [show (65536 : ℕ) = 2 ^ 16 by norm_num]
  exact Nat.pow_le_pow_right (by norm_num : 0 < 2) hn16

/-- Elementary reciprocal bound for the square root of the exponential tail. -/
theorem exp_neg_twentieth_nat_le
    (D : ℕ) (hD : 0 < D) :
    Real.exp (-(D : ℝ) / 20) ≤ 20 / (D : ℝ) := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  let x : ℝ := (D : ℝ) / 20
  have hx : 0 < x := by dsimp [x]; positivity
  have hmul : x * Real.exp (-x) ≤ 1 := by
    calc
      x * Real.exp (-x) ≤ Real.exp (-1) :=
        Real.mul_exp_neg_le_exp_neg_one x
      _ ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
  have hdiv : Real.exp (-x) ≤ 1 / x :=
    (le_div_iff₀ hx).2 (by simpa [mul_comm] using hmul)
  dsimp [x] at hdiv
  calc
    Real.exp (-(D : ℝ) / 20) =
        Real.exp (-((D : ℝ) / 20)) := by congr 1 <;> ring
    _ ≤ 1 / ((D : ℝ) / 20) := hdiv
    _ = 20 / (D : ℝ) := by field_simp

/-- Squaring the preceding estimate gives a quadratic reciprocal bound. -/
theorem exp_neg_tenth_nat_le_four_hundred_div_sq
    (D : ℕ) (hD : 0 < D) :
    Real.exp (-(D : ℝ) / 10) ≤ 400 / (D : ℝ) ^ 2 := by
  have hh := exp_neg_twentieth_nat_le D hD
  have heq :
      Real.exp (-(D : ℝ) / 10) =
        Real.exp (-(D : ℝ) / 20) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [heq]
  calc
    Real.exp (-(D : ℝ) / 20) ^ 2 ≤ (20 / (D : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (Real.exp_nonneg _) hh 2
    _ = 400 / (D : ℝ) ^ 2 := by ring

/-- At dimension at least `65536`, the half-tail term is at most
`25/8192` times the square-root statistical scale. -/
theorem exp_neg_tenth_half_le_small_sqrt
    (D U : ℕ) (hD : 0 < D) (hU : 0 < U)
    (hlargeD : 65536 ≤ D) (hcube : (U : ℝ) ≤ (D : ℝ) ^ 3) :
    Real.exp (-(D : ℝ) / 10) / 2 ≤
      (25 / 8192 : ℝ) * Real.sqrt ((D : ℝ) / (U : ℝ)) := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hlargeReal : (65536 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hlargeD
  have hexp := exp_neg_tenth_nat_le_four_hundred_div_sq D hD
  have hinv := inv_dimension_le_sqrt_dimension_div_samples
    D U hD hU hcube
  have hcoef : 200 / (D : ℝ) ≤ (25 / 8192 : ℝ) := by
    apply (div_le_iff₀ hDreal).2
    nlinarith
  calc
    Real.exp (-(D : ℝ) / 10) / 2 ≤
        (400 / (D : ℝ) ^ 2) / 2 :=
      div_le_div_of_nonneg_right hexp (by norm_num)
    _ = (200 / (D : ℝ)) * (1 / (D : ℝ)) := by ring
    _ ≤ (25 / 8192 : ℝ) * (1 / (D : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ ≤ (25 / 8192 : ℝ) * Real.sqrt ((D : ℝ) / (U : ℝ)) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)

end TomographyOracleCore
