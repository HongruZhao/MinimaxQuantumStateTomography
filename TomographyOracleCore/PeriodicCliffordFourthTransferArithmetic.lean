import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace TomographyOracleCore

/-!
# Scalar arithmetic for the periodic fourth-copy Clifford transfer

This file contains only the elementary real and finite-class arithmetic that
follows the scientific fourth-copy Clifford transfer identity.  In
particular, it does **not** assume or assert a Clifford commutant theorem, a
twirling formula, or the `30`-sector classification.
-/

noncomputable section

/-! ## The four intersection classes -/

/-- Common denominator in the four scalar Clifford-Weingarten coefficients. -/
def cliffordFourthDenominator (x : ℝ) : ℝ :=
  (x ^ 2 - 1) * (x ^ 2 - 4) * (x ^ 2 - 16)

/-- Coefficient for intersection dimension one. -/
def cliffordFourthWgOne (x : ℝ) : ℝ :=
  -8 / (x * cliffordFourthDenominator x)

/-- Coefficient for intersection dimension two. -/
def cliffordFourthWgTwo (x : ℝ) : ℝ :=
  2 / cliffordFourthDenominator x

/-- Coefficient for intersection dimension three. -/
def cliffordFourthWgThree (x : ℝ) : ℝ :=
  -(x ^ 2 - 8) / (x * cliffordFourthDenominator x)

/-- Coefficient for intersection dimension four. -/
def cliffordFourthWgFour (x : ℝ) : ℝ :=
  (x ^ 2 - 14) / cliffordFourthDenominator x

/-- Constant row sum of the fourth-copy Gram matrix with class counts
`8, 14, 7, 1`. -/
def cliffordFourthGramRowSum (x : ℝ) : ℝ :=
  8 * x + 14 * x ^ 2 + 7 * x ^ 3 + x ^ 4

/-- Signed row sum of the displayed inverse-Gram coefficients. -/
def cliffordFourthWgSignedRowSum (x : ℝ) : ℝ :=
  8 * cliffordFourthWgOne x + 14 * cliffordFourthWgTwo x +
    7 * cliffordFourthWgThree x + cliffordFourthWgFour x

/-- Absolute row sum of the displayed inverse-Gram coefficients. -/
def cliffordFourthWgAbsoluteRowSum (x : ℝ) : ℝ :=
  8 * |cliffordFourthWgOne x| + 14 * |cliffordFourthWgTwo x| +
    7 * |cliffordFourthWgThree x| + |cliffordFourthWgFour x|

theorem cliffordFourthDenominator_pos {x : ℝ} (hx : 4 < x) :
    0 < cliffordFourthDenominator x := by
  have h1 : 0 < x ^ 2 - 1 := by nlinarith [sq_nonneg (x - 4)]
  have h4 : 0 < x ^ 2 - 4 := by nlinarith [sq_nonneg (x - 4)]
  have h16 : 0 < x ^ 2 - 16 := by nlinarith [sq_nonneg (x - 4)]
  exact mul_pos (mul_pos h1 h4) h16

theorem cliffordFourthGramRowSum_eq (x : ℝ) :
    cliffordFourthGramRowSum x = x * (x + 1) * (x + 2) * (x + 4) := by
  unfold cliffordFourthGramRowSum
  ring

/-!
The next four identities are the four rows of `W_x G_x = I`, after the
intersection-number table has grouped the thirty labels by intersection
dimension.  Thus the finite classification is cleanly separated from the
rational arithmetic checked here.
-/

theorem cliffordFourthWg_inverse_class_one {x : ℝ} (hx : 4 < x) :
    7 * cliffordFourthWgOne x * x ^ 2 +
      cliffordFourthWgOne x * x ^ 4 +
      7 * cliffordFourthWgTwo x * x +
      7 * cliffordFourthWgTwo x * x ^ 3 +
      7 * cliffordFourthWgThree x * x ^ 2 +
      cliffordFourthWgFour x * x = 0 := by
  have hden := (cliffordFourthDenominator_pos hx).ne'
  have hx0 : x ≠ 0 := by positivity
  unfold cliffordFourthWgOne cliffordFourthWgTwo
    cliffordFourthWgThree cliffordFourthWgFour
  field_simp [hden, hx0]
  unfold cliffordFourthDenominator
  ring

theorem cliffordFourthWg_inverse_class_two {x : ℝ} (hx : 4 < x) :
    4 * cliffordFourthWgOne x * x +
      4 * cliffordFourthWgOne x * x ^ 3 +
      13 * cliffordFourthWgTwo x * x ^ 2 +
      cliffordFourthWgTwo x * x ^ 4 +
      4 * cliffordFourthWgThree x * x +
      3 * cliffordFourthWgThree x * x ^ 3 +
      cliffordFourthWgFour x * x ^ 2 = 0 := by
  have hden := (cliffordFourthDenominator_pos hx).ne'
  have hx0 : x ≠ 0 := by positivity
  unfold cliffordFourthWgOne cliffordFourthWgTwo
    cliffordFourthWgThree cliffordFourthWgFour
  field_simp [hden, hx0]
  unfold cliffordFourthDenominator
  ring

theorem cliffordFourthWg_inverse_class_three {x : ℝ} (hx : 4 < x) :
    8 * cliffordFourthWgOne x * x ^ 2 +
      8 * cliffordFourthWgTwo x * x +
      6 * cliffordFourthWgTwo x * x ^ 3 +
      6 * cliffordFourthWgThree x * x ^ 2 +
      cliffordFourthWgThree x * x ^ 4 +
      cliffordFourthWgFour x * x ^ 3 = 0 := by
  have hden := (cliffordFourthDenominator_pos hx).ne'
  have hx0 : x ≠ 0 := by positivity
  unfold cliffordFourthWgOne cliffordFourthWgTwo
    cliffordFourthWgThree cliffordFourthWgFour
  field_simp [hden, hx0]
  unfold cliffordFourthDenominator
  ring

theorem cliffordFourthWg_inverse_class_four {x : ℝ} (hx : 4 < x) :
    8 * cliffordFourthWgOne x * x +
      14 * cliffordFourthWgTwo x * x ^ 2 +
      7 * cliffordFourthWgThree x * x ^ 3 +
      cliffordFourthWgFour x * x ^ 4 = 1 := by
  have hden := (cliffordFourthDenominator_pos hx).ne'
  have hx0 : x ≠ 0 := by positivity
  unfold cliffordFourthWgOne cliffordFourthWgTwo
    cliffordFourthWgThree cliffordFourthWgFour
  field_simp [hden, hx0]
  unfold cliffordFourthDenominator
  ring

/-- Exact signed row sum `W_x 1 = c_x^(-1) 1`. -/
theorem cliffordFourthWgSignedRowSum_eq {x : ℝ} (hx : 4 < x) :
    cliffordFourthWgSignedRowSum x =
      1 / (x * (x + 1) * (x + 2) * (x + 4)) := by
  have hden := (cliffordFourthDenominator_pos hx).ne'
  have hx0 : x ≠ 0 := by positivity
  have hx1 : x + 1 ≠ 0 := by positivity
  have hx2 : x + 2 ≠ 0 := by positivity
  have hx4 : x + 4 ≠ 0 := by positivity
  unfold cliffordFourthWgSignedRowSum cliffordFourthWgOne
    cliffordFourthWgTwo cliffordFourthWgThree cliffordFourthWgFour
  field_simp [hden, hx0, hx1, hx2, hx4]
  unfold cliffordFourthDenominator
  ring

/-- Exact absolute row sum, using the signs valid for `x >= 8`. -/
theorem cliffordFourthWgAbsoluteRowSum_eq {x : ℝ} (hx : 8 ≤ x) :
    cliffordFourthWgAbsoluteRowSum x =
      1 / (x * (x - 1) * (x - 2) * (x - 4)) := by
  have hx4 : 4 < x := lt_of_lt_of_le (by norm_num) hx
  have hdenpos := cliffordFourthDenominator_pos hx4
  have hxpos : 0 < x := lt_trans (by norm_num) hx4
  have h8 : 0 ≤ x ^ 2 - 8 := by nlinarith [sq_nonneg (x - 8)]
  have h14 : 0 ≤ x ^ 2 - 14 := by nlinarith [sq_nonneg (x - 8)]
  have hw1 : cliffordFourthWgOne x ≤ 0 := by
    unfold cliffordFourthWgOne
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
      (mul_nonneg hxpos.le hdenpos.le)
  have hw2 : 0 ≤ cliffordFourthWgTwo x := by
    unfold cliffordFourthWgTwo
    positivity
  have hw3 : cliffordFourthWgThree x ≤ 0 := by
    unfold cliffordFourthWgThree
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr h8)
      (mul_nonneg hxpos.le hdenpos.le)
  have hw4 : 0 ≤ cliffordFourthWgFour x := by
    unfold cliffordFourthWgFour
    exact div_nonneg h14 hdenpos.le
  rw [cliffordFourthWgAbsoluteRowSum, abs_of_nonpos hw1,
    abs_of_nonneg hw2, abs_of_nonpos hw3, abs_of_nonneg hw4]
  have hden := hdenpos.ne'
  have hx0 : x ≠ 0 := hxpos.ne'
  have hx1 : x - 1 ≠ 0 := by nlinarith
  have hx2 : x - 2 ≠ 0 := by nlinarith
  have hx4ne : x - 4 ≠ 0 := by nlinarith
  unfold cliffordFourthWgOne cliffordFourthWgTwo
    cliffordFourthWgThree cliffordFourthWgFour
  field_simp [hden, hx0, hx1, hx2, hx4ne]
  unfold cliffordFourthDenominator
  ring

/-! ## Exact local correction factor -/

/-- The three-factor inflation left after multiplying the signed first-layer
row sum, the absolute second-layer row sum, and two overlap Gram row sums. -/
def periodicCliffordFourthCorrection (s : ℝ) : ℝ :=
  ((1 + 1 / s) ^ 2 / (1 - 1 / s ^ 4)) *
    ((1 + 2 / s) ^ 2 / (1 - 4 / s ^ 4)) *
    ((1 + 4 / s) ^ 2 / (1 - 16 / s ^ 4))

theorem periodicCliffordFourthCorrection_pos {s : ℝ} (hs : 8 ≤ s) :
    0 < periodicCliffordFourthCorrection s := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hs4 : (16 : ℝ) < s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 16)]
  unfold periodicCliffordFourthCorrection
  have h1 : 0 < 1 - 1 / s ^ 4 := by
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    linarith
  have h4 : 0 < 1 - 4 / s ^ 4 := by
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    linarith
  have h16 : 0 < 1 - 16 / s ^ 4 := by
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    exact hs4
  positivity

/-- Exact algebraic reduction of the local transfer factor to `s^-8` times
the correction above. -/
theorem periodicCliffordFourthLocalFactor_eq {s : ℝ} (hs : 8 ≤ s) :
    cliffordFourthWgSignedRowSum (s ^ 2) *
        cliffordFourthWgAbsoluteRowSum (s ^ 2) *
        cliffordFourthGramRowSum s ^ 2 =
      periodicCliffordFourthCorrection s / (s ^ 2) ^ 4 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hs2eight : 8 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 8)]
  have hs2four : 4 < s ^ 2 := lt_of_lt_of_le (by norm_num) hs2eight
  rw [cliffordFourthWgSignedRowSum_eq hs2four,
    cliffordFourthWgAbsoluteRowSum_eq hs2eight,
    cliffordFourthGramRowSum_eq]
  unfold periodicCliffordFourthCorrection
  have hsne : s ≠ 0 := hs0.ne'
  have hsm1 : s ^ 2 - 1 ≠ 0 := by nlinarith [sq_nonneg (s - 8)]
  have hsm2 : s ^ 2 - 2 ≠ 0 := by nlinarith [sq_nonneg (s - 8)]
  have hsm4 : s ^ 2 - 4 ≠ 0 := by nlinarith [sq_nonneg (s - 8)]
  have hsp1 : s ^ 2 + 1 ≠ 0 := by positivity
  have hsp2 : s ^ 2 + 2 ≠ 0 := by positivity
  have hsp4 : s ^ 2 + 4 ≠ 0 := by positivity
  have hd1 : 1 - 1 / s ^ 4 ≠ 0 := by
    have : (1 : ℝ) < s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 1)]
    apply ne_of_gt
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    exact this
  have hd4 : 1 - 4 / s ^ 4 ≠ 0 := by
    have : (4 : ℝ) < s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 2)]
    apply ne_of_gt
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    exact this
  have hd16 : 1 - 16 / s ^ 4 ≠ 0 := by
    have : (16 : ℝ) < s ^ 4 := by nlinarith [sq_nonneg (s ^ 2 - 4)]
    apply ne_of_gt
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    exact this
  have hpoly :
      -64 + s ^ 4 * 84 - s ^ 8 * 21 + s ^ 12 =
        (s ^ 4 - 1) * (s ^ 4 - 4) * (s ^ 4 - 16) := by ring
  have hpolyne :
      -64 + s ^ 4 * 84 - s ^ 8 * 21 + s ^ 12 ≠ 0 := by
    rw [hpoly]
    have h1 : 0 < s ^ 4 - 1 := by
      nlinarith [sq_nonneg (s ^ 2 - 1)]
    have h4 : 0 < s ^ 4 - 4 := by
      nlinarith [sq_nonneg (s ^ 2 - 2)]
    have h16 : 0 < s ^ 4 - 16 := by
      nlinarith [sq_nonneg (s ^ 2 - 4)]
    exact (mul_pos (mul_pos h1 h4) h16).ne'
  have hdprodne :
      (s ^ 4 - 1) * (s ^ 4 - 4) * (s ^ 4 - 16) ≠ 0 := by
    rw [← hpoly]
    exact hpolyne
  field_simp [hsne, hsm1, hsm2, hsm4, hsp1, hsp2, hsp4, hd1, hd4, hd16,
    hpolyne]
  rw [eq_div_iff hdprodne]
  ring

/-! ## The sharp logarithmic correction -/

/-- The alternating cubic upper bound for `log (1+x)`, proved directly by
monotonicity of the exact remainder. -/
theorem log_one_add_le_cubic {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + x ^ 3 / 3 := by
  let F : ℝ → ℝ := fun y ↦
    y - y ^ 2 / 2 + y ^ 3 / 3 - Real.log (1 + y)
  have hderiv : ∀ y ∈ Set.Icc 0 x,
      HasDerivAt F (y ^ 3 / (1 + y)) y := by
    intro y hy
    have hyden : 1 + y ≠ 0 := by nlinarith [hy.1]
    dsimp [F]
    convert
      (((hasDerivAt_id y).sub ((hasDerivAt_pow 2 y).div_const 2)).add
        ((hasDerivAt_pow 3 y).div_const 3)).sub
          (((hasDerivAt_const y 1).add (hasDerivAt_id y)).log hyden) using 1 <;>
      try rfl
    · simp only [id_eq, Pi.add_apply]
      field_simp [hyden]
      ring
  have hmono : MonotoneOn F (Set.Icc 0 x) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 x)
      (fun y hy ↦ (hderiv y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hderiv y (interior_subset hy)).hasDerivWithinAt) ?_
    intro y hy
    have hy0 : 0 ≤ y := (interior_subset hy).1
    have hyden : 0 < 1 + y := by linarith
    exact div_nonneg (pow_nonneg hy0 3) hyden.le
  have h := hmono (by exact ⟨le_rfl, hx⟩) (by exact ⟨hx, le_rfl⟩) hx
  simpa [F] using h

/-- Elementary upper bound for the logarithmic denominator correction. -/
theorem neg_log_one_sub_le_fraction {y : ℝ} (_hy0 : 0 ≤ y) (hy1 : y < 1) :
    -Real.log (1 - y) ≤ y / (1 - y) := by
  have hden : 0 < 1 - y := sub_pos.mpr hy1
  have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at h
  calc
    -Real.log (1 - y) ≤ (1 - y)⁻¹ - 1 := h
    _ = y / (1 - y) := by
      field_simp [hden.ne']
      ring

/-- Exact logarithmic expansion of the three-factor correction. -/
theorem log_periodicCliffordFourthCorrection_eq {s : ℝ} (hs : 8 ≤ s) :
    Real.log (periodicCliffordFourthCorrection s) =
      2 * Real.log (1 + 1 / s) +
      2 * Real.log (1 + 2 / s) +
      2 * Real.log (1 + 4 / s) -
      Real.log (1 - 1 / s ^ 4) -
      Real.log (1 - 4 / s ^ 4) -
      Real.log (1 - 16 / s ^ 4) := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hs4_16 : (16 : ℝ) < s ^ 4 := by
    have ht : (64 : ℝ) ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 8)]
    nlinarith [sq_nonneg (s ^ 2 - 16)]
  have hb1 : 0 < 1 + 1 / s := by positivity
  have hb2 : 0 < 1 + 2 / s := by positivity
  have hb4 : 0 < 1 + 4 / s := by positivity
  have hd1 : 0 < 1 - 1 / s ^ 4 := by
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    linarith
  have hd4 : 0 < 1 - 4 / s ^ 4 := by
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    linarith
  have hd16 : 0 < 1 - 16 / s ^ 4 := by
    rw [sub_pos, div_lt_one (pow_pos hs0 4)]
    exact hs4_16
  have hf1 : 0 < (1 + 1 / s) ^ 2 / (1 - 1 / s ^ 4) := by positivity
  have hf2 : 0 < (1 + 2 / s) ^ 2 / (1 - 4 / s ^ 4) := by positivity
  have hf4 : 0 < (1 + 4 / s) ^ 2 / (1 - 16 / s ^ 4) := by positivity
  have hlog1 :
      Real.log ((1 + 1 / s) ^ 2 / (1 - 1 / s ^ 4)) =
        2 * Real.log (1 + 1 / s) - Real.log (1 - 1 / s ^ 4) := by
    rw [Real.log_div (pow_ne_zero 2 hb1.ne') hd1.ne', Real.log_pow]
    norm_num
  have hlog2 :
      Real.log ((1 + 2 / s) ^ 2 / (1 - 4 / s ^ 4)) =
        2 * Real.log (1 + 2 / s) - Real.log (1 - 4 / s ^ 4) := by
    rw [Real.log_div (pow_ne_zero 2 hb2.ne') hd4.ne', Real.log_pow]
    norm_num
  have hlog4 :
      Real.log ((1 + 4 / s) ^ 2 / (1 - 16 / s ^ 4)) =
        2 * Real.log (1 + 4 / s) - Real.log (1 - 16 / s ^ 4) := by
    rw [Real.log_div (pow_ne_zero 2 hb4.ne') hd16.ne', Real.log_pow]
    norm_num
  unfold periodicCliffordFourthCorrection
  rw [Real.log_mul (mul_ne_zero hf1.ne' hf2.ne') hf4.ne',
    Real.log_mul hf1.ne' hf2.ne', hlog1, hlog2, hlog4]
  ring

/-- Sharp scalar estimate used by the periodic fourth-copy transfer:
`log R(s) <= 14/s` for every real `s >= 8`. -/
theorem log_periodicCliffordFourthCorrection_le {s : ℝ} (hs : 8 ≤ s) :
    Real.log (periodicCliffordFourthCorrection s) ≤ 14 / s := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsne : s ≠ 0 := hs0.ne'
  have ht : (64 : ℝ) ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 8)]
  have hs4_16 : (16 : ℝ) < s ^ 4 := by
    nlinarith [sq_nonneg (s ^ 2 - 16)]
  have hx1 : 0 ≤ 1 / s := by positivity
  have hx2 : 0 ≤ 2 / s := by positivity
  have hx4 : 0 ≤ 4 / s := by positivity
  have hy1 : 0 ≤ 1 / s ^ 4 := by positivity
  have hy4 : 0 ≤ 4 / s ^ 4 := by positivity
  have hy16 : 0 ≤ 16 / s ^ 4 := by positivity
  have hy1lt : 1 / s ^ 4 < 1 := by
    rw [div_lt_one (pow_pos hs0 4)]
    linarith
  have hy4lt : 4 / s ^ 4 < 1 := by
    rw [div_lt_one (pow_pos hs0 4)]
    linarith
  have hy16lt : 16 / s ^ 4 < 1 := by
    rw [div_lt_one (pow_pos hs0 4)]
    exact hs4_16
  have hc1 := log_one_add_le_cubic hx1
  have hc2 := log_one_add_le_cubic hx2
  have hc4 := log_one_add_le_cubic hx4
  have hn1 := neg_log_one_sub_le_fraction hy1 hy1lt
  have hn4 := neg_log_one_sub_le_fraction hy4 hy4lt
  have hn16 := neg_log_one_sub_le_fraction hy16 hy16lt
  have hraw :
      Real.log (periodicCliffordFourthCorrection s) ≤
        2 * (1 / s - (1 / s) ^ 2 / 2 + (1 / s) ^ 3 / 3) +
        2 * (2 / s - (2 / s) ^ 2 / 2 + (2 / s) ^ 3 / 3) +
        2 * (4 / s - (4 / s) ^ 2 / 2 + (4 / s) ^ 3 / 3) +
        (1 / s ^ 4) / (1 - 1 / s ^ 4) +
        (4 / s ^ 4) / (1 - 4 / s ^ 4) +
        (16 / s ^ 4) / (1 - 16 / s ^ 4) := by
    rw [log_periodicCliffordFourthCorrection_eq hs]
    linarith
  have hcubic :
      2 * (1 / s - (1 / s) ^ 2 / 2 + (1 / s) ^ 3 / 3) +
        2 * (2 / s - (2 / s) ^ 2 / 2 + (2 / s) ^ 3 / 3) +
        2 * (4 / s - (4 / s) ^ 2 / 2 + (4 / s) ^ 3 / 3) =
      14 / s - 21 / s ^ 2 + 146 / (3 * s ^ 3) := by
    field_simp [hsne]
    ring
  have hs4m1 : 0 < s ^ 4 - 1 := by linarith
  have hs4m4 : 0 < s ^ 4 - 4 := by linarith
  have hs4m16 : 0 < s ^ 4 - 16 := by linarith
  have hpenaltyRewrite :
      (1 / s ^ 4) / (1 - 1 / s ^ 4) +
          (4 / s ^ 4) / (1 - 4 / s ^ 4) +
          (16 / s ^ 4) / (1 - 16 / s ^ 4) =
        1 / (s ^ 4 - 1) + 4 / (s ^ 4 - 4) + 16 / (s ^ 4 - 16) := by
    field_simp [hsne, hs4m1.ne', hs4m4.ne', hs4m16.ne']
  have hpenalty :
      (1 / s ^ 4) / (1 - 1 / s ^ 4) +
          (4 / s ^ 4) / (1 - 4 / s ^ 4) +
          (16 / s ^ 4) / (1 - 16 / s ^ 4) ≤
        1 / s ^ 2 := by
    rw [hpenaltyRewrite]
    have h1 : 1 / (s ^ 4 - 1) ≤ 1 / (s ^ 4 - 16) := by
      rw [div_le_div_iff₀ hs4m1 hs4m16]
      linarith
    have h4 : 4 / (s ^ 4 - 4) ≤ 4 / (s ^ 4 - 16) := by
      rw [div_le_div_iff₀ hs4m4 hs4m16]
      nlinarith
    have hsum :
        1 / (s ^ 4 - 1) + 4 / (s ^ 4 - 4) + 16 / (s ^ 4 - 16) ≤
          21 / (s ^ 4 - 16) := by
      calc
        1 / (s ^ 4 - 1) + 4 / (s ^ 4 - 4) + 16 / (s ^ 4 - 16) ≤
            1 / (s ^ 4 - 16) + 4 / (s ^ 4 - 16) +
              16 / (s ^ 4 - 16) := by linarith
        _ = 21 / (s ^ 4 - 16) := by ring
    have hmul : 0 ≤ s ^ 2 * (s ^ 2 - 64) :=
      mul_nonneg (sq_nonneg s) (sub_nonneg.mpr ht)
    have hlast : 21 / (s ^ 4 - 16) ≤ 1 / s ^ 2 := by
      rw [div_le_div_iff₀ hs4m16 (sq_pos_of_pos hs0)]
      nlinarith
    exact hsum.trans hlast
  have hthird : 146 / (3 * s ^ 3) ≤ 7 / s ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos (by norm_num) (pow_pos hs0 3))
      (sq_pos_of_pos hs0)]
    nlinarith
  calc
    Real.log (periodicCliffordFourthCorrection s) ≤
        (14 / s - 21 / s ^ 2 + 146 / (3 * s ^ 3)) + 1 / s ^ 2 := by
      linarith [hraw, hpenalty, hcubic]
    _ ≤ (14 / s - 21 / s ^ 2 + 7 / s ^ 2) + 1 / s ^ 2 := by
      linarith [hthird]
    _ = 14 / s - 13 / s ^ 2 := by ring
    _ ≤ 14 / s := by
      have h13 : 0 ≤ 13 / s ^ 2 := div_nonneg (by norm_num) (sq_nonneg s)
      linarith

/-! ## Block accumulation and the abstract periodic contraction -/

/-- The exact scalar block condition needed for fourth-copy accumulation.
It is deliberately independent of the scientific identification
`m = n/K`, `s = 2^(K/2)`. -/
def PeriodicCliffordFourthBlockPredicate (m : ℕ) (s : ℝ) : Prop :=
  8 ≤ s ∧ (m : ℝ) / s ≤ Real.log 2 / 92

/-- The sharp logarithmic estimate accumulates to the explicit factor
`2^(7/46)` under the scalar block predicate. -/
theorem periodicCliffordFourthCorrection_pow_le
    {m : ℕ} {s : ℝ} (hblock : PeriodicCliffordFourthBlockPredicate m s) :
    periodicCliffordFourthCorrection s ^ m ≤
      (2 : ℝ) ^ (7 / 46 : ℝ) := by
  have hs : 8 ≤ s := hblock.1
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hRpos := periodicCliffordFourthCorrection_pos hs
  have hlog := log_periodicCliffordFourthCorrection_le hs
  have hm0 : 0 ≤ (m : ℝ) := by positivity
  have hmulLog :
      (m : ℝ) * Real.log (periodicCliffordFourthCorrection s) ≤
        (m : ℝ) * (14 / s) :=
    mul_le_mul_of_nonneg_left hlog hm0
  have hblockScaled :
      (m : ℝ) * (14 / s) ≤ (7 / 46 : ℝ) * Real.log 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hblock.2 (by norm_num : (0 : ℝ) ≤ 14)
    calc
      (m : ℝ) * (14 / s) = 14 * ((m : ℝ) / s) := by ring
      _ ≤ 14 * (Real.log 2 / 92) := hscaled
      _ = (7 / 46 : ℝ) * Real.log 2 := by ring
  calc
    periodicCliffordFourthCorrection s ^ m =
        (Real.exp (Real.log (periodicCliffordFourthCorrection s))) ^ m := by
      rw [Real.exp_log hRpos]
    _ = Real.exp ((m : ℝ) *
        Real.log (periodicCliffordFourthCorrection s)) := by
      rw [← Real.exp_nat_mul]
    _ ≤ Real.exp ((7 / 46 : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr (hmulLog.trans hblockScaled)
    _ = (2 : ℝ) ^ (7 / 46 : ℝ) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring

/-- A local-factor version of the accumulated correction bound. -/
theorem periodicCliffordFourthLocalFactor_pow_le
    {m : ℕ} {s : ℝ} (hblock : PeriodicCliffordFourthBlockPredicate m s) :
    (cliffordFourthWgSignedRowSum (s ^ 2) *
          cliffordFourthWgAbsoluteRowSum (s ^ 2) *
          cliffordFourthGramRowSum s ^ 2) ^ m ≤
      (2 : ℝ) ^ (7 / 46 : ℝ) / ((s ^ 2) ^ 4) ^ m := by
  have hs := hblock.1
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  rw [periodicCliffordFourthLocalFactor_eq hs, div_pow]
  exact div_le_div_of_nonneg_right
    (periodicCliffordFourthCorrection_pow_le hblock)
    (by positivity : 0 ≤ ((s ^ 2) ^ 4) ^ m)

/-- Pure scalar assembly of the periodic trace-cycle argument.

The hypotheses are exactly the three scientific outputs used after taking
absolute values: an arbitrary-boundary coefficient bounded by one, the
entrywise `Wg` contraction (already represented in `signedRow` and
`absoluteRow`), and the trace-cycle bound `cycle <= 30 * gramRow^(2m)`.
No Clifford or twirling statement is hidden in this theorem. -/
theorem periodicFourthContraction_of_boundary_wg_cycle
    {m : ℕ}
    {moment boundary signedRow absoluteRow gramRow cycle : ℝ}
    (_hboundary0 : 0 ≤ boundary) (hboundary1 : boundary ≤ 1)
    (hsigned : 0 ≤ signedRow) (habsolute : 0 ≤ absoluteRow)
    (_hgram : 0 ≤ gramRow) (hcycle0 : 0 ≤ cycle)
    (hmoment : moment ≤
      boundary * signedRow ^ m * absoluteRow ^ m * cycle)
    (hcycle : cycle ≤ 30 * gramRow ^ (2 * m)) :
    moment ≤ 30 * (signedRow * absoluteRow * gramRow ^ 2) ^ m := by
  have hsPow : 0 ≤ signedRow ^ m := pow_nonneg hsigned m
  have haPow : 0 ≤ absoluteRow ^ m := pow_nonneg habsolute m
  have hprefix : 0 ≤ signedRow ^ m * absoluteRow ^ m :=
    mul_nonneg hsPow haPow
  calc
    moment ≤ boundary * signedRow ^ m * absoluteRow ^ m * cycle := hmoment
    _ ≤ 1 * signedRow ^ m * absoluteRow ^ m * cycle := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hboundary1 hsPow) haPow) hcycle0
    _ ≤ signedRow ^ m * absoluteRow ^ m *
          (30 * gramRow ^ (2 * m)) := by
      simpa [one_mul] using mul_le_mul_of_nonneg_left hcycle hprefix
    _ = 30 * (signedRow * absoluteRow * gramRow ^ 2) ^ m := by
      rw [mul_pow, mul_pow, ← pow_mul]
      ring

/-- Abstract endpoint specialized to the exact four-class row sums.  The
remaining premises are the scientific boundary contraction and the periodic
trace-cycle estimate; the conclusion is the fully checked correction factor. -/
theorem periodicCliffordFourthContraction_corrected
    {m : ℕ} {s moment boundary cycle : ℝ}
    (hs : 8 ≤ s)
    (hboundary0 : 0 ≤ boundary) (hboundary1 : boundary ≤ 1)
    (hcycle0 : 0 ≤ cycle)
    (hmoment : moment ≤
      boundary * cliffordFourthWgSignedRowSum (s ^ 2) ^ m *
        cliffordFourthWgAbsoluteRowSum (s ^ 2) ^ m * cycle)
    (hcycle : cycle ≤ 30 * cliffordFourthGramRowSum s ^ (2 * m)) :
    moment ≤ 30 *
      (periodicCliffordFourthCorrection s / (s ^ 2) ^ 4) ^ m := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hs2eight : 8 ≤ s ^ 2 := by nlinarith [sq_nonneg (s - 8)]
  have hs2four : 4 < s ^ 2 := lt_of_lt_of_le (by norm_num) hs2eight
  have hsigned : 0 ≤ cliffordFourthWgSignedRowSum (s ^ 2) := by
    rw [cliffordFourthWgSignedRowSum_eq hs2four]
    positivity
  have habsolute : 0 ≤ cliffordFourthWgAbsoluteRowSum (s ^ 2) := by
    rw [cliffordFourthWgAbsoluteRowSum_eq hs2eight]
    have h1 : 0 ≤ s ^ 2 - 1 := by nlinarith
    have h2 : 0 ≤ s ^ 2 - 2 := by nlinarith
    have h4 : 0 ≤ s ^ 2 - 4 := by nlinarith
    exact div_nonneg zero_le_one
      (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg s) h1) h2) h4)
  have hgram : 0 ≤ cliffordFourthGramRowSum s := by
    rw [cliffordFourthGramRowSum_eq]
    positivity
  have hassembled := periodicFourthContraction_of_boundary_wg_cycle
    hboundary0 hboundary1 hsigned habsolute hgram hcycle0 hmoment hcycle
  rw [periodicCliffordFourthLocalFactor_eq hs] at hassembled
  exact hassembled

/-- The same abstract endpoint with the manuscript's scalar block predicate
inserted.  Its only non-arithmetic hypotheses remain visible in the
statement. -/
theorem periodicCliffordFourthContraction_under_block
    {m : ℕ} {s moment boundary cycle : ℝ}
    (hblock : PeriodicCliffordFourthBlockPredicate m s)
    (hboundary0 : 0 ≤ boundary) (hboundary1 : boundary ≤ 1)
    (hcycle0 : 0 ≤ cycle)
    (hmoment : moment ≤
      boundary * cliffordFourthWgSignedRowSum (s ^ 2) ^ m *
        cliffordFourthWgAbsoluteRowSum (s ^ 2) ^ m * cycle)
    (hcycle : cycle ≤ 30 * cliffordFourthGramRowSum s ^ (2 * m)) :
    moment ≤ 30 * (2 : ℝ) ^ (7 / 46 : ℝ) /
      ((s ^ 2) ^ 4) ^ m := by
  have hcorrected := periodicCliffordFourthContraction_corrected hblock.1
    hboundary0 hboundary1 hcycle0 hmoment hcycle
  have hpow := periodicCliffordFourthCorrection_pow_le hblock
  have hden0 : 0 ≤ ((s ^ 2) ^ 4) ^ m := by positivity
  calc
    moment ≤ 30 *
        (periodicCliffordFourthCorrection s / (s ^ 2) ^ 4) ^ m := hcorrected
    _ = 30 * (periodicCliffordFourthCorrection s ^ m /
        ((s ^ 2) ^ 4) ^ m) := by rw [div_pow]
    _ ≤ 30 * ((2 : ℝ) ^ (7 / 46 : ℝ) /
        ((s ^ 2) ^ 4) ^ m) := by
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hpow hden0) (by norm_num)
    _ = 30 * (2 : ℝ) ^ (7 / 46 : ℝ) /
        ((s ^ 2) ^ 4) ^ m := by ring

end

end TomographyOracleCore
