import TomographyOracleCore.PeriodicCliffordFourthTransferArithmetic

namespace TomographyOracleCore

/-!
# The final universal-constant conversion for the shallow fourth moment

The transfer arithmetic gives `30 * 2^(7/46) / D^4`.  This file proves,
with exact rational inequalities, that this is bounded by the normalized
constant-`34` fourth-projector moment once `D >= 65536`.
-/

noncomputable section

/-- A convenient exact rational upper bound for the accumulated block
correction. -/
theorem two_rpow_seven_div_fortysix_lt_nine_eighth :
    (2 : ℝ) ^ (7 / 46 : ℝ) < 9 / 8 := by
  have hexp : (7 / 46 : ℝ) < (6 : ℝ)⁻¹ := by norm_num
  have hmono := Real.rpow_lt_rpow_of_exponent_lt
    (by norm_num : (1 : ℝ) < 2) hexp
  have hroot : (2 : ℝ) ^ (6 : ℝ)⁻¹ < 9 / 8 := by
    rw [Real.rpow_inv_lt_iff_of_pos (by norm_num) (by norm_num) (by norm_num)]
    norm_num [Real.rpow_natCast]
  exact hmono.trans hroot

/-- For the dimensions forced by the physical block condition, the
unnormalized `D^-4` bound implies the conventional rising-factorial bound
with universal constant `34`. -/
theorem periodicCliffordFourth_constant34_conversion
    {D : ℕ} (hD : 65536 ≤ D) :
    30 * (2 : ℝ) ^ (7 / 46 : ℝ) / (D : ℝ) ^ 4 ≤
      34 / ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2) *
        ((D : ℝ) + 3)) := by
  let d : ℝ := D
  have hdLower : (65536 : ℝ) ≤ d := by
    dsimp [d]
    exact_mod_cast hD
  have hd : 0 < d := by linarith
  have hd1 : 0 < d + 1 := by positivity
  have hd2 : 0 < d + 2 := by positivity
  have hd3 : 0 < d + 3 := by positivity
  have hfac1 : d + 1 ≤ (1001 / 1000 : ℝ) * d := by
    nlinarith
  have hfac2 : d + 2 ≤ (1001 / 1000 : ℝ) * d := by
    nlinarith
  have hfac3 : d + 3 ≤ (1001 / 1000 : ℝ) * d := by
    nlinarith
  have h12 : (d + 1) * (d + 2) ≤
      ((1001 / 1000 : ℝ) * d) ^ 2 := by
    calc
      (d + 1) * (d + 2) ≤
          ((1001 / 1000 : ℝ) * d) * (d + 2) :=
        mul_le_mul_of_nonneg_right hfac1 (by positivity)
      _ ≤ ((1001 / 1000 : ℝ) * d) *
          ((1001 / 1000 : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hfac2 (by positivity)
      _ = ((1001 / 1000 : ℝ) * d) ^ 2 := by ring
  have h123 : (d + 1) * (d + 2) * (d + 3) ≤
      ((1001 / 1000 : ℝ) * d) ^ 3 := by
    calc
      (d + 1) * (d + 2) * (d + 3) ≤
          ((1001 / 1000 : ℝ) * d) ^ 2 * (d + 3) :=
        mul_le_mul_of_nonneg_right h12 (by positivity)
      _ ≤ ((1001 / 1000 : ℝ) * d) ^ 2 *
          ((1001 / 1000 : ℝ) * d) :=
        mul_le_mul_of_nonneg_left hfac3 (by positivity)
      _ = ((1001 / 1000 : ℝ) * d) ^ 3 := by ring
  have hc : (2 : ℝ) ^ (7 / 46 : ℝ) ≤ 9 / 8 :=
    (two_rpow_seven_div_fortysix_lt_nine_eighth).le
  have hcoef :
      30 * (9 / 8 : ℝ) * (1001 / 1000 : ℝ) ^ 3 < 34 := by
    norm_num
  have hnum :
      (30 * (2 : ℝ) ^ (7 / 46 : ℝ)) *
          (d * (d + 1) * (d + 2) * (d + 3)) ≤
        34 * d ^ 4 := by
    have hcNonneg : 0 ≤ (2 : ℝ) ^ (7 / 46 : ℝ) :=
      Real.rpow_nonneg (by norm_num) _
    have hprod :
        d * (d + 1) * (d + 2) * (d + 3) ≤
          d * (((1001 / 1000 : ℝ) * d) ^ 3) := by
      calc
        d * (d + 1) * (d + 2) * (d + 3) =
            d * ((d + 1) * (d + 2) * (d + 3)) := by ring
        _ ≤ d * (((1001 / 1000 : ℝ) * d) ^ 3) :=
          mul_le_mul_of_nonneg_left h123 hd.le
    calc
      (30 * (2 : ℝ) ^ (7 / 46 : ℝ)) *
          (d * (d + 1) * (d + 2) * (d + 3)) ≤
          (30 * (2 : ℝ) ^ (7 / 46 : ℝ)) *
            (d * (((1001 / 1000 : ℝ) * d) ^ 3)) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg (by norm_num) hcNonneg)
      _ ≤ (30 * (9 / 8 : ℝ)) *
            (d * (((1001 / 1000 : ℝ) * d) ^ 3)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)
      _ = (30 * (9 / 8 : ℝ) * (1001 / 1000 : ℝ) ^ 3) * d ^ 4 := by
        ring
      _ ≤ 34 * d ^ 4 :=
        mul_le_mul_of_nonneg_right hcoef.le (pow_nonneg hd.le 4)
  change 30 * (2 : ℝ) ^ (7 / 46 : ℝ) / d ^ 4 ≤
    34 / (d * (d + 1) * (d + 2) * (d + 3))
  rw [div_le_div_iff₀ (pow_pos hd 4)
    (mul_pos (mul_pos (mul_pos hd hd1) hd2) hd3)]
  exact hnum

end

end TomographyOracleCore
