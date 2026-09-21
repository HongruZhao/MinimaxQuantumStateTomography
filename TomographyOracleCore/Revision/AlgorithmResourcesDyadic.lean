import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Executable dyadic rounding of rational inputs, with its error and actual
integer-word size bounds. This file asserts no cost for an unimplemented
matrix solver. The represented output is an integer numerator over 2^s.
-/

namespace TomographyOracleCore.Revision.AlgorithmResources

/-- An executable numerator calculation on a rational input. -/
def dyadicNumerator (s : ℕ) (q : ℚ) : ℤ := ⌊q * (2 : ℚ) ^ s⌋

/-- Round down to the dyadic grid with denominator 2^s. -/
def dyadicRound (s : ℕ) (q : ℚ) : ℚ :=
  (dyadicNumerator s q : ℚ) / (2 : ℚ) ^ s

theorem dyadicRound_mul (s : ℕ) (q : ℚ) :
    dyadicRound s q * (2 : ℚ) ^ s = (dyadicNumerator s q : ℚ) := by
  exact div_mul_cancel₀ _ (ne_of_gt (pow_pos (by norm_num) s))

theorem dyadicRound_le (s : ℕ) (q : ℚ) : dyadicRound s q ≤ q := by
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) s)).2
  exact Int.floor_le _

/-- The actual rounded rational differs from its input by less than one grid step. -/
theorem dyadicRound_error (s : ℕ) (q : ℚ) :
    0 ≤ q - dyadicRound s q ∧ q - dyadicRound s q < 1 / (2 : ℚ) ^ s := by
  refine ⟨sub_nonneg.mpr (dyadicRound_le s q), ?_⟩
  apply (lt_div_iff₀ (pow_pos (by norm_num : (0 : ℚ) < 2) s)).2
  have hlt := Int.lt_floor_add_one (q * (2 : ℚ) ^ s)
  have heq := dyadicRound_mul s q
  change q * (2 : ℚ) ^ s < (dyadicNumerator s q : ℚ) + 1 at hlt
  nlinarith

theorem dyadicRound_abs_error (s : ℕ) (q : ℚ) :
    |q - dyadicRound s q| < 1 / (2 : ℚ) ^ s := by
  rw [abs_of_nonneg (dyadicRound_error s q).1]
  exact (dyadicRound_error s q).2

/-- Casting the computed rational to a real number preserves the error guarantee. -/
theorem dyadicRound_real_error (s : ℕ) (q : ℚ) :
    |(q : ℝ) - (dyadicRound s q : ℝ)| < 1 / (2 : ℝ) ^ s := by
  have h : ((|q - dyadicRound s q| : ℚ) : ℝ) <
      ((1 / (2 : ℚ) ^ s : ℚ) : ℝ) := Rat.cast_lt.mpr (dyadicRound_abs_error s q)
  simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
    Rat.cast_pow, Rat.cast_ofNat] using h

/-- A magnitude bound on an input bounds the unreduced output numerator. -/
theorem dyadicNumerator_abs_le (s B : ℕ) (q : ℚ) (hq : |q| ≤ B) :
    (dyadicNumerator s q).natAbs ≤ (B + 1) * 2 ^ s := by
  have hp : (0 : ℚ) < 2 ^ s := pow_pos (by norm_num) s
  have hp1 : (1 : ℚ) ≤ 2 ^ s := one_le_pow₀ (by norm_num)
  have hupper := Int.floor_le (q * (2 : ℚ) ^ s)
  have hlower := Int.lt_floor_add_one (q * (2 : ℚ) ^ s)
  change (dyadicNumerator s q : ℚ) ≤ q * (2 : ℚ) ^ s at hupper
  change q * (2 : ℚ) ^ s < (dyadicNumerator s q : ℚ) + 1 at hlower
  have hq' := abs_le.mp hq
  have hqlo := mul_le_mul_of_nonneg_right hq'.1 hp.le
  have hqhi := mul_le_mul_of_nonneg_right hq'.2 hp.le
  have ha : |(dyadicNumerator s q : ℚ)| ≤ ((B : ℚ) + 1) * 2 ^ s := by
    apply abs_le.mpr
    constructor <;> nlinarith
  have hz : |dyadicNumerator s q| ≤ (((B + 1) * 2 ^ s : ℕ) : ℤ) := by
    exact_mod_cast ha
  rw [← Int.natCast_natAbs] at hz
  exact_mod_cast hz

/-- Binary length of the actual numerator grows additively in the precision. -/
theorem dyadicNumerator_size_le (s B : ℕ) (q : ℚ) (hq : |q| ≤ B) :
    (dyadicNumerator s q).natAbs.size ≤ (B + 1).size + s := by
  apply Nat.size_le.mpr
  calc
    (dyadicNumerator s q).natAbs ≤ (B + 1) * 2 ^ s :=
      dyadicNumerator_abs_le s B q hq
    _ < 2 ^ (B + 1).size * 2 ^ s :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self _) (Nat.pow_pos (by decide))
    _ = 2 ^ ((B + 1).size + s) := (Nat.pow_add _ _ _).symm

theorem dyadicDenominator_size (s : ℕ) : (2 ^ s).size = s + 1 := Nat.size_pow

#print axioms dyadicRound_real_error
#print axioms dyadicNumerator_size_le

end TomographyOracleCore.Revision.AlgorithmResources
