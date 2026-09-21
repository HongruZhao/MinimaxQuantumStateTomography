import TomographyOracleCore.LowerConstants
import TomographyOracleCore.LowerDimensionComparison
import Mathlib.Analysis.Complex.ExponentialBounds

namespace TomographyOracleCore

/-!
# The explicit dimension threshold in the Fano step

The manuscript chooses `D₀ = 514` solely so that the Grassmann packing
exponent is at least `4 log 2`, already for effective rank one.  This module
checks that tight numerical comparison in Lean.
-/

/-- At `D ≥ 514` and `m ≥ 1`, the exponent
`gamma₀ * m * (D-2)` dominates `4 log 2`. -/
theorem four_log_two_le_grassmann_exponent
    (D m : ℕ) (hD : 514 ≤ D) (hm : 1 ≤ m) :
    4 * Real.log 2 ≤
      grassmannGamma0 * (m : ℝ) * (lowerAmbientDimension D : ℝ) := by
  have hkNat : 512 ≤ lowerAmbientDimension D := by
    unfold lowerAmbientDimension
    omega
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hkReal : (512 : ℝ) ≤ (lowerAmbientDimension D : ℝ) := by
    exact_mod_cast hkNat
  have hproduct : (512 : ℝ) ≤
      (m : ℝ) * (lowerAmbientDimension D : ℝ) := by
    calc
      (512 : ℝ) = 1 * 512 := by ring
      _ ≤ (m : ℝ) * (lowerAmbientDimension D : ℝ) :=
        mul_le_mul hmReal hkReal (by norm_num) (by positivity)
  have hnumeric : 4 * Real.log 2 < (25 : ℝ) / 9 := by
    nlinarith [Real.log_two_lt_d9]
  calc
    4 * Real.log 2 ≤ (25 : ℝ) / 9 := hnumeric.le
    _ = grassmannGamma0 * 512 := by
      norm_num [grassmannGamma0]
    _ ≤ grassmannGamma0 *
        ((m : ℝ) * (lowerAmbientDimension D : ℝ)) :=
      mul_le_mul_of_nonneg_left hproduct grassmannGamma0_pos.le
    _ = grassmannGamma0 * (m : ℝ) *
        (lowerAmbientDimension D : ℝ) := by ring

/-- Any supplied packing logarithm at least the manuscript exponent therefore
satisfies the exact coarse Fano threshold. -/
theorem four_log_two_le_of_grassmann_log_cardinality
    (D m : ℕ) (logCardinality : ℝ)
    (hD : 514 ≤ D) (hm : 1 ≤ m)
    (hpacking :
      grassmannGamma0 * (m : ℝ) * (lowerAmbientDimension D : ℝ) ≤
        logCardinality) :
    4 * Real.log 2 ≤ logCardinality :=
  (four_log_two_le_grassmann_exponent D m hD hm).trans hpacking

end TomographyOracleCore
