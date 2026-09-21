import TomographyOracleCore.Revision.FinitePrecisionPotential
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Nat.Log

/-! Entirely rational precision and iteration schedules for the executable
matrix solver. Their analytic inequalities are proved by exact arithmetic.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open FinitePrecision

set_option maxHeartbeats 1000000

def rationalStepSize (D : ℕ) (gamma : ℚ) : ℚ :=
  gamma / (2 * ((D + 1 : ℕ) : ℚ) ^ 2)

def rationalSpectralTolerance (gamma : ℚ) : ℚ := gamma / 4

def rationalProjectionTolerance (D : ℕ) (gamma : ℚ) : ℚ :=
  rationalStepSize D gamma * gamma / 10

def rationalInnerTolerance (D : ℕ) (gamma : ℚ) : ℚ :=
  rationalProjectionTolerance D gamma ^ 2 / 4

def rationalInnerCount (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.ceil (24 / rationalProjectionTolerance D gamma ^ 2)

def rationalProjectionPrecision (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.clog 2 (7 * (D + 1) * D ^ 2 * (rationalInnerCount D gamma + 2) ^ 2)

def rationalOuterCount (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.ceil (8 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2)

theorem rationalStepSize_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < rationalStepSize D gamma := by
  unfold rationalStepSize
  positivity

theorem rationalProjectionTolerance_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < rationalProjectionTolerance D gamma := by
  exact div_pos (mul_pos (rationalStepSize_pos D hgamma) hgamma) (by norm_num)

theorem rationalInnerTolerance_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < rationalInnerTolerance D gamma := by
  exact div_pos (sq_pos_of_pos (rationalProjectionTolerance_pos D hgamma)) (by norm_num)

@[simp] theorem cast_rationalStepSize (D : ℕ) (gamma : ℚ) :
    (rationalStepSize D gamma : ℝ) =
      (gamma : ℝ) / (2 * ((D + 1 : ℕ) : ℝ) ^ 2) := by
  simp only [rationalStepSize, Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat]

@[simp] theorem cast_rationalProjectionTolerance (D : ℕ) (gamma : ℚ) :
    (rationalProjectionTolerance D gamma : ℝ) =
      (rationalStepSize D gamma : ℝ) * (gamma : ℝ) / 10 := by
  simp only [rationalProjectionTolerance, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]

@[simp] theorem cast_rationalSpectralTolerance (gamma : ℚ) :
    (rationalSpectralTolerance gamma : ℝ) = (gamma : ℝ) / 4 := by
  simp only [rationalSpectralTolerance, Rat.cast_div, Rat.cast_ofNat]

@[simp] theorem cast_rationalInnerTolerance (D : ℕ) (gamma : ℚ) :
    (rationalInnerTolerance D gamma : ℝ) =
      (rationalProjectionTolerance D gamma : ℝ) ^ 2 / 4 := by
  simp only [rationalInnerTolerance, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]

theorem rationalOuterCount_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < rationalOuterCount D gamma := by
  change 0 < Nat.ceil (8 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2)
  apply Nat.ceil_pos.mpr
  positivity

theorem rationalOuterCount_budget (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    8 * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ (rationalOuterCount D gamma : ℝ) * (gamma : ℝ) ^ 2 := by
  have hc : 8 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2 ≤ (rationalOuterCount D gamma : ℚ) :=
    Nat.le_ceil _
  have hb : 8 * ((D + 1 : ℕ) : ℚ) ^ 2 ≤ (rationalOuterCount D gamma : ℚ) * gamma ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hgamma)).1 hc
  exact_mod_cast hb

theorem rationalInnerCount_budget (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    24 ≤ ((rationalInnerCount D gamma : ℝ) + 3) *
      (rationalProjectionTolerance D gamma : ℝ) ^ 2 := by
  have heps := rationalProjectionTolerance_pos D hgamma
  have hc : 24 / rationalProjectionTolerance D gamma ^ 2 ≤ (rationalInnerCount D gamma : ℚ) :=
    Nat.le_ceil _
  have hb := (div_le_iff₀ (sq_pos_of_pos heps)).1 hc
  have hb' : (24 : ℝ) ≤ (rationalInnerCount D gamma : ℝ) *
      (rationalProjectionTolerance D gamma : ℝ) ^ 2 := by exact_mod_cast hb
  nlinarith [sq_nonneg (rationalProjectionTolerance D gamma : ℝ)]

theorem rationalProjectionPrecision_budget (D : ℕ) (gamma : ℚ) :
    7 * (D + 1) * D ^ 2 * (rationalInnerCount D gamma + 2) ^ 2 ≤
      2 ^ rationalProjectionPrecision D gamma :=
  Nat.le_pow_clog (by norm_num) _

/-- The exact rational schedule discharges every scalar condition of the
outer perturbed subgradient convergence theorem. -/
theorem rationalSchedule_budget (D : ℕ) {gamma : ℚ}
    (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1) :
    0 < (rationalStepSize D gamma : ℝ) ∧
      (rationalStepSize D gamma : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ (gamma : ℝ) / 2 ∧
      0 ≤ (rationalProjectionTolerance D gamma : ℝ) ∧
      (rationalProjectionTolerance D gamma : ℝ) ≤ 1 ∧
      4 ≤ (rationalStepSize D gamma : ℝ) *
        (rationalOuterCount D gamma : ℝ) * (gamma : ℝ) := by
  have hG : (1 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 D
  have ht := explicit_precision_schedule hG (Rat.cast_pos.mpr hgamma)
    (show (gamma : ℝ) ≤ 1 by exact_mod_cast hgamma_le)
    (rationalOuterCount D gamma) (rationalOuterCount_budget D hgamma)
  simpa only [cast_rationalProjectionTolerance, cast_rationalStepSize] using ht

theorem rationalStepSize_radius_budget (D : ℕ) {gamma : ℚ}
    (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1) :
    (rationalStepSize D gamma : ℝ) * ((D + 1 : ℕ) : ℝ) ≤ 1 := by
  have hb := rationalSchedule_budget D hgamma hgamma_le
  have hG : (1 : ℝ) ≤ ((D + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 D
  have hg : (gamma : ℝ) ≤ 1 := by exact_mod_cast hgamma_le
  have hmul := mul_nonneg hb.1.le
    (show 0 ≤ ((D + 1 : ℕ) : ℝ) ^ 2 - ((D + 1 : ℕ) : ℝ) by nlinarith)
  nlinarith [hb.2.1]

#print axioms rationalSchedule_budget

end TomographyOracleCore.Revision.MatrixSolver
