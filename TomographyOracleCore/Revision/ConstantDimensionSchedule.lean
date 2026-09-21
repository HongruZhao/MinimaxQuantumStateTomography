import TomographyOracleCore.Revision.ConstantDimensionSolver
import TomographyOracleCore.Revision.MatrixSolverInexactSchedule
namespace TomographyOracleCore.Revision.MatrixSolver
open FinitePrecision
set_option maxHeartbeats 1000000

def dimensionRationalGradientSquareBudget (D : ℕ) : ℚ := (13 / 4 : ℚ) * ((D : ℚ) + 1)
@[simp] theorem cast_dimensionRationalGradientSquareBudget (D : ℕ) :
    (dimensionRationalGradientSquareBudget D : ℝ) = periodicGradientSquareBudget D := by
  simp [dimensionRationalGradientSquareBudget, periodicGradientSquareBudget]

def dimensionRationalStepSize (D : ℕ) (gamma : ℚ) : ℚ :=
  gamma / (2 * dimensionRationalGradientSquareBudget D)
def dimensionRationalProjectionTolerance (D : ℕ) (gamma : ℚ) : ℚ :=
  dimensionRationalStepSize D gamma * gamma / 10
def dimensionRationalInnerTolerance (D : ℕ) (gamma : ℚ) : ℚ :=
  dimensionRationalProjectionTolerance D gamma ^ 2 / 4
def dimensionRationalInnerCount (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.ceil (24 / dimensionRationalProjectionTolerance D gamma ^ 2)
def dimensionRationalProjectionPrecision (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.clog 2 (7 * (D + 1) * D ^ 2 * (dimensionRationalInnerCount D gamma + 2) ^ 2)
def dimensionRationalOuterCount (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.ceil (4 * dimensionRationalGradientSquareBudget D / gamma ^ 2)

theorem dimensionRationalStepSize_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < dimensionRationalStepSize D gamma := by
  unfold dimensionRationalStepSize dimensionRationalGradientSquareBudget
  positivity

theorem dimensionRationalProjectionTolerance_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < dimensionRationalProjectionTolerance D gamma := by
  exact div_pos (mul_pos (dimensionRationalStepSize_pos D hgamma) hgamma) (by norm_num)

theorem dimensionRationalInnerTolerance_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < dimensionRationalInnerTolerance D gamma := by
  exact div_pos (sq_pos_of_pos (dimensionRationalProjectionTolerance_pos D hgamma)) (by norm_num)

@[simp] theorem cast_dimensionRationalStepSize (D : ℕ) (gamma : ℚ) :
    (dimensionRationalStepSize D gamma : ℝ) =
      (gamma : ℝ) / (2 * periodicGradientSquareBudget D) := by
  simp only [dimensionRationalStepSize, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat,
    cast_dimensionRationalGradientSquareBudget]
@[simp] theorem cast_dimensionRationalProjectionTolerance (D : ℕ) (gamma : ℚ) :
    (dimensionRationalProjectionTolerance D gamma : ℝ) =
      (dimensionRationalStepSize D gamma : ℝ) * (gamma : ℝ) / 10 := by
  simp only [dimensionRationalProjectionTolerance, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
@[simp] theorem cast_dimensionRationalInnerTolerance (D : ℕ) (gamma : ℚ) :
    (dimensionRationalInnerTolerance D gamma : ℝ) =
      (dimensionRationalProjectionTolerance D gamma : ℝ) ^ 2 / 4 := by
  simp only [dimensionRationalInnerTolerance, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat]

theorem dimensionRationalOuterCount_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < dimensionRationalOuterCount D gamma := by
  apply Nat.ceil_pos.mpr
  unfold dimensionRationalGradientSquareBudget
  positivity

theorem dimensionRationalOuterCount_budget (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    4 * periodicGradientSquareBudget D ≤
      (dimensionRationalOuterCount D gamma : ℝ) * (gamma : ℝ) ^ 2 := by
  have hc : 4 * dimensionRationalGradientSquareBudget D / gamma ^ 2 ≤
      (dimensionRationalOuterCount D gamma : ℚ) := Nat.le_ceil _
  have hb := (div_le_iff₀ (sq_pos_of_pos hgamma)).mp hc
  have hb' : 4 * (dimensionRationalGradientSquareBudget D : ℝ) ≤
      (dimensionRationalOuterCount D gamma : ℝ) * (gamma : ℝ) ^ 2 := by exact_mod_cast hb
  simpa only [cast_dimensionRationalGradientSquareBudget] using hb'

theorem dimensionRationalInnerCount_budget (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    24 ≤ ((dimensionRationalInnerCount D gamma : ℝ) + 3) *
      (dimensionRationalProjectionTolerance D gamma : ℝ) ^ 2 := by
  have heps := dimensionRationalProjectionTolerance_pos D hgamma
  have hc : 24 / dimensionRationalProjectionTolerance D gamma ^ 2 ≤
      (dimensionRationalInnerCount D gamma : ℚ) := Nat.le_ceil _
  have hb := (div_le_iff₀ (sq_pos_of_pos heps)).mp hc
  have hb' : (24 : ℝ) ≤ (dimensionRationalInnerCount D gamma : ℝ) *
      (dimensionRationalProjectionTolerance D gamma : ℝ) ^ 2 := by exact_mod_cast hb
  nlinarith [sq_nonneg (dimensionRationalProjectionTolerance D gamma : ℝ)]

theorem dimensionRationalProjectionPrecision_budget (D : ℕ) (gamma : ℚ) :
    7 * (D + 1) * D ^ 2 * (dimensionRationalInnerCount D gamma + 2) ^ 2 ≤
      2 ^ dimensionRationalProjectionPrecision D gamma := Nat.le_pow_clog (by norm_num) _

theorem dimensionRationalSchedule_budget (D : ℕ) {gamma : ℚ}
    (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1) :
    0 < (dimensionRationalStepSize D gamma : ℝ) ∧
      (dimensionRationalStepSize D gamma : ℝ) * periodicGradientSquareBudget D ≤ (gamma : ℝ) / 2 ∧
      0 ≤ (dimensionRationalProjectionTolerance D gamma : ℝ) ∧
      (dimensionRationalProjectionTolerance D gamma : ℝ) ≤ 1 ∧
      2 ≤ (dimensionRationalStepSize D gamma : ℝ) *
        (dimensionRationalOuterCount D gamma : ℝ) * (gamma : ℝ) := by
  have hg : 0 < (gamma : ℝ) := Rat.cast_pos.mpr hgamma
  have hg1 : (gamma : ℝ) ≤ 1 := by exact_mod_cast hgamma_le
  have hG := periodicGradientSquareBudget_pos D
  have hG1 : 1 ≤ periodicGradientSquareBudget D := by
    unfold periodicGradientSquareBudget
    have : (0 : ℝ) ≤ D := by positivity
    nlinarith
  have hh : 0 < (dimensionRationalStepSize D gamma : ℝ) :=
    Rat.cast_pos.mpr (dimensionRationalStepSize_pos D hgamma)
  have hid : (dimensionRationalStepSize D gamma : ℝ) * periodicGradientSquareBudget D =
      (gamma : ℝ) / 2 := by
    rw [cast_dimensionRationalStepSize]
    field_simp
  have heps : 0 ≤ (dimensionRationalProjectionTolerance D gamma : ℝ) :=
    (Rat.cast_pos.mpr (dimensionRationalProjectionTolerance_pos D hgamma)).le
  have hstep_le : (dimensionRationalStepSize D gamma : ℝ) ≤ (gamma : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hG1 hh.le
    nlinarith
  have heps_le : (dimensionRationalProjectionTolerance D gamma : ℝ) ≤ 1 := by
    rw [cast_dimensionRationalProjectionTolerance]
    have hp := mul_le_mul_of_nonneg_left hg1 hh.le
    nlinarith
  have houter : 2 ≤ (dimensionRationalStepSize D gamma : ℝ) *
      (dimensionRationalOuterCount D gamma : ℝ) * (gamma : ℝ) := by
    have hb := mul_le_mul_of_nonneg_left (dimensionRationalOuterCount_budget D hgamma) hh.le
    apply (mul_le_mul_iff_left₀ hg).mp
    nlinarith
  exact ⟨hh, hid.le, heps, heps_le, houter⟩

theorem dimensionRationalStepSize_radius_budget (D : ℕ) {gamma : ℚ}
    (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1) :
    (dimensionRationalStepSize D gamma : ℝ) * ((D + 1 : ℕ) : ℝ) ≤ 1 := by
  have hb := dimensionRationalSchedule_budget D hgamma hgamma_le
  have hG : ((D + 1 : ℕ) : ℝ) ≤ periodicGradientSquareBudget D := by
    unfold periodicGradientSquareBudget
    push_cast
    have : (0 : ℝ) ≤ D := by positivity
    nlinarith
  have hg : (gamma : ℝ) ≤ 1 := by exact_mod_cast hgamma_le
  have hp := mul_le_mul_of_nonneg_left hG hb.1.le
  linarith [hb.2.1]

/-- Fully explicit outer count used by the executable periodic solver. -/
theorem dimensionRationalOuterCount_formula (D : ℕ) (gamma : ℚ) :
    dimensionRationalOuterCount D gamma = Nat.ceil (13 * ((D : ℚ) + 1) / gamma ^ 2) := by
  unfold dimensionRationalOuterCount dimensionRationalGradientSquareBudget
  congr 1
  ring

/-- The inner count likewise loses two powers of dimension. -/
theorem dimensionRationalInnerCount_formula (D : ℕ) {gamma : ℚ} (hgamma : gamma ≠ 0) :
    dimensionRationalInnerCount D gamma =
      Nat.ceil (101400 * ((D : ℚ) + 1) ^ 2 / gamma ^ 4) := by
  unfold dimensionRationalInnerCount dimensionRationalProjectionTolerance
    dimensionRationalStepSize dimensionRationalGradientSquareBudget
  congr 1
  field_simp
  ring

end TomographyOracleCore.Revision.MatrixSolver
