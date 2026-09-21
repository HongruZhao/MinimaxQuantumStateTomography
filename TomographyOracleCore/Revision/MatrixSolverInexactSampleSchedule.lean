import TomographyOracleCore.Revision.MatrixSolverInexactSchedule
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Polynomial integer schedules for the fully rational accuracy gamma=1/T.
This deliberately conservative choice is below the statistical tolerance
sqrt(D/T) whenever the dimension and sample count are positive.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

set_option maxHeartbeats 1000000

def rationalSampleTolerance (T : ℕ) : ℚ := 1 / (T : ℚ)

theorem rationalSampleTolerance_pos {T : ℕ} (hT : 0 < T) :
    0 < rationalSampleTolerance T := by
  unfold rationalSampleTolerance
  positivity

theorem rationalSampleTolerance_le_one {T : ℕ} (hT : 0 < T) :
    rationalSampleTolerance T ≤ 1 := by
  unfold rationalSampleTolerance
  apply (div_le_one₀ (by exact_mod_cast hT)).2
  exact_mod_cast Nat.succ_le_of_lt hT

theorem rationalSampleTolerance_le_statistical {D T : ℕ}
    (hD : 0 < D) (hT : 0 < T) :
    (rationalSampleTolerance T : ℝ) ≤ Real.sqrt ((D : ℝ) / (T : ℝ)) := by
  have hDr : (1 : ℝ) ≤ D := by exact_mod_cast Nat.succ_le_of_lt hD
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast Nat.succ_le_of_lt hT
  have hTp : (0 : ℝ) < T := by exact_mod_cast hT
  have hratio : (0 : ℝ) ≤ (D : ℝ) / (T : ℝ) := by positivity
  have hroot := Real.sq_sqrt hratio
  have hsmall : (1 / (T : ℝ)) ^ 2 ≤ (D : ℝ) / (T : ℝ) := by
    have hDT : (1 : ℝ) ≤ (D : ℝ) * (T : ℝ) := by nlinarith
    have hidL : (1 / (T : ℝ)) ^ 2 * (T : ℝ) ^ 2 = 1 := by field_simp
    have hidR : ((D : ℝ) / (T : ℝ)) * (T : ℝ) ^ 2 = (D : ℝ) * (T : ℝ) := by
      field_simp
    have hmul : (1 / (T : ℝ)) ^ 2 * (T : ℝ) ^ 2 ≤
        ((D : ℝ) / (T : ℝ)) * (T : ℝ) ^ 2 := by
      rw [hidL, hidR]
      exact hDT
    exact le_of_mul_le_mul_right hmul (sq_pos_of_pos hTp)
  have hnonneg := Real.sqrt_nonneg ((D : ℝ) / (T : ℝ))
  have hfinal : 1 / (T : ℝ) ≤ Real.sqrt ((D : ℝ) / (T : ℝ)) := by nlinarith
  simpa only [rationalSampleTolerance, Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using hfinal

theorem rationalStepSize_sample (D : ℕ) {T : ℕ} (hT : 0 < T) :
    rationalStepSize D (rationalSampleTolerance T) =
      1 / (2 * ((D + 1 : ℕ) : ℚ) ^ 2 * (T : ℚ)) := by
  have hG : ((D + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold rationalStepSize rationalSampleTolerance
  field_simp
  <;> ring

theorem rationalSpectralTolerance_sample {T : ℕ} (hT : 0 < T) :
    rationalSpectralTolerance (rationalSampleTolerance T) = 1 / (4 * (T : ℚ)) := by
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  unfold rationalSpectralTolerance rationalSampleTolerance
  field_simp
  <;> ring

theorem rationalProjectionTolerance_sample (D : ℕ) {T : ℕ} (hT : 0 < T) :
    rationalProjectionTolerance D (rationalSampleTolerance T) =
      1 / (20 * ((D + 1 : ℕ) : ℚ) ^ 2 * (T : ℚ) ^ 2) := by
  have hG : ((D + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [rationalProjectionTolerance, rationalStepSize_sample D hT]
  unfold rationalSampleTolerance
  field_simp
  <;> ring

theorem rationalInnerTolerance_sample (D : ℕ) {T : ℕ} (hT : 0 < T) :
    rationalInnerTolerance D (rationalSampleTolerance T) =
      1 / (1600 * ((D + 1 : ℕ) : ℚ) ^ 4 * (T : ℚ) ^ 4) := by
  have hG : ((D + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  rw [rationalInnerTolerance, rationalProjectionTolerance_sample D hT]
  field_simp
  <;> ring

/-- Exact outer loop length, an explicit polynomial in D and T. -/
theorem rationalOuterCount_sample (D : ℕ) {T : ℕ} (hT : 0 < T) :
    rationalOuterCount D (rationalSampleTolerance T) = 8 * (D + 1) ^ 2 * T ^ 2 := by
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  have hid : 8 * ((D + 1 : ℕ) : ℚ) ^ 2 / rationalSampleTolerance T ^ 2 =
      ((8 * (D + 1) ^ 2 * T ^ 2 : ℕ) : ℚ) := by
    unfold rationalSampleTolerance
    push_cast
    field_simp
    <;> ring
  rw [rationalOuterCount, hid, Nat.ceil_natCast]

/-- Exact inner projection loop parameter. The routine uses n+1 iterations. -/
theorem rationalInnerCount_sample (D : ℕ) {T : ℕ} (hT : 0 < T) :
    rationalInnerCount D (rationalSampleTolerance T) = 9600 * (D + 1) ^ 4 * T ^ 4 := by
  have hG : ((D + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have hTq : (T : ℚ) ≠ 0 := by exact_mod_cast hT.ne'
  have hid : 24 / rationalProjectionTolerance D (rationalSampleTolerance T) ^ 2 =
      ((9600 * (D + 1) ^ 4 * T ^ 4 : ℕ) : ℚ) := by
    rw [rationalProjectionTolerance_sample D hT]
    push_cast
    field_simp
    <;> ring
  rw [rationalInnerCount, hid, Nat.ceil_natCast]

theorem rationalProjectionPrecision_sample (D : ℕ) {T : ℕ} (hT : 0 < T) :
    rationalProjectionPrecision D (rationalSampleTolerance T) =
      Nat.clog 2 (7 * (D + 1) * D ^ 2 * (9600 * (D + 1) ^ 4 * T ^ 4 + 2) ^ 2) := by
  rw [rationalProjectionPrecision, rationalInnerCount_sample D hT]

#print axioms rationalOuterCount_sample
#print axioms rationalInnerCount_sample
#print axioms rationalSampleTolerance_le_statistical

end TomographyOracleCore.Revision.MatrixSolver
