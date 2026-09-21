import TomographyOracleCore.Revision.AlgorithmResourcesPowerNorm
import Mathlib.Data.Rat.Floor

/-! Computable strict shifts and explicit rational iteration budgets. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixReduction
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {d : ℕ}

/-- A rational upper bound strictly larger than the input operator norm. -/
def qShiftBound (A : Matrix (Fin d) (Fin d) QComplex) : ℚ :=
  1 + ∑ i, ∑ j, (|(A i j).re| + |(A i j).im|)

def qShiftMinus (A : Matrix (Fin d) (Fin d) QComplex) :
    Matrix (Fin d) (Fin d) QComplex := qShiftBound A • 1 - A

/-- The count is explicit and executable. Its dependence on the magnitude
bound is exposed; this is not a claim of polynomial dependence on its logarithm. -/
def qPowerIterationCount (d : ℕ) (bound delta : ℚ) : ℕ :=
  d + Nat.ceil ((d : ℚ) * (2 * bound) / delta)

def qMinimumDirection (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (delta : ℚ) : Fin d → QComplex :=
  let B := qShiftMinus A
  let k := qPowerIterationCount d (qShiftBound A) delta
  qPowerColumn B k (qBestPowerColumn hD B k)

noncomputable section

theorem qShiftBound_pos (A : Matrix (Fin d) (Fin d) QComplex) : 0 < qShiftBound A := by
  unfold qShiftBound
  positivity

theorem qShiftBound_norm_lt (A : Matrix (Fin d) (Fin d) QComplex) :
    matrixOperatorNorm (castQMatrix A) < (qShiftBound A : ℝ) := by
  have he (z : QComplex) : ‖qComplexToComplex z‖ ≤ (|z.re| + |z.im| : ℚ) := by
    rw [qComplexToComplex_apply]
    calc
      ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ ≤
          ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
      _ = (|z.re| + |z.im| : ℚ) := by simp
  have hsum : (∑ i, ∑ j, ‖castQMatrix A i j‖) ≤
      ((∑ i, ∑ j, (|(A i j).re| + |(A i j).im|) : ℚ) : ℝ) := by
    push_cast
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    simpa only [castQMatrix_apply, Rat.cast_add, Rat.cast_abs] using he (A i j)
  have hn := (matrixOperatorNorm_le_sum_entries (castQMatrix A)).trans hsum
  unfold qShiftBound
  push_cast
  push_cast at hn
  linarith

@[simp] theorem castQMatrix_rat_smul (q : ℚ) (A : Matrix (Fin d) (Fin d) QComplex) :
    castQMatrix (q • A) = (q : ℝ) • castQMatrix A := by
  ext i j
  simp [castQMatrix, Matrix.map_apply, qComplexToComplex_apply, QuadraticAlgebra.re_smul,
    QuadraticAlgebra.im_smul, Complex.real_smul]
  ring

@[simp] theorem castQMatrix_one :
    castQMatrix (1 : Matrix (Fin d) (Fin d) QComplex) = 1 := by
  exact Matrix.map_one qComplexToComplex (map_zero _) (map_one _)

@[simp] theorem castQMatrix_sub (A B : Matrix (Fin d) (Fin d) QComplex) :
    castQMatrix (A - B) = castQMatrix A - castQMatrix B := by
  ext i j
  exact map_sub qComplexToComplex (A i j) (B i j)

@[simp] theorem castQMatrix_neg (A : Matrix (Fin d) (Fin d) QComplex) :
    castQMatrix (-A) = -castQMatrix A := by
  ext i j
  exact map_neg qComplexToComplex (A i j)

@[simp] theorem castQMatrix_shiftMinus (A : Matrix (Fin d) (Fin d) QComplex) :
    castQMatrix (qShiftMinus A) = (qShiftBound A : ℝ) • 1 - castQMatrix A := by
  simp [qShiftMinus]

theorem qShiftMinus_posDef (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) : (castQMatrix (qShiftMinus A)).PosDef := by
  rw [castQMatrix_shiftMinus]
  exact scalar_shift_posDef _ hA _ (qShiftBound_norm_lt A)

theorem qShiftMinus_norm_le (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex) :
    matrixOperatorNorm (castQMatrix (qShiftMinus A)) ≤ 2 * (qShiftBound A : ℝ) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hD
  rw [castQMatrix_shiftMinus]
  change ‖(qShiftBound A : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) - castQMatrix A‖ ≤ _
  calc
    _ ≤ ‖(qShiftBound A : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ)‖ + ‖castQMatrix A‖ :=
      norm_sub_le _ _
    _ = (qShiftBound A : ℝ) + matrixOperatorNorm (castQMatrix A) := by
      have hp : 0 < (qShiftBound A : ℝ) := by exact_mod_cast qShiftBound_pos A
      rw [norm_smul, norm_one, mul_one, Real.norm_eq_abs, abs_of_pos hp]
      rfl
    _ ≤ 2 * (qShiftBound A : ℝ) := by linarith [qShiftBound_norm_lt A]

theorem qPowerIterationCount_ge_dimension (d : ℕ) (bound delta : ℚ) :
    d ≤ qPowerIterationCount d bound delta := Nat.le_add_right _ _

theorem qPowerIterationCount_budget (d : ℕ) (bound delta : ℚ) (hdelta : 0 < delta) :
    (d : ℝ) * (2 * (bound : ℝ)) ≤
      (((2 * qPowerIterationCount d bound delta : ℕ) + 1 : ℝ)) * (delta : ℝ) := by
  have hceil := Nat.le_ceil ((d : ℚ) * (2 * bound) / delta)
  have hk : (Nat.ceil ((d : ℚ) * (2 * bound) / delta) : ℚ) ≤
      (2 * qPowerIterationCount d bound delta : ℕ) + 1 := by
    exact_mod_cast (show Nat.ceil ((d : ℚ) * (2 * bound) / delta) ≤
      2 * qPowerIterationCount d bound delta + 1 by unfold qPowerIterationCount; omega)
  have hrat := (div_le_iff₀ hdelta).mp (hceil.trans hk)
  exact_mod_cast hrat

#print axioms qShiftMinus_posDef
#print axioms qPowerIterationCount_budget

end
end TomographyOracleCore.Revision.AlgorithmResources
