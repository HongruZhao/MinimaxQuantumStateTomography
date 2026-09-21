import TomographyOracleCore.Revision.MatrixSolverRationalInput
import TomographyOracleCore.Revision.AlgorithmResourcesDense

/-! Rational channel conversion for reusing the proved solver with an
explicit projector evaluator or an explicit Pauli multiplier evaluator.
The conversion is ordinary rational matrix arithmetic.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

abbrev RationalMatrixOperator (D : ℕ) :=
  Matrix (Fin D) (Fin D) QComplex → Matrix (Fin D) (Fin D) QComplex

def rationalCalibratedFromProjective {D : ℕ} (M : RationalMatrixOperator D)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  materializeMatrix (((D + 1 : ℕ) : ℚ) • M A - A.trace • 1)

def rationalProjectiveFromCalibrated {D : ℕ} (L : RationalMatrixOperator D)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  materializeMatrix (((D + 1 : ℕ) : ℚ)⁻¹ • (L A + A.trace • 1))

theorem cast_rationalCalibratedFromProjective {D : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (A : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalCalibratedFromProjective M A) =
      finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A) := by
  rw [rationalCalibratedFromProjective, materializeMatrix_eq, castQMatrix_sub,
    castQMatrix_rat_smul, hM, castQMatrix_qcomplex_smul, qComplexToComplex_trace,
    castQMatrix_one, finiteUnitaryFullCalibratedLinearChannel_apply]
  congr 1

theorem cast_rationalProjectiveFromCalibrated {D : ℕ} {E : Type*}
    [Fintype E] [Nonempty E] (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (L : RationalMatrixOperator D)
    (hL : ∀ A, castQMatrix (L A) = finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A))
    (A : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalProjectiveFromCalibrated L A) =
      finiteUnitaryProjectiveLinearChannel U (castQMatrix A) := by
  rw [rationalProjectiveFromCalibrated, materializeMatrix_eq, castQMatrix_rat_smul,
    castQMatrix_add, hL, castQMatrix_qcomplex_smul, qComplexToComplex_trace,
    castQMatrix_one, finiteUnitaryFullCalibratedLinearChannel_apply, sub_add_cancel,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  have hG : ((D + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero D
  simp only [Rat.cast_inv, Rat.cast_natCast]
  change ((((((D + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) * (((D + 1 : ℕ) : ℝ) : ℂ))) •
    finiteUnitaryProjectiveLinearChannel U (castQMatrix A) = _
  rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀ hG, one_smul]

theorem rationalCalibratedFromProjective_projectors {D : ℕ} {E : Type*} [Fintype E]
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (A : Matrix (Fin D) (Fin D) QComplex) :
    rationalCalibratedFromProjective (rationalProjectiveChannel P) A =
      rationalCalibratedChannel P A := by
  simp only [rationalCalibratedFromProjective, materializeMatrix_eq, rationalCalibratedChannel]

end TomographyOracleCore.Revision.MatrixSolver
