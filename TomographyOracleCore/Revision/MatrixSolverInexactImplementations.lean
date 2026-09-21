import TomographyOracleCore.Revision.MatrixSolverInexactConvergence
import TomographyOracleCore.Revision.MatrixSolverInexactSampleSchedule

/-! Concrete implementations of the reusable rational solver: explicit
projector-array channel evaluation and explicit calibrated-channel
evaluation (such as the periodic rational Pauli implementation).
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def rationalProjectorSolveDense (hD : 0 < D)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) :
    DenseMatrix D QComplex :=
  rationalMatrixSolveDense hD (rationalProjectiveChannel P) Q gamma

def rationalProjectorSolve (hD : 0 < D)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) :
    Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalProjectorSolveDense hD P Q gamma)

theorem rationalProjectorSolve_feasible (hD : 0 < D)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) (hgamma : 0 < gamma) :
    QFeasible (rationalProjectorSolve hD P Q gamma) :=
  rationalMatrixSolve_feasible hD _ Q gamma hgamma

/-- Full computational correctness for a supplied rational measurement
projector array. The channel is evaluated by its literal finite sums. -/
theorem rationalProjectorSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (hP : ∀ e b, castQMatrix (P e b) = finiteUnitaryMeasurementProjector (U e) b)
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (rationalProjectorSolve hD P Q gamma))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + (gamma : ℝ) :=
  rationalMatrixSolve_fit hD U _ (cast_rationalProjectiveChannel U P hP)
    Q hQ gamma hgamma hgamma_le sigma

def rationalCalibratedSolveDense (hD : 0 < D) (L : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) :
    DenseMatrix D QComplex :=
  rationalMatrixSolveDense hD (rationalProjectiveFromCalibrated L) Q gamma

def rationalCalibratedSolve (hD : 0 < D) (L : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) :
    Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalCalibratedSolveDense hD L Q gamma)

theorem rationalCalibratedSolve_feasible (hD : 0 < D) (L : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) (hgamma : 0 < gamma) :
    QFeasible (rationalCalibratedSolve hD L Q gamma) :=
  rationalMatrixSolve_feasible hD _ Q gamma hgamma

/-- A proved calibrated rational channel evaluator plugs directly into
the complete rational solver. -/
theorem rationalCalibratedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (L : RationalMatrixOperator D)
    (hL : ∀ A, castQMatrix (L A) = finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A))
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (rationalCalibratedSolve hD L Q gamma))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + (gamma : ℝ) :=
  rationalMatrixSolve_fit hD U _ (cast_rationalProjectiveFromCalibrated U L hL)
    Q hQ gamma hgamma hgamma_le sigma

/-- The fully rational sample-count choice is sufficient for the paper's
statistical accuracy without a square-root computation. -/
theorem rationalCalibratedSolve_statistical_fit (hD : 0 < D) {T : ℕ} (hT : 0 < T)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (L : RationalMatrixOperator D)
    (hL : ∀ A, castQMatrix (L A) = finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A))
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (rationalCalibratedSolve hD L Q (rationalSampleTolerance T)))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + Real.sqrt ((D : ℝ) / T) := by
  exact (rationalCalibratedSolve_fit hD U L hL Q hQ _
    (rationalSampleTolerance_pos hT) (rationalSampleTolerance_le_one hT) sigma).trans
      (add_le_add le_rfl (rationalSampleTolerance_le_statistical hD hT))

#print axioms rationalProjectorSolve_fit
#print axioms rationalCalibratedSolve_statistical_fit

end TomographyOracleCore.Revision.MatrixSolver
