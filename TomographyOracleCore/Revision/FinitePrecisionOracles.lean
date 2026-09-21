import TomographyOracleCore.Revision.AlgorithmResourcesPowerMinimum
import TomographyOracleCore.Revision.AlgorithmResourcesDense
import TomographyOracleCore.Revision.FinitePrecisionRationalProjection

/-! The actual rational power-iteration direction instantiated as a total
feasible density-matrix linear minimization routine. -/

namespace TomographyOracleCore.Revision.FinitePrecision

open AlgorithmResources MatrixReduction MatrixSolver Matrix
open scoped ComplexOrder BigOperators

variable {D : ℕ}

def qFallbackDirection (hD : 0 < D) : Fin D → QComplex :=
  Pi.single ⟨0, hD⟩ 1

theorem qFallbackDirection_ne_zero (hD : 0 < D) : qFallbackDirection hD ≠ 0 := by
  intro h
  have hx := congrArg (fun v : Fin D → QComplex => v ⟨0, hD⟩) h
  simpa [qFallbackDirection] using hx

/-- Eager implementation of the proved shifted power direction. -/
def qDenseMinimumDirection (hD : 0 < D)
    (A : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) : Fin D → QComplex :=
  qDenseBestPowerVector hD (qShiftMinus A)
    (qPowerIterationCount D (qShiftBound A) delta)

@[simp] theorem qDenseMinimumDirection_eq (hD : 0 < D)
    (A : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    qDenseMinimumDirection hD A delta = qMinimumDirection hD A delta := by
  rw [qDenseMinimumDirection, qDenseBestPowerVector_eq]
  rfl

/-- A total executable approximate linear minimizer. The fallback is used
only away from the Hermitian inputs occurring in the proved algorithm. -/
def qMinimumDensityOracle (hD : 0 < D) (delta : ℚ)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  qSafeNormalizedProjector (qDenseMinimumDirection hD A delta) (qFallbackDirection hD)

/-- The actual stored atom caches the power-search column as a Vector.
This is the execution interface: a function-valued direction would be eta
expanded by the compiler and could rerun the search at each matrix entry. -/
def qMinimumDensityOracleDense (hD : 0 < D) (delta : ℚ)
    (A : Matrix (Fin D) (Fin D) QComplex) : DenseMatrix D QComplex :=
  let input := denseOfMatrix A
  let v := qDenseBestPowerColumn hD (qShiftMinus (denseToMatrix input))
    (qPowerIterationCount D (qShiftBound (denseToMatrix input)) delta)
  denseOfMatrix (qSafeNormalizedProjector (fun i => v.get i) (qFallbackDirection hD))

@[simp] theorem denseToMatrix_qMinimumDensityOracleDense
    (hD : 0 < D) (delta : ℚ) (A : Matrix (Fin D) (Fin D) QComplex) :
    denseToMatrix (qMinimumDensityOracleDense hD delta A) = qMinimumDensityOracle hD delta A := by
  simp only [qMinimumDensityOracleDense, denseToMatrix_ofMatrix, qDenseBestPowerColumn_get,
    qMinimumDensityOracle, qDenseMinimumDirection]

theorem qMinimumDensityOracle_feasible
    (hD : 0 < D) (delta : ℚ) (A : Matrix (Fin D) (Fin D) QComplex) :
    (castQMatrix (qMinimumDensityOracle hD delta A)).PosSemidef ∧
      (castQMatrix (qMinimumDensityOracle hD delta A)).trace = 1 :=
  qSafeNormalizedProjector_feasible _ _ (qFallbackDirection_ne_zero hD)

theorem qMinimumDensityOracle_eq
    (hD : 0 < D) (delta : ℚ) (A : Matrix (Fin D) (Fin D) QComplex)
    (hA : (castQMatrix A).IsHermitian) :
    qMinimumDensityOracle hD delta A = qNormalizedProjector (qMinimumDirection hD A delta) := by
  simp only [qMinimumDensityOracle, qDenseMinimumDirection_eq, qSafeNormalizedProjector,
    if_neg (qMinimumDirection_nonzero hD A hA delta)]

/-- There is no spectral or linear-optimization hypothesis in this result:
the output is computed by the certified rational power search. -/
theorem qMinimumDensityOracle_correct
    (hD : 0 < D) (delta : ℚ) (hdelta : 0 < delta)
    (A : Matrix (Fin D) (Fin D) QComplex) (hA : (castQMatrix A).IsHermitian)
    (rho : DensityOperator (Fin D)) :
    (castQMatrix (qMinimumDensityOracle hD delta A) * castQMatrix A).trace.re ≤
      (rho.matrix * castQMatrix A).trace.re + (delta : ℝ) := by
  rw [qMinimumDensityOracle_eq hD delta A hA, cast_qNormalizedProjector]
  exact qMinimumDirection_linear_minimizer hD A hA delta hdelta rho

end TomographyOracleCore.Revision.FinitePrecision
