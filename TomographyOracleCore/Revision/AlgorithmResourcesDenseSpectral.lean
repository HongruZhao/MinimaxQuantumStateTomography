import TomographyOracleCore.Revision.AlgorithmResourcesDense
import TomographyOracleCore.Revision.AlgorithmResourcesPowerSigned

/-! Stored-matrix implementations inherit the full spectral correctness proof. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixReduction FinitePrecision
open scoped ComplexOrder

variable {d : ℕ}

def qDenseMinimumDirection (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) : Fin d → QComplex :=
  qDenseBestPowerVector hD (qShiftMinus A) (qPowerIterationCount d (qShiftBound A) delta)

@[simp] theorem qDenseMinimumDirection_eq (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    qDenseMinimumDirection hD A delta = qMinimumDirection hD A delta :=
  qDenseBestPowerVector_eq hD _ _

def qDenseSignedSpectralDirection (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    (Fin d → QComplex) × ℚ :=
  let input := materializeMatrix A
  let vp := qDenseMinimumDirection hD (-input) delta
  let vm := qDenseMinimumDirection hD input delta
  if -qRayleigh input vm ≤ qRayleigh input vp then (vp, 1) else (vm, -1)

@[simp] theorem qDenseSignedSpectralDirection_eq (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    qDenseSignedSpectralDirection hD A delta = qSignedSpectralDirection hD A delta := by
  simp only [qDenseSignedSpectralDirection, materializeMatrix_eq,
    qDenseMinimumDirection_eq, qSignedSpectralDirection]

noncomputable section

theorem qDenseMinimumDirection_nonzero
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) :
    qDenseMinimumDirection hD A delta ≠ 0 := by
  rw [qDenseMinimumDirection_eq]
  exact qMinimumDirection_nonzero hD A hA delta

theorem qDenseMinimumDirection_linear_minimizer
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta)
    (rho : DensityOperator (Fin d)) :
    (normalizedProjector
        (WithLp.toLp 2 (castQVector (qDenseMinimumDirection hD A delta))) * castQMatrix A).trace.re ≤
      (rho.matrix * castQMatrix A).trace.re + (delta : ℝ) := by
  rw [qDenseMinimumDirection_eq]
  exact qMinimumDirection_linear_minimizer hD A hA delta hdelta rho

theorem qDenseSignedSpectralDirection_sign (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    |(qDenseSignedSpectralDirection hD A delta).2| = 1 := by
  rw [qDenseSignedSpectralDirection_eq]
  exact qSignedSpectralDirection_sign hD A delta

theorem qDenseSignedSpectralDirection_nonzero
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) :
    (qDenseSignedSpectralDirection hD A delta).1 ≠ 0 := by
  rw [qDenseSignedSpectralDirection_eq]
  exact qSignedSpectralDirection_nonzero hD A hA delta

theorem qDenseSignedSpectralDirection_signedRayleigh
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta) :
    matrixOperatorNorm (castQMatrix A) - (delta : ℝ) ≤
      signedRayleigh (castQMatrix A)
        (WithLp.toLp 2 (castQVector (qDenseSignedSpectralDirection hD A delta).1))
        ((qDenseSignedSpectralDirection hD A delta).2 : ℝ) := by
  rw [qDenseSignedSpectralDirection_eq]
  exact qSignedSpectralDirection_signedRayleigh hD A hA delta hdelta

#print axioms qDenseSignedSpectralDirection_signedRayleigh

end
end TomographyOracleCore.Revision.AlgorithmResources
