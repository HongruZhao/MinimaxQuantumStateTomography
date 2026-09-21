import TomographyOracleCore.Revision.MatrixSolverRationalOperator
import TomographyOracleCore.Revision.MatrixSolverSubgradient
import TomographyOracleCore.Revision.AlgorithmResourcesDenseSpectral

/-! Executable rational matrix subgradients for the actual forward objective.

The supplied rational channel evaluator has an explicit interpretation
identity. Concrete projector and Pauli evaluators instantiate it. Every spectral direction is computed
by the proved, materialized rational power algorithm; no spectral oracle or
subgradient hypothesis occurs in the correctness theorems.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision
open scoped BigOperators InnerProductSpace ComplexOrder

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def QFeasible (X : Matrix (Fin D) (Fin D) QComplex) : Prop :=
  (castQMatrix X).PosSemidef ∧ (castQMatrix X).trace = 1

noncomputable def rationalDensity (X : Matrix (Fin D) (Fin D) QComplex)
    (hX : QFeasible X) : DensityOperator (Fin D) :=
  ⟨castQMatrix X, hX.1, hX.2⟩

def qDenseSignedDirection (hD : 0 < D)
    (A : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    (Fin D → QComplex) × ℚ :=
  qDenseSignedSpectralDirection hD A delta

@[simp] theorem qDenseSignedDirection_eq (hD : 0 < D)
    (A : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    qDenseSignedDirection hD A delta = qSignedSpectralDirection hD A delta := by
  exact qDenseSignedSpectralDirection_eq hD A delta

def rationalResidual
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  materializeMatrix (Q - rationalCalibratedFromProjective M X)

def rationalDirection (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    (Fin D → QComplex) × ℚ :=
  qDenseSignedDirection hD (rationalResidual M Q X) delta

def rationalForwardGradient (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    Matrix (Fin D) (Fin D) QComplex :=
  let direction := rationalDirection hD M Q X delta
  materializeMatrix ((-((D + 1 : ℕ) : ℚ) * direction.2) •
    M (qNormalizedProjector direction.1))

def rationalForwardTarget (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) (delta h : ℚ) :
    Matrix (Fin D) (Fin D) QComplex :=
  materializeMatrix (X - h • rationalForwardGradient hD M Q X delta)

theorem cast_rationalResidual
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalResidual M Q X) = castQMatrix Q -
      finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X) := by
  simp only [rationalResidual, materializeMatrix_eq, castQMatrix_sub,
    cast_rationalCalibratedFromProjective U M hM]

theorem rationalResidual_isHermitian
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) :
    (castQMatrix (rationalResidual M Q X)).IsHermitian := by
  rw [cast_rationalResidual U M hM]
  exact residual_isHermitian U (castQMatrix Q) hQ (rationalDensity X hX)

theorem rationalDirection_nonzero (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) (delta : ℚ) :
    (rationalDirection hD M Q X delta).1 ≠ 0 := by
  rw [rationalDirection, qDenseSignedDirection_eq]
  exact qSignedSpectralDirection_nonzero hD _
    (rationalResidual_isHermitian U M hM Q X hQ hX) delta

theorem rationalDirection_sign (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    |((rationalDirection hD M Q X delta).2 : ℝ)| ≤ 1 := by
  have h := qSignedSpectralDirection_sign hD (rationalResidual M Q X) delta
  rw [← qDenseSignedDirection_eq] at h
  change |((rationalDirection hD M Q X delta).2 : ℝ)| ≤ 1
  exact le_of_eq (by exact_mod_cast h)

theorem rationalDirection_accuracy (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X)
    (delta : ℚ) (hdelta : 0 < delta) :
    matrixOperatorNorm (castQMatrix Q -
        finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X)) - (delta : ℝ) ≤
      signedRayleigh (castQMatrix Q -
        finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X))
        (FinitePrecision.castQVector (rationalDirection hD M Q X delta).1)
        ((rationalDirection hD M Q X delta).2 : ℝ) := by
  have ht := qSignedSpectralDirection_signedRayleigh hD (rationalResidual M Q X)
    (rationalResidual_isHermitian U M hM Q X hQ hX) delta hdelta
  rw [cast_rationalResidual U M hM] at ht
  simpa only [rationalDirection, qDenseSignedDirection_eq, FinitePrecision.castQVector,
    AlgorithmResources.castQVector, Function.comp_def] using ht

theorem encode_rationalForwardGradient (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex) (delta : ℚ) :
    encode (castQMatrix (rationalForwardGradient hD M Q X delta)) =
      forwardGradient U (FinitePrecision.castQVector (rationalDirection hD M Q X delta).1)
        ((rationalDirection hD M Q X delta).2 : ℝ) := by
  simp only [rationalForwardGradient, materializeMatrix_eq, castQMatrix_rat_smul,
    hM, cast_qNormalizedProjector,
    Rat.cast_mul, Rat.cast_neg, Rat.cast_natCast, encode_smul, forwardGradient]

theorem rationalForwardGradient_norm_le (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) (delta : ℚ) :
    ‖encode (castQMatrix (rationalForwardGradient hD M Q X delta))‖ ≤
      ((D + 1 : ℕ) : ℝ) := by
  rw [encode_rationalForwardGradient hD U M hM]
  exact forwardGradient_norm_le U _
    (FinitePrecision.castQVector_ne_zero (rationalDirection_nonzero hD U M hM Q X hQ hX delta))
    (rationalDirection_sign hD M Q X delta)

theorem rationalForwardGradient_isHermitian (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) (delta : ℚ) :
    (castQMatrix (rationalForwardGradient hD M Q X delta)).IsHermitian := by
  rw [← decode_encode (castQMatrix (rationalForwardGradient hD M Q X delta)),
    encode_rationalForwardGradient hD U M hM]
  exact forwardGradient_isHermitian U _
    (FinitePrecision.castQVector_ne_zero (rationalDirection_nonzero hD U M hM Q X hQ hX delta)) _

theorem rationalForwardGradient_supporting (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X)
    (delta : ℚ) (hdelta : 0 < delta) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X)) -
        matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) ≤
      ⟪encode (castQMatrix (rationalForwardGradient hD M Q X delta)),
        encode (castQMatrix X) - encode sigma.matrix⟫_ℝ + (delta : ℝ) := by
  rw [encode_rationalForwardGradient hD U M hM]
  exact forwardGradient_subgradient U _ (rationalDensity X hX) sigma _
    (rationalDirection_sign hD M Q X delta)
    (rationalDirection_accuracy hD U M hM Q X hQ hX delta hdelta)

@[simp] theorem cast_rationalForwardTarget (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) (delta h : ℚ) :
    castQMatrix (rationalForwardTarget hD M Q X delta h) =
      castQMatrix X - (h : ℝ) • castQMatrix (rationalForwardGradient hD M Q X delta) := by
  simp only [rationalForwardTarget, materializeMatrix_eq, castQMatrix_sub, castQMatrix_rat_smul]

theorem rationalForwardTarget_isHermitian (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) (delta h : ℚ) :
    (castQMatrix (rationalForwardTarget hD M Q X delta h)).IsHermitian := by
  rw [cast_rationalForwardTarget]
  exact hX.1.isHermitian.sub
    ((rationalForwardGradient_isHermitian hD U M hM Q X hQ hX delta).smul
      (isSelfAdjoint_iff.mpr (by simp)))

theorem rationalForwardTarget_norm_le_two (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) (delta h : ℚ)
    (hh : 0 ≤ h) (hstep : (h : ℝ) * ((D + 1 : ℕ) : ℝ) ≤ 1) :
    ‖encode (castQMatrix (rationalForwardTarget hD M Q X delta h))‖ ≤ 2 := by
  have hx2 := density_frobenius_norm_sq_le_one (rationalDensity X hX)
  have hx : ‖encode (castQMatrix X)‖ ≤ 1 := by
    change ‖encode (castQMatrix X)‖ ^ 2 ≤ 1 at hx2
    nlinarith [norm_nonneg (encode (castQMatrix X))]
  have hg := rationalForwardGradient_norm_le hD U M hM Q X hQ hX delta
  have hh' : (0 : ℝ) ≤ h := Rat.cast_nonneg.mpr hh
  rw [cast_rationalForwardTarget, encode_sub, encode_smul]
  calc
    _ ≤ ‖encode (castQMatrix X)‖ +
        ‖(h : ℝ) • encode (castQMatrix (rationalForwardGradient hD M Q X delta))‖ := norm_sub_le _ _
    _ = ‖encode (castQMatrix X)‖ +
        (h : ℝ) * ‖encode (castQMatrix (rationalForwardGradient hD M Q X delta))‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh']
    _ ≤ 1 + (h : ℝ) * ((D + 1 : ℕ) : ℝ) := by gcongr
    _ ≤ 2 := by linarith

#print axioms rationalForwardGradient_supporting
#print axioms rationalForwardTarget_norm_le_two

end TomographyOracleCore.Revision.MatrixSolver
