import TomographyOracleCore.Revision.MatrixSolverInexactGradient
import TomographyOracleCore.Revision.FinitePrecisionRoundedProjection
import TomographyOracleCore.Revision.FinitePrecisionPotential

/-! The actual rational outer step and its proved accumulated-error term.
Both the signed spectral direction and the feasible approximate projection
are executable routines. The only accuracy premises below are explicit
inequalities for their chosen precision and iteration budgets.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision
open scoped InnerProductSpace BigOperators ComplexOrder

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def rationalProjectedStepDense (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n : ℕ) : DenseMatrix D QComplex :=
  let input := denseOfMatrix X
  let target := denseOfMatrix (rationalForwardTarget hD M Q (denseToMatrix input) deltaS h)
  qRoundedProjectionDense hD deltaP s (denseToMatrix input) (denseToMatrix target) (n + 1)

def rationalProjectedStep (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n : ℕ) : Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalProjectedStepDense hD M Q X deltaS h deltaP s n)

@[simp] theorem rationalProjectedStep_eq (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n : ℕ) :
    rationalProjectedStep hD M Q X deltaS h deltaP s n =
      qRoundedProjection hD deltaP s X (rationalForwardTarget hD M Q X deltaS h) (n + 1) := by
  simp only [rationalProjectedStep, rationalProjectedStepDense, denseToMatrix_ofMatrix,
    qRoundedProjection]

theorem rationalProjectedStep_feasible (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X : Matrix (Fin D) (Fin D) QComplex) (hX : QFeasible X)
    (deltaS h deltaP : ℚ) (s n : ℕ) :
    QFeasible (rationalProjectedStep hD M Q X deltaS h deltaP s n) := by
  rw [rationalProjectedStep_eq]
  exact qRoundedProjection_feasible hD deltaP s X _ hX (n + 1)

theorem rationalProjectedStep_projection_error (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X)
    (deltaS h deltaP : ℚ) (s n : ℕ)
    (hh : 0 ≤ h) (hstep : (h : ℝ) * ((D + 1 : ℕ) : ℝ) ≤ 1)
    (hdeltaP : 0 < deltaP) (epsilonP : ℝ) (hepsilonP : 0 ≤ epsilonP)
    (hdeltaBudget : (deltaP : ℝ) ≤ epsilonP ^ 2 / 4)
    (hiterationBudget : 24 ≤ ((n : ℝ) + 3) * epsilonP ^ 2)
    (hprecision : 7 * (D + 1) * D ^ 2 * (n + 2) ^ 2 ≤ 2 ^ s)
    (rho0 : DensityOperator (Fin D)) :
    ‖encode (castQMatrix (rationalProjectedStep hD M Q X deltaS h deltaP s n)) -
      densityProjection rho0 (encode (castQMatrix X) -
        (h : ℝ) • encode (castQMatrix (rationalForwardGradient hD M Q X deltaS)))‖ ≤ epsilonP := by
  have ht := qRoundedProjection_error hD deltaP hdeltaP s X
    (rationalForwardTarget hD M Q X deltaS h) hX
    (rationalForwardTarget_isHermitian hD U M hM Q X hQ hX deltaS h)
    (rationalForwardTarget_norm_le_two hD U M hM Q X hQ hX deltaS h hh hstep)
    rho0 n epsilonP hepsilonP hdeltaBudget hiterationBudget hprecision
  simpa only [rationalProjectedStep_eq, cast_rationalForwardTarget, encode_sub, encode_smul] using ht

/-- The actual rational matrix iteration satisfies the perturbed potential
recurrence, with every spectral and projection obligation discharged. -/
theorem rationalProjectedStep_potential (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X)
    (deltaS h deltaP : ℚ) (s n : ℕ)
    (hdeltaS : 0 < deltaS) (hh : 0 ≤ h)
    (hstep : (h : ℝ) * ((D + 1 : ℕ) : ℝ) ≤ 1)
    (hdeltaP : 0 < deltaP) (epsilonP : ℝ) (hepsilonP : 0 ≤ epsilonP)
    (hdeltaBudget : (deltaP : ℝ) ≤ epsilonP ^ 2 / 4)
    (hiterationBudget : 24 ≤ ((n : ℝ) + 3) * epsilonP ^ 2)
    (hprecision : 7 * (D + 1) * D ^ 2 * (n + 2) ^ 2 ≤ 2 ^ s)
    (rho0 sigma : DensityOperator (Fin D)) :
    ‖encode (castQMatrix (rationalProjectedStep hD M Q X deltaS h deltaP s n)) -
        encode sigma.matrix‖ ^ 2 ≤
      ‖encode (castQMatrix X) - encode sigma.matrix‖ ^ 2 - 2 * (h : ℝ) *
        (matrixOperatorNorm (castQMatrix Q -
            finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X)) -
          matrixOperatorNorm (castQMatrix Q -
            finiteUnitaryFullCalibratedLinearChannel U sigma.matrix)) +
        (h : ℝ) ^ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 + 2 * (h : ℝ) * (deltaS : ℝ) +
        4 * epsilonP + epsilonP ^ 2 := by
  let x := encode (castQMatrix X)
  let z := encode sigma.matrix
  let g := encode (castQMatrix (rationalForwardGradient hD M Q X deltaS))
  let p := densityProjection rho0 (x - (h : ℝ) • g)
  have hsupport := rationalForwardGradient_supporting hD U M hM Q X hQ hX deltaS hdeltaS sigma
  have hgradient := rationalForwardGradient_norm_le hD U M hM Q X hQ hX deltaS
  have hbase := projected_subgradient_step rho0 x z g (encode_density_mem sigma)
    (h : ℝ) ((D + 1 : ℕ) : ℝ)
    (matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X)) -
      matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) -
      (deltaS : ℝ)) (Rat.cast_nonneg.mpr hh) (by positivity)
    (by dsimp only [x, z, g]; linarith) hgradient
  have hdiam2 := densitySet_diameter_sq p z
    (densityProjection_mem rho0 (x - (h : ℝ) • g)) (encode_density_mem sigma)
  have hdiam : ‖p - z‖ ≤ 2 := by nlinarith [norm_nonneg (p - z)]
  have herror := rationalProjectedStep_projection_error hD U M hM Q X hQ hX
    deltaS h deltaP s n hh hstep hdeltaP epsilonP hepsilonP hdeltaBudget
    hiterationBudget hprecision rho0
  have hperturb := nearby_projection_potential p
    (encode (castQMatrix (rationalProjectedStep hD M Q X deltaS h deltaP s n))) z
    (R := 2) (by norm_num) hepsilonP hdiam herror
  dsimp only [p, x, z, g] at hbase hperturb
  nlinarith

#print axioms rationalProjectedStep_potential

end TomographyOracleCore.Revision.MatrixSolver
