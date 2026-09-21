import TomographyOracleCore.Revision.ConstantDimensionSchedule
import TomographyOracleCore.Revision.ConstantRationalSolver
namespace TomographyOracleCore.Revision.MatrixSolver
open MatrixReduction AlgorithmResources FinitePrecision
open scoped InnerProductSpace BigOperators ComplexOrder
set_option maxHeartbeats 1000000
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

theorem rationalForwardGradient_norm_le_dimension (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (hgradient : HasDimensionGradientBound U)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (hX : QFeasible X) (delta : ℚ) :
    ‖encode (castQMatrix (rationalForwardGradient hD M Q X delta))‖ ≤
      Real.sqrt (periodicGradientSquareBudget D) := by
  rw [encode_rationalForwardGradient hD U M hM]
  exact hgradient _
    (FinitePrecision.castQVector_ne_zero (rationalDirection_nonzero hD U M hM Q X hQ hX delta)) _
    (rationalDirection_sign hD M Q X delta)

theorem rationalProjectedStep_potential_dimension (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (hgradient : HasDimensionGradientBound U)
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
        (h : ℝ) ^ 2 * periodicGradientSquareBudget D + 2 * (h : ℝ) * (deltaS : ℝ) +
        4 * epsilonP + epsilonP ^ 2 := by
  let x := encode (castQMatrix X)
  let z := encode sigma.matrix
  let g := encode (castQMatrix (rationalForwardGradient hD M Q X deltaS))
  let p := densityProjection rho0 (x - (h : ℝ) • g)
  have hsupport := rationalForwardGradient_supporting hD U M hM Q X hQ hX deltaS hdeltaS sigma
  have hgnorm := rationalForwardGradient_norm_le_dimension hD U hgradient M hM Q X hQ hX deltaS
  have hbase := projected_subgradient_step rho0 x z g (encode_density_mem sigma)
    (h : ℝ) (Real.sqrt (periodicGradientSquareBudget D))
    (matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U (castQMatrix X)) -
      matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) -
      (deltaS : ℝ)) (Rat.cast_nonneg.mpr hh) (by positivity)
    (by dsimp only [x, z, g]; linarith) hgnorm
  rw [Real.sq_sqrt (periodicGradientSquareBudget_pos D).le] at hbase
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

theorem rationalAverageOutput_fit_dimension (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (hgradient : HasDimensionGradientBound U)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (hQ : (castQMatrix Q).IsHermitian) (h0 : QFeasible X0)
    (deltaS h deltaP : ℚ) (s n J : ℕ)
    (hdeltaS : 0 < deltaS) (hh : 0 < h)
    (hradius : (h : ℝ) * ((D + 1 : ℕ) : ℝ) ≤ 1)
    (hdeltaP : 0 < deltaP) (epsilonP gamma : ℝ) (hepsilonP : 0 ≤ epsilonP)
    (hdeltaBudget : (deltaP : ℝ) ≤ epsilonP ^ 2 / 4)
    (hinnerBudget : 24 ≤ ((n : ℝ) + 3) * epsilonP ^ 2)
    (hprecision : 7 * (D + 1) * D ^ 2 * (n + 2) ^ 2 ≤ 2 ^ s)
    (hJ : 0 < J) (houterBudget : 2 ≤ (h : ℝ) * (J : ℝ) * gamma)
    (hvariance : (h : ℝ) * periodicGradientSquareBudget D ≤ gamma / 2)
    (hspectral : (deltaS : ℝ) ≤ gamma / 4)
    (hprojection : epsilonP ≤ (h : ℝ) * gamma / 10) (hepsilonP_le : epsilonP ≤ 1)
    (sigma : DensityOperator (Fin D))
    (hstart : ‖encode (castQMatrix X0) - encode sigma.matrix‖ ^ 2 ≤ 1) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (rationalAverageOutput hD M Q X0 deltaS h deltaP s n J))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  let X := rationalIterate hD M Q X0 deltaS h deltaP s n
  let states (j : ℕ) := rationalDensity (X j)
    (rationalIterate_feasible hD M Q X0 h0 deltaS h deltaP s n j)
  let potential (j : ℕ) := ‖encode (castQMatrix (X j)) - encode sigma.matrix‖ ^ 2
  let gap (j : ℕ) :=
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U (castQMatrix (X j))) -
      matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix)
  have hzero : potential 0 ≤ 1 := by
    simpa only [potential, X, rationalIterate_zero] using hstart
  have hsteps : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * (h : ℝ) * gap j +
        (h : ℝ) ^ 2 * periodicGradientSquareBudget D + 2 * (h : ℝ) * (deltaS : ℝ) +
        4 * epsilonP + epsilonP ^ 2 := by
    intro j hj
    exact rationalProjectedStep_potential_dimension hD U hgradient M hM Q (X j) hQ
      (rationalIterate_feasible hD M Q X0 h0 deltaS h deltaP s n j)
      deltaS h deltaP s n hdeltaS hh.le hradius hdeltaP epsilonP hepsilonP
      hdeltaBudget hinnerBudget hprecision (rationalDensity X0 h0) sigma
  have hmean := inexact_solver_gamma_budget_unit_radius potential gap (h : ℝ)
    (Real.sqrt (periodicGradientSquareBudget D)) gamma (deltaS : ℝ) epsilonP J (Rat.cast_pos.mpr hh) hJ
    hzero (sq_nonneg _)
    (by simpa only [Real.sq_sqrt (periodicGradientSquareBudget_pos D).le] using hsteps)
    houterBudget (by simpa only [Real.sq_sqrt (periodicGradientSquareBudget_pos D).le] using hvariance) hspectral hprojection hepsilonP hepsilonP_le
  have havg := average_objective_gap_le (finiteUnitaryFullCalibratedLinearChannel U)
    (castQMatrix Q) states J hJ sigma
  rw [cast_rationalAverageOutput hD M Q X0 h0 deltaS h deltaP s n J hJ]
  have hfinal := havg.trans hmean
  linarith


def dimensionRationalMatrixSolveDense (hD : 0 < D) (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) : DenseMatrix D QComplex :=
  rationalAverageOutputDense hD M Q (rationalInitialMatrix D)
    (rationalSpectralTolerance gamma) (dimensionRationalStepSize D gamma) (dimensionRationalInnerTolerance D gamma)
    (dimensionRationalProjectionPrecision D gamma) (dimensionRationalInnerCount D gamma) (dimensionRationalOuterCount D gamma)

def dimensionRationalMatrixSolve (hD : 0 < D) (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) : Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (dimensionRationalMatrixSolveDense hD M Q gamma)

theorem dimensionRationalMatrixSolve_feasible (hD : 0 < D) (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) (hgamma : 0 < gamma) :
    QFeasible (dimensionRationalMatrixSolve hD M Q gamma) :=
  rationalAverageOutput_feasible hD M Q _ (rationalInitialMatrix_feasible hD)
    _ _ _ _ _ _ (dimensionRationalOuterCount_pos D hgamma)

/-- Actual executable rational output, with its exact fitting guarantee. -/
theorem dimensionRationalMatrixSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (hgradient : HasDimensionGradientBound U)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (dimensionRationalMatrixSolve hD M Q gamma))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + (gamma : ℝ) := by
  have hb := dimensionRationalSchedule_budget D hgamma hgamma_le
  exact rationalAverageOutput_fit_dimension hD U hgradient M hM Q _ hQ
    (rationalInitialMatrix_feasible hD) _ _ _ _ _ _
    (by exact div_pos hgamma (by norm_num)) (dimensionRationalStepSize_pos D hgamma)
    (dimensionRationalStepSize_radius_budget D hgamma hgamma_le)
    (dimensionRationalInnerTolerance_pos D hgamma) (dimensionRationalProjectionTolerance D gamma : ℝ)
    (gamma : ℝ) hb.2.2.1 (by rw [cast_dimensionRationalInnerTolerance])
    (dimensionRationalInnerCount_budget D hgamma) (dimensionRationalProjectionPrecision_budget D gamma)
    (dimensionRationalOuterCount_pos D hgamma) hb.2.2.2.2 hb.2.1
    (by rw [cast_rationalSpectralTolerance])
    (by rw [cast_dimensionRationalProjectionTolerance]) hb.2.2.2.1 sigma
    (by rw [cast_rationalInitialMatrix_eq_mixed hD]; exact maximallyMixed_distance_sq_le_one hD sigma)


end TomographyOracleCore.Revision.MatrixSolver
