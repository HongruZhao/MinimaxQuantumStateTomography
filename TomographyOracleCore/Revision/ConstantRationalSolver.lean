import TomographyOracleCore.Revision.ConstantFinitePrecision
import TomographyOracleCore.Revision.ConstantSolver
import TomographyOracleCore.Revision.MatrixSolverInexactConvergence

namespace TomographyOracleCore.Revision.MatrixSolver
open MatrixReduction AlgorithmResources FinitePrecision
open scoped InnerProductSpace BigOperators ComplexOrder
set_option maxHeartbeats 1000000
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

theorem rationalAverageOutput_fit_unit_radius (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
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
    (hvariance : (h : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ gamma / 2)
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
        (h : ℝ) ^ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 + 2 * (h : ℝ) * (deltaS : ℝ) +
        4 * epsilonP + epsilonP ^ 2 := by
    intro j hj
    exact rationalProjectedStep_potential hD U M hM Q (X j) hQ
      (rationalIterate_feasible hD M Q X0 h0 deltaS h deltaP s n j)
      deltaS h deltaP s n hdeltaS hh.le hradius hdeltaP epsilonP hepsilonP
      hdeltaBudget hinnerBudget hprecision (rationalDensity X0 h0) sigma
  have hmean := inexact_solver_gamma_budget_unit_radius potential gap (h : ℝ)
    ((D + 1 : ℕ) : ℝ) gamma (deltaS : ℝ) epsilonP J (Rat.cast_pos.mpr hh) hJ
    hzero (sq_nonneg _) hsteps houterBudget hvariance hspectral hprojection hepsilonP hepsilonP_le
  have havg := average_objective_gap_le (finiteUnitaryFullCalibratedLinearChannel U)
    (castQMatrix Q) states J hJ sigma
  rw [cast_rationalAverageOutput hD M Q X0 h0 deltaS h deltaP s n J hJ]
  have hfinal := havg.trans hmean
  linarith


/-- The rational starting state is exactly the maximally mixed state. -/
theorem cast_rationalInitialMatrix_eq_mixed (hD : 0 < D) :
    castQMatrix (rationalInitialMatrix D) = (maximallyMixedDensity D hD).matrix := by
  rw [rationalInitialMatrix, castQMatrix_rat_smul, castQMatrix_one]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  rfl

def rationalMixedOuterCount (D : ℕ) (gamma : ℚ) : ℕ :=
  Nat.ceil (4 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2)

theorem rationalMixedOuterCount_pos (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    0 < rationalMixedOuterCount D gamma := by
  apply Nat.ceil_pos.mpr
  positivity

theorem rationalMixedOuterCount_budget (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    4 * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ (rationalMixedOuterCount D gamma : ℝ) * (gamma : ℝ) ^ 2 := by
  have hc : 4 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2 ≤ (rationalMixedOuterCount D gamma : ℚ) :=
    Nat.le_ceil _
  have hb : 4 * ((D + 1 : ℕ) : ℚ) ^ 2 ≤ (rationalMixedOuterCount D gamma : ℚ) * gamma ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hgamma)).1 hc
  exact_mod_cast hb

theorem rationalMixedOuterCount_scaled_budget (D : ℕ) {gamma : ℚ} (hgamma : 0 < gamma) :
    2 ≤ (rationalStepSize D gamma : ℝ) * (rationalMixedOuterCount D gamma : ℝ) * (gamma : ℝ) := by
  have hg : 0 < (gamma : ℝ) := Rat.cast_pos.mpr hgamma
  have hG : 0 < ((D + 1 : ℕ) : ℝ) := by positivity
  have hh : 0 < (rationalStepSize D gamma : ℝ) := Rat.cast_pos.mpr (rationalStepSize_pos D hgamma)
  have hid : (rationalStepSize D gamma : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 2 = (gamma : ℝ) / 2 := by
    rw [cast_rationalStepSize]
    field_simp
  have hmul := mul_le_mul_of_nonneg_left (rationalMixedOuterCount_budget D hgamma) hh.le
  apply (mul_le_mul_iff_left₀ hg).mp
  nlinarith

/-- Halved outer iteration budget; all inner operations and precisions are unchanged. -/
def rationalMixedMatrixSolveDense (hD : 0 < D) (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) : DenseMatrix D QComplex :=
  rationalAverageOutputDense hD M Q (rationalInitialMatrix D)
    (rationalSpectralTolerance gamma) (rationalStepSize D gamma) (rationalInnerTolerance D gamma)
    (rationalProjectionPrecision D gamma) (rationalInnerCount D gamma) (rationalMixedOuterCount D gamma)

def rationalMixedMatrixSolve (hD : 0 < D) (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) : Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalMixedMatrixSolveDense hD M Q gamma)

theorem rationalMixedMatrixSolve_feasible (hD : 0 < D) (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) (hgamma : 0 < gamma) :
    QFeasible (rationalMixedMatrixSolve hD M Q gamma) :=
  rationalAverageOutput_feasible hD M Q _ (rationalInitialMatrix_feasible hD)
    _ _ _ _ _ _ (rationalMixedOuterCount_pos D hgamma)

/-- Actual executable rational output, with its exact fitting guarantee. -/
theorem rationalMixedMatrixSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (rationalMixedMatrixSolve hD M Q gamma))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + (gamma : ℝ) := by
  have hb := rationalSchedule_budget D hgamma hgamma_le
  exact rationalAverageOutput_fit_unit_radius hD U M hM Q _ hQ
    (rationalInitialMatrix_feasible hD) _ _ _ _ _ _
    (by exact div_pos hgamma (by norm_num)) (rationalStepSize_pos D hgamma)
    (rationalStepSize_radius_budget D hgamma hgamma_le)
    (rationalInnerTolerance_pos D hgamma) (rationalProjectionTolerance D gamma : ℝ)
    (gamma : ℝ) hb.2.2.1 (by rw [cast_rationalInnerTolerance])
    (rationalInnerCount_budget D hgamma) (rationalProjectionPrecision_budget D gamma)
    (rationalMixedOuterCount_pos D hgamma) (rationalMixedOuterCount_scaled_budget D hgamma) hb.2.1
    (by rw [cast_rationalSpectralTolerance])
    (by rw [cast_rationalProjectionTolerance]) hb.2.2.2.1 sigma
    (by rw [cast_rationalInitialMatrix_eq_mixed hD]; exact maximallyMixed_distance_sq_le_one hD sigma)

/-- The integer cost improves by a factor two, up to one unavoidable ceiling unit. -/
theorem twice_rationalMixedOuterCount_le_old_add_one (D : ℕ) (gamma : ℚ) :
    2 * rationalMixedOuterCount D gamma ≤ rationalOuterCount D gamma + 1 := by
  unfold rationalMixedOuterCount rationalOuterCount
  let x : ℚ := 4 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2
  have hid : 8 * ((D + 1 : ℕ) : ℚ) ^ 2 / gamma ^ 2 = 2 * x := by dsimp [x]; ring
  rw [hid]
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hc := Nat.ceil_lt_add_one hx
  have ho := Nat.le_ceil (2 * x)
  have hreal : (2 * Nat.ceil x : ℚ) < (Nat.ceil (2 * x) : ℚ) + 2 := by nlinarith
  have hnat : 2 * Nat.ceil x < Nat.ceil (2 * x) + 2 := by exact_mod_cast hreal
  change 2 * Nat.ceil x ≤ Nat.ceil (2 * x) + 1
  omega

end TomographyOracleCore.Revision.MatrixSolver
