import TomographyOracleCore.Revision.MatrixSolverInexactStep
import TomographyOracleCore.Revision.MatrixSolverInexactSchedule
import TomographyOracleCore.Revision.MatrixSolverAverage

/-! An executable rational matrix solver, including all spectral searches,
feasible rounded projections, accumulated errors, and final averaging.

The implementation materializes every iterate and accumulates the output
sum during one traversal. Its correctness theorem contains no spectral,
projection, optimization, or convergence premise. The rational channel evaluator is an explicit input; its interpretation
as the measurement channel is the sole model-encoding premise. Concrete
projector and Pauli implementations instantiate this reusable core.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision
open scoped InnerProductSpace BigOperators ComplexOrder

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def rationalIterateDense (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n : ℕ) : ℕ → DenseMatrix D QComplex
  | 0 => denseOfMatrix X0
  | j + 1 => rationalProjectedStepDense hD M Q
      (denseToMatrix (rationalIterateDense hD M Q X0 deltaS h deltaP s n j)) deltaS h deltaP s n

def rationalIterate (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n j : ℕ) : Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalIterateDense hD M Q X0 deltaS h deltaP s n j)

@[simp] theorem rationalIterate_zero (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n : ℕ) :
    rationalIterate hD M Q X0 deltaS h deltaP s n 0 = X0 := by
  simp only [rationalIterate, rationalIterateDense, denseToMatrix_ofMatrix]

@[simp] theorem rationalIterate_succ (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n j : ℕ) :
    rationalIterate hD M Q X0 deltaS h deltaP s n (j + 1) =
      rationalProjectedStep hD M Q (rationalIterate hD M Q X0 deltaS h deltaP s n j)
        deltaS h deltaP s n := rfl

theorem rationalIterate_feasible (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex) (h0 : QFeasible X0)
    (deltaS h deltaP : ℚ) (s n j : ℕ) :
    QFeasible (rationalIterate hD M Q X0 deltaS h deltaP s n j) := by
  induction j with
  | zero => simpa only [rationalIterate_zero] using h0
  | succ j ih => exact rationalProjectedStep_feasible hD M Q _ ih deltaS h deltaP s n

/-- A single traversal computes the next state and the sum of all previous
states. Thus forming the average does not rerun the iteration prefixes. -/
def rationalSolverLoopDense (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n : ℕ) :
    ℕ → DenseMatrix D QComplex × DenseMatrix D QComplex
  | 0 => (denseOfMatrix X0, denseOfMatrix 0)
  | j + 1 =>
      let previous := rationalSolverLoopDense hD M Q X0 deltaS h deltaP s n j
      (rationalProjectedStepDense hD M Q (denseToMatrix previous.1) deltaS h deltaP s n,
        denseOfMatrix (denseToMatrix previous.2 + denseToMatrix previous.1))

def rationalSolverLoop (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n J : ℕ) :
    Matrix (Fin D) (Fin D) QComplex × Matrix (Fin D) (Fin D) QComplex :=
  let result := rationalSolverLoopDense hD M Q X0 deltaS h deltaP s n J
  (denseToMatrix result.1, denseToMatrix result.2)

theorem rationalSolverLoop_spec (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n J : ℕ) :
    (rationalSolverLoop hD M Q X0 deltaS h deltaP s n J).1 =
        rationalIterate hD M Q X0 deltaS h deltaP s n J ∧
      (rationalSolverLoop hD M Q X0 deltaS h deltaP s n J).2 =
        ∑ j ∈ Finset.range J, rationalIterate hD M Q X0 deltaS h deltaP s n j := by
  induction J with
  | zero => simp only [rationalSolverLoop, rationalSolverLoopDense,
      rationalIterate_zero, denseToMatrix_ofMatrix,
      Finset.range_zero, Finset.sum_empty, and_self]
  | succ J ih =>
      dsimp only [rationalSolverLoop] at ih ⊢
      simp only [rationalSolverLoopDense, denseToMatrix_ofMatrix,
        ih.1, ih.2, rationalIterate_succ, rationalProjectedStep, Finset.sum_range_succ, and_self]

def rationalAverageOutputDense (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n J : ℕ) : DenseMatrix D QComplex :=
  let result := rationalSolverLoopDense hD M Q X0 deltaS h deltaP s n J
  denseOfMatrix ((J : ℚ)⁻¹ • denseToMatrix result.2)

def rationalAverageOutput (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex)
    (deltaS h deltaP : ℚ) (s n J : ℕ) : Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalAverageOutputDense hD M Q X0 deltaS h deltaP s n J)

theorem cast_rationalAverageOutput (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex) (h0 : QFeasible X0)
    (deltaS h deltaP : ℚ) (s n J : ℕ) (hJ : 0 < J) :
    castQMatrix (rationalAverageOutput hD M Q X0 deltaS h deltaP s n J) =
      (averageDensity
        (fun j => rationalDensity (rationalIterate hD M Q X0 deltaS h deltaP s n j)
          (rationalIterate_feasible hD M Q X0 h0 deltaS h deltaP s n j)) J hJ).matrix := by
  rw [rationalAverageOutput, rationalAverageOutputDense, denseToMatrix_ofMatrix,
    castQMatrix_rat_smul]
  change (((J : ℚ)⁻¹ : ℚ) : ℝ) •
    castQMatrix (rationalSolverLoop hD M Q X0 deltaS h deltaP s n J).2 = _
  rw [
    (rationalSolverLoop_spec hD M Q X0 deltaS h deltaP s n J).2, castQMatrix_sum,
    averageDensity_matrix]
  simp only [Rat.cast_inv, Rat.cast_natCast, rationalDensity]

theorem rationalAverageOutput_feasible (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q X0 : Matrix (Fin D) (Fin D) QComplex) (h0 : QFeasible X0)
    (deltaS h deltaP : ℚ) (s n J : ℕ) (hJ : 0 < J) :
    QFeasible (rationalAverageOutput hD M Q X0 deltaS h deltaP s n J) := by
  unfold QFeasible
  rw [cast_rationalAverageOutput hD M Q X0 h0 deltaS h deltaP s n J hJ]
  exact ⟨DensityOperator.posSemidef _, DensityOperator.trace_eq_one _⟩

theorem rationalAverageOutput_fit_with_budgets (hD : 0 < D)
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
    (hJ : 0 < J) (houterBudget : 4 ≤ (h : ℝ) * (J : ℝ) * gamma)
    (hvariance : (h : ℝ) * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ gamma / 2)
    (hspectral : (deltaS : ℝ) ≤ gamma / 4)
    (hprojection : epsilonP ≤ (h : ℝ) * gamma / 10) (hepsilonP_le : epsilonP ≤ 1)
    (sigma : DensityOperator (Fin D)) :
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
  have hzero : potential 0 ≤ 2 := by
    simpa only [potential, X, rationalIterate_zero, rationalDensity] using
      density_frobenius_diameter_sq (rationalDensity X0 h0) sigma
  have hsteps : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * (h : ℝ) * gap j +
        (h : ℝ) ^ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 + 2 * (h : ℝ) * (deltaS : ℝ) +
        4 * epsilonP + epsilonP ^ 2 := by
    intro j hj
    exact rationalProjectedStep_potential hD U M hM Q (X j) hQ
      (rationalIterate_feasible hD M Q X0 h0 deltaS h deltaP s n j)
      deltaS h deltaP s n hdeltaS hh.le hradius hdeltaP epsilonP hepsilonP
      hdeltaBudget hinnerBudget hprecision (rationalDensity X0 h0) sigma
  have hmean := inexact_solver_gamma_budget potential gap (h : ℝ)
    ((D + 1 : ℕ) : ℝ) gamma (deltaS : ℝ) epsilonP J (Rat.cast_pos.mpr hh) hJ
    hzero (sq_nonneg _) hsteps houterBudget hvariance hspectral hprojection hepsilonP hepsilonP_le
  have havg := average_objective_gap_le (finiteUnitaryFullCalibratedLinearChannel U)
    (castQMatrix Q) states J hJ sigma
  rw [cast_rationalAverageOutput hD M Q X0 h0 deltaS h deltaP s n J hJ]
  have hfinal := havg.trans hmean
  linarith

/-- The paper's initial density matrix, using only rational arithmetic. -/
def rationalInitialMatrix (D : ℕ) : Matrix (Fin D) (Fin D) QComplex :=
  (D : ℚ)⁻¹ • 1

theorem rationalInitialMatrix_feasible (hD : 0 < D) :
    QFeasible (rationalInitialMatrix D) := by
  unfold QFeasible
  rw [rationalInitialMatrix, castQMatrix_rat_smul, castQMatrix_one]
  simp only [Rat.cast_inv, Rat.cast_natCast]
  constructor
  · exact Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg D))
  · rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change (((D : ℝ)⁻¹ : ℝ) : ℂ) * (D : ℂ) = 1
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀]
    exact_mod_cast Nat.ne_of_gt hD

/-- Complete executable rational solver, with no runtime exact-real choices. -/
def rationalMatrixSolveDense (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) :
    DenseMatrix D QComplex :=
  rationalAverageOutputDense hD M Q (rationalInitialMatrix D)
    (rationalSpectralTolerance gamma) (rationalStepSize D gamma) (rationalInnerTolerance D gamma)
    (rationalProjectionPrecision D gamma) (rationalInnerCount D gamma) (rationalOuterCount D gamma)

def rationalMatrixSolve (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) :
    Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (rationalMatrixSolveDense hD M Q gamma)

theorem rationalMatrixSolve_feasible (hD : 0 < D)
    (M : RationalMatrixOperator D)
    (Q : Matrix (Fin D) (Fin D) QComplex) (gamma : ℚ) (hgamma : 0 < gamma) :
    QFeasible (rationalMatrixSolve hD M Q gamma) :=
  rationalAverageOutput_feasible hD M Q _ (rationalInitialMatrix_feasible hD)
    _ _ _ _ _ _ (rationalOuterCount_pos D hgamma)

/-- Unconditional computational correctness on correctly encoded inputs:
the returned rational matrix is within gamma of every density comparator
for the literal forward operator-norm objective. -/
theorem rationalMatrixSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (castQMatrix Q - finiteUnitaryFullCalibratedLinearChannel U
      (castQMatrix (rationalMatrixSolve hD M Q gamma))) ≤
        matrixOperatorNorm (castQMatrix Q -
          finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + (gamma : ℝ) := by
  have hb := rationalSchedule_budget D hgamma hgamma_le
  exact rationalAverageOutput_fit_with_budgets hD U M hM Q _ hQ
    (rationalInitialMatrix_feasible hD) _ _ _ _ _ _
    (by exact div_pos hgamma (by norm_num)) (rationalStepSize_pos D hgamma)
    (rationalStepSize_radius_budget D hgamma hgamma_le)
    (rationalInnerTolerance_pos D hgamma) (rationalProjectionTolerance D gamma : ℝ)
    (gamma : ℝ) hb.2.2.1 (by rw [cast_rationalInnerTolerance])
    (rationalInnerCount_budget D hgamma) (rationalProjectionPrecision_budget D gamma)
    (rationalOuterCount_pos D hgamma) hb.2.2.2.2 hb.2.1
    (by rw [cast_rationalSpectralTolerance])
    (by rw [cast_rationalProjectionTolerance]) hb.2.2.2.1 sigma

#print axioms rationalMatrixSolve_feasible
#print axioms rationalMatrixSolve_fit

end TomographyOracleCore.Revision.MatrixSolver
