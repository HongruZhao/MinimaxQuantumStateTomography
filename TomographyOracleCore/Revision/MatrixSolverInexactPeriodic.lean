import TomographyOracleCore.Revision.MatrixSolverInexactPhysical
import TomographyOracleCore.Revision.AlgorithmResourcesPeriodicChannel

/-! Complete rational solver for the literal periodic measurement channel.
The channel multipliers, signed spectral directions, feasible approximate
projections, and outer iteration are all computed. No channel, eigenvector,
projection, fitting, or convergence contract is assumed.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision

set_option maxHeartbeats 1000000

def rationalPeriodicSolveDense (n K : ℕ) (hdiv : K ∣ n)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (gamma : ℚ) :
    DenseMatrix (2 ^ n) QComplex :=
  rationalCalibratedSolveDense (by positivity) (qPeriodicCalibratedChannel n K hdiv) Q gamma

def rationalPeriodicSolve (n K : ℕ) (hdiv : K ∣ n)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (gamma : ℚ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex :=
  denseToMatrix (rationalPeriodicSolveDense n K hdiv Q gamma)

theorem rationalPeriodicSolve_feasible (n K : ℕ) (hdiv : K ∣ n)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (gamma : ℚ) (hgamma : 0 < gamma) :
    QFeasible (rationalPeriodicSolve n K hdiv Q gamma) :=
  rationalCalibratedSolve_feasible (by positivity) _ Q gamma hgamma

/-- Unconditional computational fitting for the actual periodic channel,
on Hermitian rational input and positive requested accuracy at most one. -/
theorem rationalPeriodicSolve_fit (n K : ℕ) (hdiv : K ∣ n) (hK : 0 < K)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin (2 ^ n))) :
    matrixOperatorNorm (castQMatrix Q -
      finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (castQMatrix (rationalPeriodicSolve n K hdiv Q gamma))) ≤
      matrixOperatorNorm (castQMatrix Q -
        finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
          sigma.matrix) + (gamma : ℝ) :=
  rationalCalibratedSolve_fit (by positivity) _ _
    (qPeriodicCalibratedChannel_correct n K hdiv hK) Q hQ gamma hgamma hgamma_le sigma

theorem rationalPeriodicSolve_statistical_fit (n K T : ℕ)
    (hdiv : K ∣ n) (hK : 0 < K) (hT : 0 < T)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (sigma : DensityOperator (Fin (2 ^ n))) :
    matrixOperatorNorm (castQMatrix Q -
      finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (castQMatrix (rationalPeriodicSolve n K hdiv Q (rationalSampleTolerance T)))) ≤
      matrixOperatorNorm (castQMatrix Q -
        finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
          sigma.matrix) + Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) :=
  rationalCalibratedSolve_statistical_fit (by positivity) hT _ _
    (qPeriodicCalibratedChannel_correct n K hdiv hK) Q hQ sigma

noncomputable def guardedRationalPeriodicSolve (n K T : ℕ) (hdiv : K ∣ n) (hT : 0 < T) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)) :=
  guardedRationalCalibratedSolve (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) (qPeriodicCalibratedChannel n K hdiv)
    (rationalSampleTolerance T) (rationalSampleTolerance_pos hT)

/-- Universal-input fitting interface for the finite-support physical risk
proof. The actual encoded branch is identified in the next theorem. -/
theorem guardedRationalPeriodicSolve_fit (n K T : ℕ)
    (hdiv : K ∣ n) (hK : 0 < K) (hT : 0 < T)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (sigma : DensityOperator (Fin (2 ^ n))) :
    matrixOperatorNorm (Q -
      finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (guardedRationalPeriodicSolve n K T hdiv hT Q).matrix) ≤
      matrixOperatorNorm (Q -
        finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
          sigma.matrix) + Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) :=
  guardedRationalCalibratedSolve_statistical_fit (by positivity) hT _ _
    (qPeriodicCalibratedChannel_correct n K hdiv hK) Q sigma

theorem guardedRationalPeriodicSolve_eq_encoded (n K T : ℕ)
    (hdiv : K ∣ n) (hT : 0 < T)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (hQ : (castQMatrix Q).IsHermitian) :
    (guardedRationalPeriodicSolve n K T hdiv hT (castQMatrix Q)).matrix =
      castQMatrix (rationalPeriodicSolve n K hdiv Q (rationalSampleTolerance T)) := by
  have ht := guardedRationalSolve_eq_encoded (by positivity : 0 < 2 ^ n)
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
    (rationalProjectiveFromCalibrated (qPeriodicCalibratedChannel n K hdiv))
    (rationalSampleTolerance T) (rationalSampleTolerance_pos hT) Q hQ
  exact congrArg DensityOperator.matrix ht

#print axioms rationalPeriodicSolve_fit
#print axioms rationalPeriodicSolve_statistical_fit
#print axioms guardedRationalPeriodicSolve_fit
#print axioms guardedRationalPeriodicSolve_eq_encoded

end TomographyOracleCore.Revision.MatrixSolver
