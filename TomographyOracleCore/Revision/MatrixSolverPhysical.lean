import TomographyOracleCore.Revision.MatrixSolverConvergence
import TomographyOracleCore.Revision.PhysicalMinimaxEstimator

/-! The exact projected solver as a total physical estimator interface.
On every Hermitian input it is exactly the projected algorithm. The
non-Hermitian branch uses a compact minimizer solely to make the interface
total outside the physical experiment. -/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction
open scoped ComplexOrder

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- The paper's starting state `I/d`. -/
def maximallyMixedDensity (D : ℕ) (hD : 0 < D) : DensityOperator (Fin D) where
  matrix := (D : ℝ)⁻¹ • (1 : Matrix (Fin D) (Fin D) ℂ)
  posSemidef := Matrix.PosSemidef.one.smul (inv_nonneg.mpr (Nat.cast_nonneg D))
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_one]
    simp only [Fintype.card_fin]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change (((D : ℝ)⁻¹ : ℝ) : ℂ) * (D : ℂ) = 1
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀]
    exact_mod_cast (Nat.ne_of_gt hD)

def guardedProjectedSolve (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) := by
  classical
  exact if hQ : Q.IsHermitian then
    exactProjectedSolve hD U Q hQ (maximallyMixedDensity D hD) gamma hgamma
  else PhysicalMinimax.forwardMinimizer hD U Q

theorem guardedProjectedSolve_eq_of_hermitian (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian) :
    guardedProjectedSolve hD U gamma hgamma Q =
      exactProjectedSolve hD U Q hQ (maximallyMixedDensity D hD) gamma hgamma := by
  simp [guardedProjectedSolve, hQ]

/-- The total interface meets the fitting premise for every matrix, and
uses the actual projected algorithm on all physical inputs. -/
theorem guardedProjectedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (guardedProjectedSolve hD U gamma hgamma Q).matrix) ≤
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  classical
  unfold guardedProjectedSolve
  split_ifs with hQ
  · exact exactProjectedSolve_fit hD U Q hQ _ gamma hgamma sigma
  · have hm := PhysicalMinimax.forwardMinimizer_le hD U Q sigma
    exact hm.trans (le_add_of_nonneg_right hgamma.le)

end

end TomographyOracleCore.Revision.MatrixSolver
