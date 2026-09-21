import TomographyOracleCore.Revision.PhysicalMinimaxClosure
import TomographyOracleCore.Revision.PhysicalMinimaxHermitian
import TomographyOracleCore.Revision.MatrixSolverPhysical

/-!
# Actual projected-subgradient estimator: closed physical risk and minimax chain

The solver here is the proved matrix projected-subgradient algorithm, with
the paper's maximally mixed start and tolerance min(1,sqrt(D/T)). Its fitting
theorem is discharged internally. The physical covariance theorem and
final risk endpoints use only Lean's standard foundations.
This exact-arithmetic result does not assert finite-precision bit complexity.
-/

namespace TomographyOracleCore.Revision.PhysicalMinimax

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped Matrix.Norms.L2Operator ENNReal

noncomputable section

def algorithmTolerance (n T : ℕ) : ℝ :=
  min 1 (Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))

theorem algorithmTolerance_pos (n T : ℕ) (hT : 0 < T) :
    0 < algorithmTolerance n T := by
  apply lt_min zero_lt_one
  exact Real.sqrt_pos.mpr (div_pos (by positivity) (by exact_mod_cast hT))

def projectedPhysicalEstimator {n K T : ℕ} (h : ChoKimBlockCondition n K) (hT : 0 < T) :
    Estimator (2 ^ n) T :=
  algorithmPhysicalEstimator (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (MatrixSolver.guardedProjectedSolve (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      (algorithmTolerance n T) (algorithmTolerance_pos n T hT))

/-- The selected actual projected estimator has the full physical rate,
with no covariance or fitting theorem left as an explicit premise. The
covariance theorem is proved from standard foundations. -/
theorem candidate2_projected_selectedPhysicalUpper :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → ∀ hT : 0 < T,
        ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
          classWorstCaseRisk (2 ^ n) T alpha L
            (constantMatrixPOVMPhysicalDesign
              (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
            (projectedPhysicalEstimator h hT) ≤
          ENNReal.ofReal (algorithmUpperConstant c A *
            spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  obtain ⟨c, A, hc, hA, hupper⟩ := candidate2_algorithm_selectedPhysicalUpper
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT alpha L halpha hL
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let gamma := algorithmTolerance n T
  have hgamma := algorithmTolerance_pos n T hT
  exact hupper h hn hT
    (MatrixSolver.guardedProjectedSolve (by positivity) U gamma hgamma)
    gamma hgamma.le (min_le_right _ _)
    (fun Q rho => MatrixSolver.guardedProjectedSolve_fit (by positivity) U gamma hgamma Q rho)
    alpha L halpha hL

/-- The actual projected algorithm supplies the upper side of the physical
unrestricted/fixed-design minimax sandwich, with E.1 proved internally. -/
theorem candidate2_projected_physicalMinimax :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T →
        ExplicitPhysicalMinimaxTarget (2 ^ n) T
          (constantMatrixPOVMPhysicalDesign
            (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (fun _ => algorithmUpperConstant c A) := by
  obtain ⟨c, A, hc, hA, hupper⟩ := candidate2_projected_selectedPhysicalUpper
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT
  apply physicalMinimaxSandwich_of_lower_and_simultaneousUpper
  · intro alpha L halpha hL
    have hlarge := h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn
    exact explicitSpectralDecayRateENNReal_le_unrestrictedRisk
      (2 ^ n) T L alpha (by omega) hT hL halpha
  · exact ⟨projectedPhysicalEstimator h hT, hupper h hn hT⟩

#print axioms candidate2_projected_selectedPhysicalUpper
#print axioms candidate2_projected_physicalMinimax

end
end TomographyOracleCore.Revision.PhysicalMinimax
