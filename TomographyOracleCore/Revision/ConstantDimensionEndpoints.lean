import TomographyOracleCore.Revision.ConstantEndpoints
import TomographyOracleCore.Revision.ConstantDimensionPhysical
namespace TomographyOracleCore.Revision.ConstantEndpoints
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk PhysicalMinimax
open ConstantCovariance MatrixSolver
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section

/-- The projected estimator with the reduced iteration count. -/
def dimensionProjectedPhysicalEstimator {n K T : ℕ}
    (h : ChoKimBlockCondition n K) (hT : 0 < T) : Estimator (2 ^ n) T :=
  algorithmPhysicalEstimator (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (guardedDimensionProjectedSolve (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      (algorithmTolerance n T) (algorithmTolerance_pos n T hT))

/-- The faster projected estimator satisfies the improved physical bound. -/
theorem dimensionProjected_selectedPhysicalUpper
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (dimensionProjectedPhysicalEstimator h hT) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  exact algorithm_selectedPhysicalUpper_sharp h hn hT
    (guardedDimensionProjectedSolve (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      (algorithmTolerance n T) (algorithmTolerance_pos n T hT))
    (algorithmTolerance n T) (algorithmTolerance_pos n T hT).le (min_le_right _ _)
    (fun Q rho => guardedDimensionProjectedSolve_fit (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) (periodic_hasDimensionGradientBound h hn) _ (algorithmTolerance_pos n T hT) Q rho)
    alpha L halpha hL

/-- The actual rational estimator with the reduced iteration schedule. -/
def dimensionRationalPhysicalEstimator {n K T : ℕ}
    (h : ChoKimBlockCondition n K) (hT : 0 < T) : Estimator (2 ^ n) T :=
  algorithmPhysicalEstimator (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (guardedDimensionRationalPeriodicSolve n K T h.block_dvd hT)

theorem dimensionRational_selectedPhysicalUpper
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (dimensionRationalPhysicalEstimator h hT) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  exact algorithm_selectedPhysicalUpper_sharp h hn hT
    (guardedDimensionRationalPeriodicSolve n K T h.block_dvd hT)
    (Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) (Real.sqrt_nonneg _) le_rfl
    (fun Q rho => guardedDimensionRationalPeriodicSolve_fit n K T h.block_dvd h.block_pos hT
      (periodic_hasDimensionGradientBound h hn) Q rho)
    alpha L halpha hL

/-- Final minimax sandwich with both strengthened constants, for the unchanged
nonadaptive single-copy comparison class. -/
theorem periodic_physicalMinimax_dimension
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T) :
    PhysicalMinimaxSandwich (2 ^ n) T
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      sharpDecayLowerConstant (fun _ => certifiedUpperConstant) := by
  apply physicalMinimaxSandwich_of_lower_and_simultaneousUpper
  · intro alpha L halpha hL
    apply sharpSpectralDecayRateENNReal_le_unrestrictedRisk (2 ^ n) T L alpha
      (le_trans (by norm_num : 514 ≤ 65536) (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn))
      hT hL halpha
  · exact ⟨dimensionRationalPhysicalEstimator h hT, dimensionRational_selectedPhysicalUpper h hn hT⟩

end
end TomographyOracleCore.Revision.ConstantEndpoints
