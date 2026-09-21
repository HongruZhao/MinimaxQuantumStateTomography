import TomographyOracleCore.Revision.ConstantRisk
import TomographyOracleCore.Revision.ConstantCovariance
import TomographyOracleCore.Revision.ConstantLower
import TomographyOracleCore.Revision.ConstantSolver
import TomographyOracleCore.Revision.ConstantRationalPhysical
import TomographyOracleCore.Revision.PhysicalMinimaxProjectedClosure
import TomographyOracleCore.Revision.MatrixSolverInexactRisk

namespace TomographyOracleCore.Revision.ConstantEndpoints
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk PhysicalMinimax
open ConstantCovariance MatrixSolver
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section

/-- Explicit universal upper coefficient, with the covariance theorem discharged. -/
def certifiedUpperConstant : ℝ :=
  algorithmUpperConstant_sharp 2 sharpForwardCovarianceConstant

theorem certifiedUpperConstant_pos : 0 < certifiedUpperConstant :=
  algorithmUpperConstant_sharp_pos 2 sharpForwardCovarianceConstant (by norm_num)

/-- The physical risk guarantee applies to the supplied solver itself. -/
theorem algorithm_selectedPhysicalUpper_sharp
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ Q rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  unfold classWorstCaseRisk
  apply iSup_le
  intro rho
  exact periodicAlgorithm_physicalRisk_rate_sharp h hT solve gamma hgamma hgammaScale hfit
    2 sharpForwardCovarianceConstant (by norm_num) sharpForwardCovarianceConstant_pos
    (fun hsize truth => periodic_expected_forward_covariance_sharp h hn hT hsize truth)
    rho.1 alpha L halpha hL rho.2

/-- The compact exact fit has the improved physical risk bound without any premise. -/
theorem exactFit_selectedPhysicalUpper_sharp
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (physicalEstimator (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  exact algorithm_selectedPhysicalUpper_sharp h hn hT
    (forwardMinimizer (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd))
    0 (by norm_num) (Real.sqrt_nonneg _)
    (by
      intro Q rho
      simpa only [add_zero] using forwardMinimizer_le (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho) alpha L halpha hL

/-- The existing rational implementation inherits the improved statistical constants. -/
theorem rational_selectedPhysicalUpper_sharp
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (rationalPhysicalEstimator h hT) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  exact algorithm_selectedPhysicalUpper_sharp h hn hT (guardedRationalPeriodicSolve n K T h.block_dvd hT)
    (Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) (Real.sqrt_nonneg _) le_rfl
    (fun Q rho => guardedRationalPeriodicSolve_fit n K T h.block_dvd h.block_pos hT Q rho)
    alpha L halpha hL

/-- The projected estimator with the reduced iteration count. -/
def improvedProjectedPhysicalEstimator {n K T : ℕ}
    (h : ChoKimBlockCondition n K) (hT : 0 < T) : Estimator (2 ^ n) T :=
  algorithmPhysicalEstimator (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (guardedMixedProjectedSolve (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      (algorithmTolerance n T) (algorithmTolerance_pos n T hT))

/-- The faster projected estimator satisfies the improved physical bound. -/
theorem projected_selectedPhysicalUpper_sharp
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (improvedProjectedPhysicalEstimator h hT) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  exact algorithm_selectedPhysicalUpper_sharp h hn hT
    (guardedMixedProjectedSolve (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      (algorithmTolerance n T) (algorithmTolerance_pos n T hT))
    (algorithmTolerance n T) (algorithmTolerance_pos n T hT).le (min_le_right _ _)
    (fun Q rho => guardedMixedProjectedSolve_fit (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) _ (algorithmTolerance_pos n T hT) Q rho)
    alpha L halpha hL

/-- The actual rational estimator with the reduced iteration schedule. -/
def improvedRationalPhysicalEstimator {n K T : ℕ}
    (h : ChoKimBlockCondition n K) (hT : 0 < T) : Estimator (2 ^ n) T :=
  algorithmPhysicalEstimator (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (guardedRationalMixedPeriodicSolve n K T h.block_dvd hT)

theorem improvedRational_selectedPhysicalUpper_sharp
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2 ^ n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (improvedRationalPhysicalEstimator h hT) ≤
      ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  exact algorithm_selectedPhysicalUpper_sharp h hn hT
    (guardedRationalMixedPeriodicSolve n K T h.block_dvd hT)
    (Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) (Real.sqrt_nonneg _) le_rfl
    (fun Q rho => guardedRationalMixedPeriodicSolve_fit n K T h.block_dvd h.block_pos hT Q rho)
    alpha L halpha hL

/-- Final minimax sandwich with both strengthened constants, for the unchanged
nonadaptive single-copy comparison class. -/
theorem periodic_physicalMinimax_sharp
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T) :
    PhysicalMinimaxSandwich (2 ^ n) T
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      sharpDecayLowerConstant (fun _ => certifiedUpperConstant) := by
  apply physicalMinimaxSandwich_of_lower_and_simultaneousUpper
  · intro alpha L halpha hL
    apply sharpSpectralDecayRateENNReal_le_unrestrictedRisk (2 ^ n) T L alpha
      (le_trans (by norm_num : 514 ≤ 65536) (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn))
      hT hL halpha
  · exact ⟨improvedRationalPhysicalEstimator h hT, improvedRational_selectedPhysicalUpper_sharp h hn hT⟩

end
end TomographyOracleCore.Revision.ConstantEndpoints
