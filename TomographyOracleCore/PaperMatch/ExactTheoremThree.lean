import TomographyOracleCore.PaperMatch.LowerMoments.OperatorMinimax
import TomographyOracleCore.PaperMatch.Model.GeneralRiskBridge
import TomographyOracleCore.Revision.ConstantDimensionEndpoints

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open Revision.ConstantEndpoints Revision.MatrixSolver Revision.FinitePrecision
open Revision.PhysicalMinimax Revision.AlgorithmResources
open scoped ENNReal
noncomputable section

/-- The selected OMD solver meets the paper's capped tolerance for every
record matrix and every comparison density, including T<d. -/
theorem theorem3_solver_fit {n K T : ℕ} (h : ChoKimBlockCondition n K)
    (hn : 0 < n) (hT : 0 < T) :
    let gamma : ℝ := statisticalRationalTolerance (2^n) T
    0 < gamma ∧ gamma ≤ min 1 (Real.sqrt (((2^n : ℕ) : ℝ) / T)) ∧
      ∀ (Q : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (sigma : DensityOperator (Fin (2^n))),
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q
        (guardedDimensionRationalPeriodicSolve n K T h.block_dvd hT Q) ≤
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q sigma + gamma := by
  dsimp only
  refine ⟨Rat.cast_pos.mpr (statisticalRationalTolerance_pos _ _),
    le_min (by exact_mod_cast statisticalRationalTolerance_le_one (2^n) T)
      (statisticalRationalTolerance_le_statistical (by positivity) hT), ?_⟩
  intro Q sigma
  exact guardedDimensionRationalSolve_fit (by positivity) _
    (periodic_hasDimensionGradientBound h hn) _
    (cast_rationalProjectiveFromCalibrated _ _ (qPeriodicCalibratedChannel_correct n K h.block_dvd h.block_pos))
    _ (statisticalRationalTolerance_pos _ _) (statisticalRationalTolerance_le_one _ _) Q sigma

/-- Theorem 3: one actual OMD estimator is fixed before alpha and L.
The minimax domain consists of arbitrary operator-valued POVMs on arbitrary
standard Borel seed and outcome spaces. -/
theorem theorem3 {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T) :
    let D := 2 ^ n
    let design := constantMatrixPOVMPhysicalDesign
      (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T
    ∃ estimator : Estimator D T,
      estimator = dimensionRationalPhysicalEstimator h hT ∧ ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      0 < sharpDecayLowerConstant alpha ∧ 0 < certifiedUpperConstant ∧
      ENNReal.ofReal (sharpDecayLowerConstant alpha * spectralDecayMinimaxRate D T L alpha) ≤
        minimaxRisk (T := T) (spectralDecayClass D alpha L) ∧
      minimaxRisk (T := T) (spectralDecayClass D alpha L) ≤
        fixedRisk (spectralDecayClass D alpha L) design.toOperator ∧
      fixedRisk (spectralDecayClass D alpha L) design.toOperator ≤
        classWorstCaseRisk D T alpha L design estimator ∧
      classWorstCaseRisk D T alpha L design estimator ≤
        ENNReal.ofReal (certifiedUpperConstant * spectralDecayMinimaxRate D T L alpha) := by
  dsimp only
  refine ⟨dimensionRationalPhysicalEstimator h hT, rfl, ?_⟩
  intro alpha L halpha hL
  have hD : 514 ≤ 2 ^ n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨sharpDecayLowerConstant_pos alpha, certifiedUpperConstant_pos,
    theorem11_minimax L alpha hD hT hL halpha, minimaxRisk_le_fixedRisk _ _, ?_,
    dimensionRational_selectedPhysicalUpper h hn hT alpha L halpha hL⟩
  rw [fixedRisk_ofDominated]
  exact iInf_le _ _

end
end TomographyOracleCore.PaperMatch.ExactMain
