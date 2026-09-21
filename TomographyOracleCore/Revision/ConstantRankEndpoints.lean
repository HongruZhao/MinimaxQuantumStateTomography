import TomographyOracleCore.Revision.ConstantDimensionEndpoints
import TomographyOracleCore.Revision.ConstantRankTail
namespace TomographyOracleCore.Revision.ConstantEndpoints
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk PhysicalMinimax
open ConstantCovariance MatrixSolver
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000

/-- Rank classes avoid the factor-ten spectral-decay optimization. -/
def certifiedRankUpperConstant : ℝ :=
  max 4 ((8 * sharpForwardCovarianceConstant + 4) / sharpPeriodicCurvature)

/-- Statewise rank bound for any actual approximate forward solver, including
all positive sample counts. -/
theorem algorithm_rank_physicalRisk_sharp
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2 ^ n)
    (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ Q rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma)
    (rho : DensityOperator (Fin (2 ^ n))) (hrho : rho.matrix.rank ≤ r) :
    statewiseExpectedTraceRisk
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) rho ≤
      ENNReal.ofReal (min 2 (certifiedRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))) := by
  let q := Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have ha := sharpPeriodicCurvature_pos
  have hcoef := le_max_right (4 : ℝ) ((8 * sharpForwardCovarianceConstant + 4) / sharpPeriodicCurvature)
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  rw [ENNReal.ofReal_min]
  apply le_min
  · simpa only [ENNReal.ofReal_ofNat] using statewiseExpectedTraceRisk_le_two _ _ rho
  · by_cases hlarge : 2 * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ)
    · have hmean := periodic_expected_forward_covariance_sharp h hn hT hlarge rho
      have horacle := periodicAlgorithmExpectedError_oracle_sharp h T solve gamma hgamma hfit
        rho (sharpForwardCovarianceConstant * q) hmean
      have herr := horacle r hr hrD
      rw [orderedSpectralTail_eq_zero_of_rank_le rho r hrho, mul_zero, zero_add] at herr
      have htolerance := mul_le_mul_of_nonneg_left hgammaScale
        (show 0 ≤ 4 / sharpPeriodicCurvature by positivity)
      have hnoise : (8 / sharpPeriodicCurvature) * (sharpForwardCovarianceConstant * q) +
          (4 / sharpPeriodicCurvature) * gamma ≤ certifiedRankUpperConstant * q := by
        change (8 / sharpPeriodicCurvature) * (sharpForwardCovarianceConstant * q) +
          (4 / sharpPeriodicCurvature) * gamma ≤ _
        have hcoefq := mul_le_mul_of_nonneg_right hcoef hq
        calc
          _ ≤ (8 / sharpPeriodicCurvature) * (sharpForwardCovarianceConstant * q) +
              (4 / sharpPeriodicCurvature) * q := add_le_add le_rfl htolerance
          _ = ((8 * sharpForwardCovarianceConstant + 4) / sharpPeriodicCurvature) * q := by ring
          _ ≤ _ := hcoefq
      have hbound : periodicAlgorithmExpectedError h T solve rho ≤
          certifiedRankUpperConstant * (r : ℝ) * q := by
        have hm := mul_le_mul_of_nonneg_right hnoise (show 0 ≤ (r : ℝ) by positivity)
        nlinarith
      exact (algorithmPhysicalEstimator_risk_le_product_integral (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve rho).trans
          (ENNReal.ofReal_le_ofReal hbound)
    · have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
      have hratio : (1 / 2 : ℝ) ≤ (((2 ^ n : ℕ) : ℝ)) / (T : ℝ) := by
        apply (le_div_iff₀ hTreal).mpr
        linarith
      have hqhalf : (1 / 2 : ℝ) ≤ q := by
        apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
        nlinarith
      have hC : 4 ≤ certifiedRankUpperConstant := le_max_left _ _
      have hCr : 4 ≤ certifiedRankUpperConstant * (r : ℝ) := by nlinarith
      have htwo : (2 : ℝ) ≤ certifiedRankUpperConstant * (r : ℝ) * q := by nlinarith
      exact (statewiseExpectedTraceRisk_le_two _ _ rho).trans
        (by simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal htwo)

/-- Worst-case rank-class risk is a literal supremum over matrix rank bounds. -/
def rankClassWorstCaseRisk (D T r : ℕ) (design : Design D T) (estimator : Estimator D T) : ENNReal :=
  ⨆ rho : {rho : DensityOperator (Fin D) // rho.matrix.rank ≤ r},
    statewiseExpectedTraceRisk design estimator rho.val

/-- Complete rank-class endpoint for the new rational implementation. -/
theorem dimensionRational_rankClass_physicalUpper
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2 ^ n) :
    rankClassWorstCaseRisk (2 ^ n) T r
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (dimensionRationalPhysicalEstimator h hT) ≤
      ENNReal.ofReal (min 2 (certifiedRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))) := by
  unfold rankClassWorstCaseRisk
  apply iSup_le
  intro rho
  exact algorithm_rank_physicalRisk_sharp h hn hT hr hrD
    (guardedDimensionRationalPeriodicSolve n K T h.block_dvd hT)
    (Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) (Real.sqrt_nonneg _) le_rfl
    (fun Q sigma => guardedDimensionRationalPeriodicSolve_fit n K T h.block_dvd h.block_pos hT
      (periodic_hasDimensionGradientBound h hn) Q sigma) rho.val rho.property

end
end TomographyOracleCore.Revision.ConstantEndpoints
