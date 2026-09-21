import TomographyOracleCore.Revision.MWPLSRisk

/-! MW-PLS paper-facing endpoints: actual estimator, arbitrary-state oracle,
adaptive physical upper risk, and the unrestricted minimax sandwich. -/
namespace TomographyOracleCore.MWPLS
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open Revision.PhysicalMinimax Revision.ConstantCovariance
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000

def upperConstant : ℝ := algorithmUpperConstant_mw 2 sharpForwardCovarianceConstant

theorem upperConstant_pos : 0 < upperConstant :=
  algorithmUpperConstant_mw_pos 2 sharpForwardCovarianceConstant (by norm_num)

/-- A measurable physical MW-PLS estimator, independent of alpha, L and rank. -/
def periodicEstimator {n K : ℕ} (h : ChoKimBlockCondition n K) (T : ℕ) :
    Estimator (2^n) T :=
  algorithmPhysicalEstimator (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (minimizer (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd))

theorem algorithm_statewise_adaptive_oracle
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hsize : 2 * (((2^n : ℕ) : ℝ)) ≤ (T : ℝ))
    (solve : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → DensityOperator (Fin (2^n)))
    (gamma : ℝ) (hg : 0 ≤ gamma)
    (hgscale : gamma ≤ Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ)))
    (hcert : ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) (gamma^2))
    (rho : DensityOperator (Fin (2^n))) :
    OracleBound (periodicAlgorithmExpectedError h T solve rho) (orderedSpectralTail rho)
      (PaperTheorems.statewiseOracleConstant * Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ))) (2^n) := by
  have ho := periodicAlgorithmExpectedError_oracle_mw h T solve gamma hg hcert rho
    (sharpForwardCovarianceConstant * Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ)))
    (periodic_expected_forward_covariance_sharp h hn hT hsize rho)
  intro s hs hsD
  have hh := ho s hs hsD
  have hc := mul_le_mul_of_nonneg_left hgscale
    (show 0 ≤ 4/sharpPeriodicCurvature by exact div_nonneg (by norm_num) sharpPeriodicCurvature_pos.le)
  have hc2 := mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg s)
  dsimp [PaperTheorems.statewiseOracleConstant]
  simp only [div_eq_mul_inv] at hh hc2 ⊢
  nlinarith

/-- The exact MW-PLS minimizer has the statewise adaptive expected oracle.
Its objective optimality and the physical covariance bound are discharged. -/
theorem minimizer_statewise_adaptive_oracle
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hsize : 2 * (((2^n : ℕ) : ℝ)) ≤ (T : ℝ))
    (rho : DensityOperator (Fin (2^n))) :
    OracleBound
      (periodicAlgorithmExpectedError h T
        (minimizer (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)) rho)
      (orderedSpectralTail rho)
      (PaperTheorems.statewiseOracleConstant * Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ))) (2^n) := by
  apply algorithm_statewise_adaptive_oracle h hn hT hsize _ 0 (by norm_num) (Real.sqrt_nonneg _) _ rho
  intro Q
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    minimizer_certificate (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q

/-- Every certified quadratic solver has the all-sample class upper rate. -/
theorem algorithm_selectedPhysicalUpper
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (solve : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → DensityOperator (Fin (2^n)))
    (gamma : ℝ) (hg : 0 ≤ gamma)
    (hgscale : gamma ≤ Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ)))
    (hcert : ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) (gamma^2))
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2^n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ≤
    ENNReal.ofReal (upperConstant * spectralDecayMinimaxRate (2^n) (T : ℝ) L alpha) := by
  unfold classWorstCaseRisk
  apply iSup_le
  intro rho
  exact periodicAlgorithm_physicalRisk_rate_mw h hT solve gamma hg hgscale hcert
    2 sharpForwardCovarianceConstant (by norm_num) sharpForwardCovarianceConstant_pos
    (fun hsize truth => periodic_expected_forward_covariance_sharp h hn hT hsize truth)
    rho.1 alpha L halpha hL rho.2

/-- The paper's statistical tolerance min(1,d/T), expressed by its complete
first-order inequality. This does not certify a floating-point eigenpair. -/
theorem algorithm_statisticalTolerance_upper
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (solve : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → DensityOperator (Fin (2^n)))
    (hcert : ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q)
      (min 1 (((2^n : ℕ) : ℝ)/(T : ℝ))))
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2^n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ≤
    ENNReal.ofReal (upperConstant * spectralDecayMinimaxRate (2^n) (T : ℝ) L alpha) := by
  let eps := min 1 (((2^n : ℕ) : ℝ)/(T : ℝ))
  have heps : 0 ≤ eps := by dsimp [eps]; positivity
  apply algorithm_selectedPhysicalUpper h hn hT solve (Real.sqrt eps) (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (min_le_right _ _)) _ alpha L halpha hL
  intro Q
  rw [Real.sq_sqrt heps]
  exact hcert Q

/-- No solver, concentration, or spectral-oracle premise remains. -/
theorem minimizer_selectedPhysicalUpper
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    classWorstCaseRisk (2^n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (periodicEstimator h T) ≤
    ENNReal.ofReal (upperConstant * spectralDecayMinimaxRate (2^n) (T : ℝ) L alpha) := by
  apply algorithm_selectedPhysicalUpper h hn hT _ 0 (by norm_num) (Real.sqrt_nonneg _) _ alpha L halpha hL
  intro Q
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0)] using
    minimizer_certificate (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q

/-- MW-PLS is minimax against every permitted randomized nonadaptive
single-copy design. The estimator is the explicit compact MW minimizer above. -/
theorem minimizer_minimax
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    0 < explicitDecayLowerConstant alpha ∧
    ENNReal.ofReal (explicitDecayLowerConstant alpha *
      spectralDecayMinimaxRate (2^n) (T : ℝ) L alpha) ≤ PhysicalRisk.unrestrictedRisk (2^n) T alpha L ∧
    PhysicalRisk.unrestrictedRisk (2^n) T alpha L ≤ PhysicalRisk.fixedDesignRisk (2^n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T) ∧
    PhysicalRisk.fixedDesignRisk (2^n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T) ≤
      classWorstCaseRisk (2^n) T alpha L
        (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
        (periodicEstimator h T) ∧
    classWorstCaseRisk (2^n) T alpha L
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (periodicEstimator h T) ≤
      ENNReal.ofReal (upperConstant * spectralDecayMinimaxRate (2^n) (T : ℝ) L alpha) := by
  have hD : 514 ≤ 2^n := (by decide : 514 ≤ 65536).trans
    (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  exact ⟨explicitDecayLowerConstant_pos alpha,
    explicitSpectralDecayRateENNReal_le_unrestrictedRisk (2^n) T L alpha hD hT hL halpha,
    PhysicalRisk.unrestrictedRisk_le_fixedDesignRisk _, PhysicalRisk.fixedDesignRisk_le_estimator _ (periodicEstimator h T),
    minimizer_selectedPhysicalUpper h hn hT alpha L halpha hL⟩

end
end TomographyOracleCore.MWPLS
