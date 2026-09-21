import TomographyOracleCore.PaperMatch.ExactCorollaryFourMW

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk MWPLS RankMinimax
open Revision.PhysicalMinimax Revision.ConstantEndpoints Revision.ConstantCovariance
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000

/-- A universal coefficient for the paragraph following Theorem 3. -/
def mwRecordSpectralConstant : ℝ := max 4 (10 * max 1 (Upper.mwExpectedOracleConstant / 4))

theorem mwRecordSpectralConstant_pos : 0 < mwRecordSpectralConstant :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _)

/-- Every feasible MW fit of the entire record has the spectral upper bound;
the fit need not be a function of the empirical average alone. -/
theorem mw_record_spectral_expected_upper
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (rho : DensityOperator (Fin (2^n))) (alpha L : ℝ)
    (halpha : 1 < alpha) (hL : 1 ≤ L) (hrho : rho ∈ spectralDecayClass (2^n) alpha L)
    (hcert : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      HasFirstOrderCertificate (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) (estimate sample)
        (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ)))) :
    (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤
      mwRecordSpectralConstant * spectralDecayMinimaxRate (2^n) T L alpha := by
  let err := ∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
    ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho
  let q := Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ))
  let B := Upper.mwExpectedOracleConstant / 4
  have hB : 0 < B := by
    dsimp [B, Upper.mwExpectedOracleConstant]
    exact div_pos (add_pos (div_pos (mul_pos (by norm_num) sharpForwardCovarianceConstant_pos)
      sharpPeriodicCurvature_pos) (div_pos (by norm_num) (Real.sqrt_pos.mpr sharpPeriodicCurvature_pos)))
      (by norm_num)
  have hq : 0 < q := Real.sqrt_pos.mpr (div_pos (by positivity) (by exact_mod_cast hT))
  have hi := integrable_productBorn_real (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho
    (fun sample => hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho))
  change Integrable _ (periodicSampleLaw h T rho) at hi
  have hcap : err ≤ 2 := by
    have hb := integral_mono hi (integrable_const (2 : ℝ))
      (fun sample => density_hermitianTraceNorm_sub_le_two (estimate sample) rho)
    simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] using hb
  have hr0 : 0 ≤ spectralDecayMinimaxRate (2^n) T L alpha := by
    unfold spectralDecayMinimaxRate samplingDecayRate
    positivity
  by_cases hlarge : 2 * (((2^n : ℕ) : ℝ)) ≤ (T : ℝ)
  · have hc : ∀ᵐ sample ∂periodicSampleLaw h T rho,
        HasFirstOrderCertificate (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) (estimate sample) (((2^n : ℕ) : ℝ) / (T : ℝ)) := by
      filter_upwards [hcert] with sample hs
      exact fun state => (hs state).trans (min_le_right _ _)
    have ho : OracleBound err (orderedSpectralTail rho) (4 * (B * q)) (2^n) := by
      intro s hs hsD
      have hb := Upper.mw_expected_oracle h hn hT hlarge estimate rho hc s hs
      change err ≤ _ at hb
      dsimp [OracleBound, B, q] at ⊢
      convert hb using 1 <;> ring
    have hraw := decay_oracle_three_regime_ten err L (B*q) alpha (orderedSpectralTail rho)
      (2^n) (Nat.one_le_pow n 2 (by norm_num)) hL (mul_pos hB hq) halpha hcap ho
      (fun s hs hsD => hrho s hs hsD) (orderedSpectralTail_fin_dimension_eq_zero (2^n) rho)
    have hscale := decayUpperRate_const_mul_sqrt_le_spectralDecayMinimaxRate
      (2^n) (T : ℝ) L alpha B (Nat.one_le_pow n 2 (by norm_num))
      (by exact_mod_cast hT) hL halpha hB.le
    change err ≤ 10 * decayUpperRate (2^n) L (B*q) alpha at hraw
    calc
      err ≤ 10 * decayUpperRate (2^n) L (B*q) alpha := hraw
      _ ≤ 10 * (max 1 B * spectralDecayMinimaxRate (2^n) T L alpha) :=
        mul_le_mul_of_nonneg_left hscale (by norm_num)
      _ = (10 * max 1 B) * spectralDecayMinimaxRate (2^n) T L alpha := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hr0
  · have hr := one_div_le_spectralDecayMinimaxRate_of_samples_le (2^n) T alpha L 2
      (Nat.one_le_pow n 2 (by norm_num)) hT halpha hL (by norm_num) (le_of_not_ge hlarge)
    have hC : 4 ≤ mwRecordSpectralConstant := le_max_left _ _
    have hprod := mul_le_mul_of_nonneg_right hC hr0
    change err ≤ _
    nlinarith

/-- The complete MW-PLS minimax sandwich asserted after Theorem 3, for every
measurable feasible record rule at the paper's tolerance. -/
theorem theorem3_mw_record
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (hmeas : Measurable estimate)
    (hcert : ∀ rho : DensityOperator (Fin (2^n)),
      ∀ᵐ sample ∂periodicSampleLaw h T rho,
        HasFirstOrderCertificate (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) (estimate sample)
          (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ))))
    (alpha L : ℝ) (halpha : 1 < alpha) (hL : 1 ≤ L) :
    let design := constantMatrixPOVMPhysicalDesign
      (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T
    let estimator := mw_record_physical_estimator (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas
    ENNReal.ofReal (sharpDecayLowerConstant alpha * spectralDecayMinimaxRate (2^n) T L alpha) ≤
      minimaxRisk (T := T) (spectralDecayClass (2^n) alpha L) ∧
    minimaxRisk (T := T) (spectralDecayClass (2^n) alpha L) ≤
      fixedRisk (spectralDecayClass (2^n) alpha L) design.toOperator ∧
    fixedRisk (spectralDecayClass (2^n) alpha L) design.toOperator ≤
      classWorstCaseRisk (2^n) T alpha L design estimator ∧
    classWorstCaseRisk (2^n) T alpha L design estimator ≤
      ENNReal.ofReal (mwRecordSpectralConstant * spectralDecayMinimaxRate (2^n) T L alpha) := by
  dsimp only
  have hD : 514 ≤ 2^n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨theorem11_minimax L alpha hD hT hL halpha, minimaxRisk_le_fixedRisk _ _, ?_, ?_⟩
  · rw [fixedRisk_ofDominated]
    exact iInf_le _ _
  · unfold classWorstCaseRisk
    apply iSup_le
    intro rho
    exact (mw_record_physicalRisk_le_integral (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas rho.val).trans
      (ENNReal.ofReal_le_ofReal (mw_record_spectral_expected_upper h hn hT estimate rho.val
        alpha L halpha hL rho.property (hcert rho.val)))

end
end TomographyOracleCore.PaperMatch.ExactMain
