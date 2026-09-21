import TomographyOracleCore.PaperMatch.CorollaryFourUnconditional
import TomographyOracleCore.PaperMatch.Upper.ExpectedMW

/-! Corollary 4 for MW-PLS. The rank class and lower constant are identical
to the OMD endpoint. The upper bound uses the actual MW first-order gap,
the sharp expected oracle, and the loss cap for all positive sample counts.
The final minimizer theorem discharges the optimization certificate.
All sampling objects remain those of the existing concrete Clifford model. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk MWPLS
open Revision.PhysicalMinimax Revision.ConstantEndpoints Revision.ConstantCovariance
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The MW replacement for C_rank in Corollary 4. -/
def mwRankUpperConstant : ℝ := max 4 Upper.mwExpectedOracleConstant

theorem mwRankUpperConstant_pos : 0 < mwRankUpperConstant :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _)

theorem mwRankUpperConstant_paper_value :
    mwRankUpperConstant = max 4
      (4 * sharpForwardCovarianceConstant / sharpPeriodicCurvature +
        4 / Real.sqrt sharpPeriodicCurvature) := rfl

/-- A measurable fit of the full record gives an admissible physical estimator. -/
def mw_record_physical_estimator {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (estimate : (Fin T → Matrix (Fin D) (Fin D) ℂ) → DensityOperator (Fin D))
    (hmeas : Measurable estimate) : Estimator D T where
  kernel := Kernel.deterministic
    (estimate ∘ decodeAllMatrixPOVMExperiment (finiteUnitaryProjectivePOVM D hD U) T)
    (hmeas.comp (measurable_decodeAllMatrixPOVMExperiment _ T))
  markov := by infer_instance

/-- Risk transport for an arbitrary measurable record fit. -/
theorem mw_record_physicalRisk_le_integral
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (estimate : (Fin T → Matrix (Fin D) (Fin D) ℂ) → DensityOperator (Fin D))
    (hmeas : Measurable estimate) (rho : DensityOperator (Fin D)) :
    statewiseExpectedTraceRisk
      (constantMatrixPOVMPhysicalDesign (finiteUnitaryProjectivePOVM D hD U) T)
      (mw_record_physical_estimator hD U T estimate hmeas) rho ≤
    ENNReal.ofReal (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho)
      ∂Measure.pi (fun _ : Fin T => (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho)) := by
  let loss := fun sample => hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
    ((estimate sample).sub_isHermitian rho)
  let M := finiteUnitaryProjectivePOVM D hD U
  let design := constantMatrixPOVMPhysicalDesign M T
  let decode := decodeAllMatrixPOVMExperiment M T
  let fit := estimate ∘ decode
  let realLoss := loss ∘ decode
  have hdecode := measurePreserving_decodeAllMatrixPOVMExperiment M T rho
  have hi := integrable_productBorn_real hD U T rho (loss)
  have hiobs : Integrable realLoss (design.experimentKernel rho) :=
    hdecode.integrable_comp_of_integrable hi
  have hbind :
      (∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂(Kernel.deterministic fit
          ((hmeas).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) ∘ₖ
          design.experimentKernel) rho) ≤
      ∫⁻ observed, ∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂Kernel.deterministic fit
          ((hmeas).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) observed
        ∂design.experimentKernel rho := Measure.lintegral_bind_le _ _ _
  have hinner :
      (∫⁻ observed, ∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂Kernel.deterministic fit
          ((hmeas).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) observed
        ∂design.experimentKernel rho) =
      ∫⁻ observed, ENNReal.ofReal (realLoss observed)
        ∂design.experimentKernel rho := by
    apply lintegral_congr
    intro observed
    simp only [Kernel.deterministic_apply, lintegral_dirac]
    rfl
  have hofReal := ofReal_integral_eq_lintegral_ofReal hiobs
    (ae_of_all _ fun observed => hermitianTraceNorm_nonneg _ _)
  have hint : (∫ observed, realLoss observed ∂design.experimentKernel rho) =
      ∫ sample, loss sample
        ∂Measure.pi (fun _ : Fin T => M.bornMeasure rho) := by
    have himap : AEStronglyMeasurable (loss)
        (Measure.map decode (design.experimentKernel rho)) := by
      rw [hdecode.map_eq]
      exact hi.aestronglyMeasurable
    exact (integral_map hdecode.measurable.aemeasurable himap).symm.trans
      (congrArg (fun mu => ∫ sample, loss sample ∂mu)
        hdecode.map_eq)
  change (∫⁻ sigma, hermitianTraceLoss rho sigma
    ∂(Kernel.deterministic fit
      ((hmeas).comp
        (measurable_decodeAllMatrixPOVMExperiment M T)) ∘ₖ design.experimentKernel) rho) ≤ _
  exact hbind.trans (hinner.trans (hofReal.symm.trans (congrArg ENNReal.ofReal hint))).le


/-- The all-sample expected rank bound for any feasible fit of the whole
record satisfying the paper's statistical gap tolerance almost surely. -/
theorem mw_record_rank_expected_upper
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r)
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (rho : DensityOperator (Fin (2^n))) (hrho : rho.matrix.rank ≤ r)
    (hcert : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      HasFirstOrderCertificate (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) (estimate sample)
        (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ)))) :
    (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤
      min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ))) := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let q := Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ))
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hi := integrable_productBorn_real (by positivity) U T rho
    (fun sample => hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho))
  change Integrable _ (periodicSampleLaw h T rho) at hi
  have hcap : (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤ 2 := by
    have hb := integral_mono hi (integrable_const (2 : ℝ))
      (fun sample => density_hermitianTraceNorm_sub_le_two (estimate sample) rho)
    simpa only [integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul] using hb
  refine le_min hcap ?_
  by_cases hlarge : 2 * (((2^n : ℕ) : ℝ)) ≤ (T : ℝ)
  · have hc : ∀ᵐ sample ∂periodicSampleLaw h T rho,
        HasFirstOrderCertificate U (empiricalForwardMatrix sample) (estimate sample)
          (((2^n : ℕ) : ℝ) / (T : ℝ)) := by
      filter_upwards [hcert] with sample hs
      exact fun state => (hs state).trans (min_le_right _ _)
    have hb := Upper.mw_expected_oracle h hn hT hlarge estimate rho hc r hr
    rw [orderedSpectralTail_eq_zero_of_rank_le rho r hrho, mul_zero, zero_add] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Nat.cast_nonneg r)) hq)
  · have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
    have hratio : (1 / 2 : ℝ) ≤ (((2^n : ℕ) : ℝ)) / (T : ℝ) := by
      apply (le_div_iff₀ hTreal).mpr
      linarith
    have hqhalf : (1 / 2 : ℝ) ≤ q := by
      apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
      nlinarith
    have hC : 4 ≤ mwRankUpperConstant := le_max_left _ _
    have hCr : 4 ≤ mwRankUpperConstant * (r : ℝ) := by nlinarith
    have htwo : (2 : ℝ) ≤ mwRankUpperConstant * (r : ℝ) * q := by nlinarith
    exact hcap.trans htwo

/-- Actual physical risk of any MW solver with the prescribed gap bound. -/
theorem mw_algorithm_rank_physicalUpper
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r)
    (solve : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → DensityOperator (Fin (2^n)))
    (hcert : ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q)
      (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ))))
    (rho : DensityOperator (Fin (2^n))) (hrho : rho.matrix.rank ≤ r) :
    statewiseExpectedTraceRisk
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) rho ≤
      ENNReal.ofReal (min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  have hD : 0 < 2^n := by positivity
  let estimate := algorithmSampleEstimator hD U T solve
  have hc : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      HasFirstOrderCertificate U (empiricalForwardMatrix sample) (estimate sample)
        (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ))) := by
    have hs := ae_mem_possibleSamples hD U T rho
    filter_upwards [hs] with sample hsample
    dsimp only [estimate]
    rw [algorithmSampleEstimator_eq hD U T solve sample hsample]
    exact hcert _
  have hb := mw_record_rank_expected_upper h hn hT hr estimate rho hrho hc
  change periodicAlgorithmExpectedError h T solve rho ≤ _ at hb
  exact (algorithmPhysicalEstimator_risk_le_product_integral hD U T solve rho).trans
    (ENNReal.ofReal_le_ofReal hb)

/-- Supremum over exactly the rank-at-most-r density matrices. -/
theorem mw_algorithm_rankClass_upper
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r)
    (solve : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → DensityOperator (Fin (2^n)))
    (hcert : ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q)
      (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ)))) :
    rankClassWorstCaseRisk (2^n) T r
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ≤
      ENNReal.ofReal (min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  unfold rankClassWorstCaseRisk
  apply iSup_le
  intro rho
  exact mw_algorithm_rank_physicalUpper h hn hT hr solve hcert rho.val rho.property

/-- The extended Corollary 4 for a certified approximate MW fit. The only
solver premise is the same statistical tolerance as equation (20). -/
theorem corollary4_mw_algorithm_sandwich
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2^n)
    (solve : Matrix (Fin (2^n)) (Fin (2^n)) ℂ → DensityOperator (Fin (2^n)))
    (hcert : ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q)
      (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ)))) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate (2^n) T r) ≤
        Model.minimaxRiskOn (T := T) (rankClass (2^n) r) ∧
    Model.minimaxRiskOn (T := T) (rankClass (2^n) r) ≤
        rankClassWorstCaseRisk (2^n) T r
          (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (algorithmPhysicalEstimator (by positivity)
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ∧
    rankClassWorstCaseRisk (2^n) T r
        (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
        (algorithmPhysicalEstimator (by positivity)
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ≤
      ENNReal.ofReal (min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  have hd : 514 ≤ 2^n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨rank_minimax_lower_all_ranks hd hT r hr hrD, ?_,
    mw_algorithm_rankClass_upper h hn hT hr solve hcert⟩
  exact (iInf_le _ _).trans (iInf_le _ _)

/-- Full Corollary 4 for any measurable feasible record fit with the
paper's almost-sure optimization certificate. -/
theorem corollary4_mw_record_sandwich
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2^n)
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (hmeas : Measurable estimate)
    (hcert : ∀ rho : DensityOperator (Fin (2^n)),
      ∀ᵐ sample ∂periodicSampleLaw h T rho,
        HasFirstOrderCertificate (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) (estimate sample)
          (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ)))) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate (2^n) T r) ≤
        Model.minimaxRiskOn (T := T) (rankClass (2^n) r) ∧
    Model.minimaxRiskOn (T := T) (rankClass (2^n) r) ≤
        rankClassWorstCaseRisk (2^n) T r
          (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (mw_record_physical_estimator (by positivity)
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas) ∧
    rankClassWorstCaseRisk (2^n) T r
        (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
        (mw_record_physical_estimator (by positivity)
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas) ≤
      ENNReal.ofReal (min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  have hd : 514 ≤ 2^n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨rank_minimax_lower_all_ranks hd hT r hr hrD, ?_, ?_⟩
  · exact (iInf_le _ _).trans (iInf_le _ _)
  · unfold rankClassWorstCaseRisk
    apply iSup_le
    intro rho
    exact (mw_record_physicalRisk_le_integral (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas rho.val).trans
      (ENNReal.ofReal_le_ofReal
        (mw_record_rank_expected_upper h hn hT hr estimate rho.val rho.property (hcert rho.val)))

/-- The exact MW minimizer satisfies the statistical certificate for every Q. -/
theorem mw_minimizer_statistical_certificate
    {n K T : ℕ} (h : ChoKimBlockCondition n K) :
    ∀ Q, HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q
      (minimizer (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q)
      (min 1 (((2^n : ℕ) : ℝ) / (T : ℝ))) := by
  intro Q rho
  exact (minimizer_certificate (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho).trans (by positivity)

/-- MW-PLS attains the rank-class minimax rate for every rank, with the same
lower constant as OMD and no solver or statistical-bound hypothesis. -/
theorem corollary4_mw_minimax_sandwich
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2^n) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate (2^n) T r) ≤
        Model.minimaxRiskOn (T := T) (rankClass (2^n) r) ∧
    Model.minimaxRiskOn (T := T) (rankClass (2^n) r) ≤
        rankClassWorstCaseRisk (2^n) T r
          (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (periodicEstimator h T) ∧
    rankClassWorstCaseRisk (2^n) T r
        (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
        (periodicEstimator h T) ≤
      ENNReal.ofReal (min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  exact corollary4_mw_algorithm_sandwich h hn hT hr hrD _
    (mw_minimizer_statistical_certificate h)

end
end TomographyOracleCore.PaperMatch.RankMinimax
