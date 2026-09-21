import TomographyOracleCore.PaperMatch.ExactCorollaryFourMW
import TomographyOracleCore.Revision.PaperTheorems

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk RankMinimax
open Revision.PhysicalMinimax Revision.ConstantEndpoints Revision.ConstantCovariance
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000

def omdRankUpperConstant : ℝ := max 4 PaperTheorems.statewiseOracleConstant

theorem omdRankUpperConstant_pos : 0 < omdRankUpperConstant :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) (le_max_left _ _)

theorem omd_record_rank_expected_upper
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r)
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (rho : DensityOperator (Fin (2^n))) (hrho : rho.matrix.rank ≤ r)
    (hrD : r ≤ 2^n) (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) (estimate sample) ≤
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) rho + gamma) :
    (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤
      min 2 (omdRankUpperConstant * (r : ℝ) *
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
  · have hb := PaperTheorems.statewise_adaptive_oracle h hn hT hlarge estimate rho
      gamma hgamma hgammaScale hfit r hr hrD
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
    have hC : 4 ≤ omdRankUpperConstant := le_max_left _ _
    have hCr : 4 ≤ omdRankUpperConstant * (r : ℝ) := by nlinarith
    have htwo : (2 : ℝ) ≤ omdRankUpperConstant * (r : ℝ) * q := by nlinarith
    exact hcap.trans htwo


theorem corollary4_omd_record
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2^n)
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (hmeas : Measurable estimate)
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ min 1 (Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ))))
    (hfit : ∀ rho : DensityOperator (Fin (2^n)),
      ∀ᵐ sample ∂periodicSampleLaw h T rho,
      ∀ sigma : DensityOperator (Fin (2^n)),
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) (estimate sample) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) sigma + gamma) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate (2^n) T r) ≤
        minimaxRisk (T := T) (rankClass (2^n) r) ∧
    minimaxRisk (T := T) (rankClass (2^n) r) ≤
        rankClassWorstCaseRisk (2^n) T r
          (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (mw_record_physical_estimator (by positivity)
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas) ∧
    rankClassWorstCaseRisk (2^n) T r
        (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
        (mw_record_physical_estimator (by positivity)
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas) ≤
      ENNReal.ofReal (min 2 (omdRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  have hd : 514 ≤ 2^n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨rank_minimax_lower_all_ranks hd hT r hr hrD, ?_, ?_⟩
  · exact iInf_le _ (Procedure.ofDominated
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (mw_record_physical_estimator (by positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas))
  · unfold rankClassWorstCaseRisk
    apply iSup_le
    intro rho
    have hf : ∀ᵐ sample ∂periodicSampleLaw h T rho.val,
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) (estimate sample) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
          (empiricalForwardMatrix sample) rho.val + gamma := by
      filter_upwards [hfit rho.val] with sample hs
      exact hs rho.val
    exact (mw_record_physicalRisk_le_integral (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas rho.val).trans
      (ENNReal.ofReal_le_ofReal (omd_record_rank_expected_upper h hn hT hr estimate
        rho.val rho.property hrD gamma hgamma (hgammaScale.trans (min_le_right _ _)) hf))

end
end TomographyOracleCore.PaperMatch.ExactMain
