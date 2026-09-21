import TomographyOracleCore.PaperMatch.ExactCorollaryFour
import TomographyOracleCore.PaperMatch.CorollaryFourMWPLS

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk MWPLS RankMinimax
open Revision.PhysicalMinimax Revision.ConstantEndpoints Revision.ConstantCovariance
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000

/-- The MW-PLS clause of Corollary 4 on the unrestricted operator-POVM domain,
for every measurable record rule satisfying the paper's optimization tolerance. -/
theorem corollary4_mw
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
      ENNReal.ofReal (min 2 (mwRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2^n : ℕ) : ℝ) / (T : ℝ)))) := by
  have hd : 514 ≤ 2^n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨rank_minimax_lower_all_ranks hd hT r hr hrD, ?_,
    (RankMinimax.corollary4_mw_record_sandwich h hn hT hr hrD estimate hmeas hcert).2.2⟩
  exact iInf_le _ (Procedure.ofDominated
    (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
    (mw_record_physical_estimator (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T estimate hmeas))

end
end TomographyOracleCore.PaperMatch.ExactMain
