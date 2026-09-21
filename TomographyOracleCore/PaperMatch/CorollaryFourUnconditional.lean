import TomographyOracleCore.PaperMatch.PureHypercubeRisk
import TomographyOracleCore.PaperMatch.PureHypercubeScale

/-! Corollary 4, Parts I and II: the small-rank proof is discharged using
actual pure states, dominated POVMs, common seeds, and reconstruction kernels.
The public conclusions below have no literature or statistical-bound premise. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalRisk
open Revision.ConstantEndpoints
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Pure-state full-trace expected minimax lower bound in the existing physical model. -/
theorem pure_rank_minimax_lower {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) :
    ENNReal.ofReal ((1 / 128 : ℝ) * rankRate d T 1) ≤
      Model.minimaxRiskOn (T := T) (rankClass d 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hm : 1 ≤ m := by omega
  let a := cubeAmplitude m T
  obtain ⟨ha0, hma, hTa, ha1⟩ := cubeAmplitude_bounds (T := T) hm
  have ha : (m : ℝ) * a ^ 2 ≤ 1 := by dsimp [a]; linarith
  apply le_iInf
  intro design
  apply le_iInf
  intro estimator
  obtain ⟨θ, hθ⟩ := exists_cube_expected_loss_ge hm a ha0.le ha ha1 hTa design estimator
  have hscale := cubeAmplitude_risk_scale hm hT
  have hrisk : ENNReal.ofReal ((1 / 128 : ℝ) * rankRate (m + 1) T 1) ≤
      statewiseExpectedTraceRisk design estimator (cubeState a ha θ) := by
    rw [← cubeExpectedLoss_ofReal a ha design estimator θ]
    exact ENNReal.ofReal_le_ofReal (hscale.trans hθ)
  exact hrisk.trans (le_iSup (fun ρ : rankClass (m + 1) 1 =>
    statewiseExpectedTraceRisk design estimator ρ.1)
      ⟨cubeState a ha θ, cubeState_rank_le_one a ha θ⟩)

/-- Rank two follows by class inclusion, with no undischarged pure-state premise. -/
theorem rank_two_minimax_lower {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) :
    ENNReal.ofReal ((1 / 256 : ℝ) * rankRate d T 2) ≤
      Model.minimaxRiskOn (T := T) (rankClass d 2) := by
  have hc : (1 / 128 : ℝ) / 2 = 1 / 256 := by norm_num
  simpa only [hc] using rank_two_lower_of_pure_lower (by norm_num : (0 : ℝ) ≤ 1 / 128)
    (pure_rank_minimax_lower hd hT)

/-- One positive coefficient valid for every rank. -/
def unconditionalRankLowerConstant : ℝ := min (1 / 256) rankThreeLowerConstant

theorem unconditionalRankLowerConstant_pos : 0 < unconditionalRankLowerConstant :=
  lt_min (by norm_num) rankThreeLowerConstant_pos

/-- Equality with Part I's explicit constant, gamma = min {1/4, c_I}. -/
theorem unconditionalRankLowerConstant_paper_value :
    unconditionalRankLowerConstant =
      min (11 * min (1 / 4) lowerInformationConstant / 768) (1 / 256) := by
  have hscale : directRankScale = min (1 / 4) lowerInformationConstant := by
    unfold directRankScale hardFamilyScaleConstant
    norm_num
    rw [← min_assoc, min_eq_left (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)]
  rw [unconditionalRankLowerConstant, rankThreeLowerConstant, hscale, min_comm]

/-- The complete nonadaptive lower bound, including ranks one and two. -/
theorem rank_minimax_lower_all_ranks {d T : ℕ} (hd : 514 ≤ d) (hT : 1 ≤ T)
    (r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate d T r) ≤
      Model.minimaxRiskOn (T := T) (rankClass d r) := by
  have hc : (1 / 128 : ℝ) / 2 = 1 / 256 := by norm_num
  simpa only [hc, unconditionalRankLowerConstant] using all_rank_lower_of_pure_lower hd hT
    (by norm_num : (0 : ℝ) < 1 / 128)
    (pure_rank_minimax_lower (by omega) hT) r hr hrd

/-- Corollary 4's full expected-risk sandwich for all ranks, without a
literature assumption or a probability/confidence premise. The estimator is
the existing rational OMD implementation on the encoded periodic experiment. -/
theorem corollary4_minimax_sandwich_unconditional
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2 ^ n) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate (2 ^ n) T r) ≤
        Model.minimaxRiskOn (T := T) (rankClass (2 ^ n) r) ∧
    Model.minimaxRiskOn (T := T) (rankClass (2 ^ n) r) ≤
        rankClassWorstCaseRisk (2 ^ n) T r
          (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (dimensionRationalPhysicalEstimator h hT) ∧
    rankClassWorstCaseRisk (2 ^ n) T r
        (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
        (dimensionRationalPhysicalEstimator h hT) ≤
      ENNReal.ofReal (min 2 (certifiedRankUpperConstant * (r : ℝ) *
        Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))) := by
  have hd : 514 ≤ 2 ^ n :=
    (by norm_num : 514 ≤ 65536).trans (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  refine ⟨rank_minimax_lower_all_ranks hd hT r hr hrD, ?_,
    dimensionRational_rankClass_physicalUpper h hn hT hr hrD⟩
  exact (iInf_le _ _).trans (iInf_le _ _)

end
end TomographyOracleCore.PaperMatch.RankMinimax
