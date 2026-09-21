import TomographyOracleCore.PaperMatch.ExactTheoremThree
import TomographyOracleCore.PaperMatch.LowerMoments.GeneralPureRisk
import TomographyOracleCore.PaperMatch.CorollaryFourUnconditional

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open Revision.NonadaptiveFano RankMinimax Revision.ConstantEndpoints
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 1500000
variable {Seed Outcome : Type*} [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

theorem rankClass_direct_lower_at_tail_rank
    (k m T r : ℕ) (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hD : 514 ≤ k + 2) (hT : 1 ≤ T) (hmr : m + 2 ≤ r)
    (design : OperatorDesign (k + 2) T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin (k + 2))))
    [IsMarkovKernel estimator] :
    ENNReal.ofReal (11 * directRankScale / 64 *
      min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ)))) ≤
      worstCaseRisk (rankClass (k + 2) r) design estimator := by
  let b := directRankScale * min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ)))
  have hk1 : 1 ≤ k := by omega
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk1
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have heta : 0 < Real.sqrt ((k : ℝ) / (T : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hkpos hTpos)
  have hbpos : 0 < b := mul_pos directRankScale_pos
    (lt_min zero_lt_one (mul_pos hmpos heta))
  have hb0 := hbpos.le
  have hbquarter : b ≤ 1 / 4 := calc
    b ≤ directRankScale * 1 :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) directRankScale_pos.le
    _ ≤ 1 / 4 := by simpa [directRankScale] using hardFamilyScaleConstant_le_quarter 2
  have hbscale : b ≤ lowerInformationConstant * (m : ℝ) *
      Real.sqrt ((k : ℝ) / (T : ℝ)) := calc
    b ≤ directRankScale * ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) directRankScale_pos.le
    _ ≤ lowerInformationConstant * ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))) :=
      mul_le_mul_of_nonneg_right (hardFamilyScaleConstant_le_information 2)
        (mul_nonneg hmpos.le heta.le)
    _ = _ := by ring
  obtain ⟨W, _hWcard⟩ := exists_complexGrassmannPackingWitness_card_eq hm hkm

  have hlog : 4 * Real.log 2 ≤ Real.log W.card :=
    (four_log_two_le_grassmann_exponent (k + 2) m hD hm).trans
      (by simpa [lowerAmbientDimension, grassmannGamma0] using W.log_cardinality_lower)
  let : NeZero W.card := ⟨by
    intro hc
    simp only [hc, Nat.cast_zero, Real.log_zero] at hlog
    have hpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith⟩
  have hclass : b ≤ (2 : ℝ) ^ (1 - (2 : ℝ)) * (2 * m) * (m : ℝ) ^ (1 - (2 : ℝ)) := by
    have heq : (2 : ℝ) ^ (1 - (2 : ℝ)) * (2 * m) * (m : ℝ) ^ (1 - (2 : ℝ)) = 1 := by
      norm_num [Real.rpow_neg_one]
      field_simp
    rw [heq]
    linarith
  obtain ⟨x, w, _, _, hmean⟩ := sectionC_fixed_state_bounds
    design.toDominated estimator W.projector b 2 (2 * m) hm hD hT hbpos hbquarter
    (by norm_num) (by exact_mod_cast (show 1 ≤ 2 * m by omega)) hclass W.pairwise_separated
    (by simpa [grassmannGamma0] using W.log_cardinality_lower) hbscale
  have hmean' := hmean.trans (le_iSup
    (fun rho : rankClass (k + 2) r => expectedTraceLoss design.experimentKernel estimator rho.1)
    ⟨_, (orientedHardProjector_rank_le w (W.projector x) b hm hb0 hbquarter).trans hmr⟩)
  have heq : 11 * directRankScale / 64 *
      min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))) = 11 * b / 64 := by
    dsimp [b]
    ring
  rw [heq]
  exact hmean'

theorem rank_minimax_lower_rank_ge_three
    (d T r : ℕ) (hd : 514 ≤ d) (hT : 1 ≤ T)
    (hr : 3 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (rankThreeLowerConstant * rankRate d T r) ≤
      minimaxRisk (T := T) (rankClass d r) := by
  let k := d - 2
  have heq : d = k + 2 := by dsimp [k]; omega
  have hk : 512 ≤ k := by dsimp [k]; omega
  rw [heq] at hrd ⊢
  let m := min (r - 2) (k / 3)
  have hm : 1 ≤ m := by dsimp [m]; omega
  have hkm : 3 * m ≤ k := by dsimp [m]; omega
  have hmr : m + 2 ≤ r := by dsimp [m]; omega
  have hrcap : r ≤ 6 * m := by dsimp [m]; omega
  have hTr : 0 < (T : ℝ) := by exact_mod_cast hT
  have hkr : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hksq : (Real.sqrt ((k : ℝ) / (T : ℝ))) ^ 2 = (k : ℝ) / (T : ℝ) :=
    Real.sq_sqrt (div_nonneg hkr hTr.le)
  have hdsq : (Real.sqrt (((k : ℝ) + 2) / (T : ℝ))) ^ 2 =
      ((k : ℝ) + 2) / (T : ℝ) := Real.sq_sqrt (by positivity)
  have hquot : ((k : ℝ) + 2) / (T : ℝ) ≤ 4 * ((k : ℝ) / (T : ℝ)) := by
    have hkreal : 512 ≤ (k : ℝ) := by exact_mod_cast hk
    have hh := (div_le_div_of_nonneg_right (show (k : ℝ) + 2 ≤ 4 * (k : ℝ) by linarith) hTr.le)
    simpa [mul_div_assoc] using hh
  have hsqrt : Real.sqrt (((k : ℝ) + 2) / (T : ℝ)) ≤
      2 * Real.sqrt ((k : ℝ) / (T : ℝ)) := by
    nlinarith [Real.sqrt_nonneg (((k : ℝ) + 2) / (T : ℝ)),
      Real.sqrt_nonneg ((k : ℝ) / (T : ℝ))]
  have hsc : (r : ℝ) * Real.sqrt (((k : ℝ) + 2) / (T : ℝ)) ≤
      12 * ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))) := by
    have hrr : (r : ℝ) ≤ 6 * (m : ℝ) := by exact_mod_cast hrcap
    calc
      _ ≤ (6 * (m : ℝ)) * (2 * Real.sqrt ((k : ℝ) / (T : ℝ))) :=
        mul_le_mul hrr hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring
  have hrate : rankRate (k + 2) T r ≤
      12 * min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))) := by
    unfold rankRate
    push_cast
    by_cases hc : 1 ≤ (m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))
    · rw [min_eq_left hc]
      exact (min_le_left _ _).trans (by norm_num)
    · rw [min_eq_right (le_of_not_ge hc)]
      exact (min_le_right _ _).trans hsc
  have hscalar : rankThreeLowerConstant * rankRate (k + 2) T r ≤
      11 * directRankScale / 64 *
        min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ))) := by
    calc
      _ ≤ rankThreeLowerConstant *
          (12 * min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ)))) :=
        mul_le_mul_of_nonneg_left hrate rankThreeLowerConstant_pos.le
      _ = _ := by dsimp [rankThreeLowerConstant]; ring
  apply le_iInf
  intro p
  exact (ENNReal.ofReal_le_ofReal hscalar).trans
    (rankClass_direct_lower_at_tail_rank k m T r hm hkm
      (by omega) hT hmr p.design p.estimator)




theorem pure_rank_minimax_lower {d T : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) :
    ENNReal.ofReal ((1 / 128 : ℝ) * rankRate d T 1) ≤
      minimaxRisk (T := T) (rankClass d 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
  have hm : 1 ≤ m := by omega
  let a := cubeAmplitude m T
  obtain ⟨ha0, hma, hTa, ha1⟩ := cubeAmplitude_bounds (T := T) hm
  have ha : (m : ℝ) * a ^ 2 ≤ 1 := by dsimp [a]; linarith
  apply le_iInf
  intro p
  obtain ⟨θ, hθ⟩ := Pure.exists_cube_expected_loss_ge hm a ha0.le ha ha1 hTa p.design p.estimator
  have hscale := cubeAmplitude_risk_scale hm hT
  have hrisk : ENNReal.ofReal ((1 / 128 : ℝ) * rankRate (m + 1) T 1) ≤
      expectedTraceLoss p.design.experimentKernel p.estimator (cubeState a ha θ) := by
    rw [← Pure.cubeExpectedLoss_ofReal a ha p.design p.estimator θ]
    exact ENNReal.ofReal_le_ofReal (hscale.trans hθ)
  exact hrisk.trans (le_iSup (fun ρ : rankClass (m + 1) 1 =>
    expectedTraceLoss p.design.experimentKernel p.estimator ρ.1)
      ⟨cubeState a ha θ, cubeState_rank_le_one a ha θ⟩)


/-- Inclusion of state classes increases the full-domain minimax risk. -/
theorem rankClass_minimaxRisk_mono {d T r s : ℕ} (hrs : r ≤ s) :
    minimaxRisk (T := T) (rankClass d r) ≤ minimaxRisk (T := T) (rankClass d s) := by
  apply iInf_mono
  intro p
  apply iSup_le
  intro rho
  exact le_iSup (fun sigma : rankClass d s =>
    expectedTraceLoss p.design.experimentKernel p.estimator sigma.1)
    ⟨rho.1, rankClass_mono hrs rho.2⟩

theorem rank_two_lower_of_pure_lower {d T : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hpure : ENNReal.ofReal (c * rankRate d T 1) ≤
      minimaxRisk (T := T) (rankClass d 1)) :
    ENNReal.ofReal ((c / 2) * rankRate d T 2) ≤
      minimaxRisk (T := T) (rankClass d 2) := by
  have hrate := rankRate_le_rank_mul_pureRate d T 2 (by omega)
  have hscale : (c / 2) * rankRate d T 2 ≤ c * rankRate d T 1 := by
    have h := mul_le_mul_of_nonneg_left hrate (show 0 ≤ c / 2 by positivity)
    norm_num at h
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hscale).trans
    (hpure.trans (rankClass_minimaxRisk_mono (by omega : 1 ≤ 2)))

/-- Once the pure-state endpoint is supplied, all ranks follow using the
already proved rank-at-least-three endpoint and a single positive constant. -/
theorem all_rank_lower_of_pure_lower {d T : ℕ} (hd : 514 ≤ d) (hT : 1 ≤ T)
    {c : ℝ} (hc : 0 < c)
    (hpure : ENNReal.ofReal (c * rankRate d T 1) ≤
      minimaxRisk (T := T) (rankClass d 1))
    (r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (min (c / 2) rankThreeLowerConstant * rankRate d T r) ≤
      minimaxRisk (T := T) (rankClass d r) := by
  have hrate := rankRate_nonneg d T r
  rcases show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega with h | h | h
  · subst r
    apply le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        ((min_le_left _ _).trans (show c / 2 ≤ c by linarith)) hrate)) hpure
  · subst r
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hrate)).trans
        (rank_two_lower_of_pure_lower hc.le hpure)
  · exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hrate)).trans
        (rank_minimax_lower_rank_ge_three d T r hd hT h hrd)

theorem rank_minimax_lower_all_ranks {d T : ℕ} (hd : 514 ≤ d) (hT : 1 ≤ T)
    (r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate d T r) ≤
      minimaxRisk (T := T) (rankClass d r) := by
  have hc : (1 / 128 : ℝ) / 2 = 1 / 256 := by norm_num
  simpa only [hc, unconditionalRankLowerConstant] using all_rank_lower_of_pure_lower hd hT
    (by norm_num : (0 : ℝ) < 1 / 128)
    (pure_rank_minimax_lower (by omega) hT) r hr hrd

/-- Corollary 4's full expected-risk sandwich for all ranks, without a
literature assumption or a probability/confidence premise. The estimator is
the existing rational OMD implementation on the encoded periodic experiment. -/
theorem corollary4
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2 ^ n) :
    ENNReal.ofReal (unconditionalRankLowerConstant * rankRate (2 ^ n) T r) ≤
        minimaxRisk (T := T) (rankClass (2 ^ n) r) ∧
    minimaxRisk (T := T) (rankClass (2 ^ n) r) ≤
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
  refine (minimaxRisk_le_fixedRisk (rankClass (2 ^ n) r)
    (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)).trans ?_
  rw [fixedRisk_ofDominated]
  exact iInf_le _ _

end
end TomographyOracleCore.PaperMatch.ExactMain
