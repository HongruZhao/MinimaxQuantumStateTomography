import TomographyOracleCore.PaperMatch.SharedHaarOn
import TomographyOracleCore.PaperMatch.RankMinimax
import TomographyOracleCore.PhysicalSharedHaarLowerUnconditional

/-! Direct lower bounds for the actual rank-at-most class using the existing
physical nonadaptive experiment. This module starts at rank three because
the hard states have two head eigenvalues and a nonzero rank-m tail. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory InformationTheory MatrixReduction PhysicalRisk
open Revision.ConstantEndpoints
open scoped BigOperators ENNReal ComplexOrder Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000

lemma rank_eq_card_nonzero_roots {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    A.rank = ((A.charpoly.roots.map RCLike.re).filter (· ≠ 0)).card := by
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_def, RCLike.ofReal_re]
  rw [Multiset.filter_map, Multiset.card_map]
  change A.rank = (Finset.univ.filter (fun i => hA.eigenvalues i ≠ 0)).card
  rw [← Fintype.card_subtype]
  exact hA.rank_eq_card_non_zero_eigs

lemma hardProjector_rank_le {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hbq : b ≤ 1 / 4) :
    (hardProjectorDensityOperator P b hm hb hbq).matrix.rank ≤ m + 2 := by
  change (hardProjectorMatrix P b).rank ≤ _
  rw [rank_eq_card_nonzero_roots _ (hardProjectorMatrix_posSemidef P b hm hb hbq).isHermitian,
    hardProjectorMatrix_roots_re_eq_spectrum]
  change ((hardProjectorSpectrumList k m b).filter (fun x => decide (x ≠ 0))).length ≤ m + 2
  simp only [hardProjectorSpectrumList, List.filter_append, List.filter_replicate,
    ne_self_iff_false, decide_false, Bool.false_eq_true, ↓reduceIte,
    List.append_nil]
  exact (List.length_filter_le _ _).trans_eq (hardSpectrumList_length m b)

lemma orientedHardProjector_rank_le {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb : 0 ≤ b) (hbq : b ≤ 1 / 4) :
    (orientedHardProjectorDensityOperator U P b hm hb hbq).matrix.rank ≤ m + 2 := by
  rw [orientedHardProjectorDensityOperator_matrix, unitaryConjugateMatrix_apply]
  exact (Matrix.rank_mul_le_left _ _).trans
    ((Matrix.rank_mul_le_right _ _).trans (hardProjector_rank_le P b hm hb hbq))


/-- A fixed positive numerical coefficient; no statistical theorem is supplied. -/
def directRankScale : ℝ := hardFamilyScaleConstant 2

theorem directRankScale_pos : 0 < directRankScale := hardFamilyScaleConstant_pos 2

/-- Hard-family lower bound on rank at most m+2, for every physical design
and randomized reconstruction kernel. -/
theorem rankClass_direct_lower_at_tail_rank
    (k m T r : ℕ) (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hD : 514 ≤ k + 2) (hT : 1 ≤ T) (hmr : m + 2 ≤ r)
    (design : Design (k + 2) T) (estimator : Estimator (k + 2) T) :
    ENNReal.ofReal (11 * directRankScale / 64 *
      min 1 ((m : ℝ) * Real.sqrt ((k : ℝ) / (T : ℝ)))) ≤
      Model.worstCaseRiskOn (rankClass (k + 2) r) design estimator := by
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
  let state : Fin W.card → unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) →
      DensityOperator (Fin (k + 2)) := fun a U =>
    orientedHardProjectorDensityOperator U (W.projector a) b hm hb0 hbquarter
  let reference := orientedHardReferenceDensityOperator k b hk1 hb0 hbquarter
  let budget : Fin T → ENNReal := fun _ => ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ)))
  have hstate : ∀ a, Measurable (state a) := fun a =>
    measurable_orientedHardProjectorDensityOperator (W.projector a) b hm hb0 hbquarter
  have hreference : Measurable reference :=
    measurable_orientedHardReferenceDensityOperator k b hk1 hb0 hbquarter
  have hlogTwo : 4 * Real.log 2 ≤ Real.log (W.card : ℝ) :=
    (four_log_two_le_grassmann_exponent (k + 2) m hD hm).trans
      (by simpa [lowerAmbientDimension, grassmannGamma0] using W.log_cardinality_lower)
  have hN : 2 ≤ W.card := by
    have hp : 0 < Real.log (W.card : ℝ) :=
      (mul_pos (by norm_num) (Real.log_pos (by norm_num))).trans_le hlogTwo
    have hc : 1 < (W.card : ℝ) := (Real.log_pos_iff (by positivity)).mp hp
    exact_mod_cast hc
  let : NeZero W.card := ⟨by omega⟩
  have hfano := sharedHaar_lower_on (rankClass (k + 2) r) hN
    design estimator (unitaryHaarProbability (k + 2)) state reference
    hstate hreference (b / 4) (by positivity) (fun U a =>
      (orientedHardProjector_rank_le U (W.projector a) b hm hb0 hbquarter).trans hmr)
  have hsep : ∀ U a c, a ≠ c → 2 * (b / 4) ≤
      realHermitianTraceLoss (state a U) (state c U) := by
    intro U a c hac
    have hs := orientedHardProjectorDensityOperator_traceDistance_ge_half_mass
      U (W.projector c) (W.projector a) b hm hb0 hbquarter
        (W.pairwise_separated c a hac.symm)
    change 2 * (b / 4) ≤ _
    simpa only [state, realHermitianTraceLoss] using
      (show 2 * (b / 4) ≤ _ from (by convert hs using 1 <;> ring))
  have hfinite : (∑ t, budget t) ≠ ∞ := by
    simpa [budget, Finset.sum_const, nsmul_eq_mul] using
      (ENNReal.mul_ne_top (show (T : ENNReal) ≠ ∞ by simp)
        (show ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ))) ≠ ∞ by simp))
  have hshot : ∀ a t,
      klDiv (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ
        PhysicalPOVM.RandomizedNonadaptiveDesign.sharedOrientationShotKernel
          design (state a) (hstate a) t)
        (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ
        PhysicalPOVM.RandomizedNonadaptiveDesign.sharedOrientationShotKernel
          design reference hreference t) ≤ budget t := by
    intro a t
    exact PhysicalPOVM.RandomizedNonadaptiveDesign.klDiv_sharedOrientationShotKernel_orientedHardProjector_le
      design (W.projector a) b hm hk1 hbpos hbquarter t
  have hi : (∑ t, budget t).toReal ≤ Real.log (W.card : ℝ) / 16 := by
    have hs := informationRadius_le_logCardinality_div_sixteen
      (m : ℝ) (k : ℝ) (T : ℝ) b (Real.log (W.card : ℝ))
      hmpos hkpos hTpos hb0 hbscale W.log_cardinality_lower
    simpa only [budget, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (show 0 ≤ 8 * b ^ 2 / (3 * (m : ℝ)) by positivity)] using hs
  convert hfano hsep budget hfinite hshot hi hlogTwo using 1 <;> dsimp [b] <;> congr 1 <;> ring



/-- Uniform lower coefficient for the proved rank-at-least-three endpoint. -/
def rankThreeLowerConstant : ℝ := 11 * directRankScale / 768

theorem rankThreeLowerConstant_pos : 0 < rankThreeLowerConstant := by
  exact div_pos (mul_pos (by norm_num) directRankScale_pos) (by norm_num)

/-- The nonadaptive rank-class lower bound, without a literature premise,
for every 3 ≤ r ≤ d and d ≥ 514. Ranks one and two are not asserted here. -/
theorem rank_minimax_lower_rank_ge_three
    (d T r : ℕ) (hd : 514 ≤ d) (hT : 1 ≤ T)
    (hr : 3 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (rankThreeLowerConstant * rankRate d T r) ≤
      Model.minimaxRiskOn (T := T) (rankClass d r) := by
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
  intro design
  apply le_iInf
  intro estimator
  exact (ENNReal.ofReal_le_ofReal hscalar).trans
    (rankClass_direct_lower_at_tail_rank k m T r hm hkm
      (by omega) hT hmr design estimator)



/-- Corollary 4's full expected-risk sandwich, without a literature premise,
on the proved range 3 ≤ r ≤ 2^n. This does not claim the r=1 or r=2 cases. -/
theorem corollary4_minimax_sandwich_rank_ge_three
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 3 ≤ r) (hrD : r ≤ 2 ^ n) :
    ENNReal.ofReal (rankThreeLowerConstant * rankRate (2 ^ n) T r) ≤
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
  refine ⟨rank_minimax_lower_rank_ge_three _ _ _ hd hT hr hrD, ?_,
    dimensionRational_rankClass_physicalUpper h hn hT (by omega) hrD⟩
  exact (iInf_le _ _).trans (iInf_le _ _)


end
end TomographyOracleCore.PaperMatch.RankMinimax
