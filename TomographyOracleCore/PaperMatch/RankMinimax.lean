import TomographyOracleCore.Revision.ConstantRankEndpoints
import TomographyOracleCore.PaperMatch.Model.StatesRisk
import TomographyOracleCore.SharedHaarFanoAssembly
import Mathlib.Probability.Kernel.Representation
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Corollary 4: rank-class minimax assembly

The state class, observations, reconstruction kernels, and full trace loss are
the manuscript's physical objects. The upper bound is the previously proved
OMD bound. The probability-to-expectation conversion, uniform constants,
optimization over designs, and kernel-randomness representation are proved here.

LiteratureLowerBound records the t = 1 specialization of Nayak--Zhou,
arXiv:2609.10514v1, Theorem 1.1 and Section 3.5. It is an explicit theorem
argument, not an axiom and not a proved instance. This module does not formalize
their Fisher-information and van Trees proof. The minimax theorem in this historical assembly is conditional on that input.
The public `CorollaryFourUnconditional.lean` now removes it using direct
large-rank and pure-hypercube proofs, including ranks one and two.
-/

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalRisk
open Revision.ConstantEndpoints
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1000000

/-- The actual rank-at-most class, rather than an eigenvalue-decay surrogate. -/
def rankClass (d r : ℕ) : Set (DensityOperator (Fin d)) :=
  {rho | rho.matrix.rank ≤ r}

/-- The capped rank rate in equation (28). -/
def rankRate (d T r : ℕ) : ℝ :=
  min 1 ((r : ℝ) * Real.sqrt ((d : ℝ) / (T : ℝ)))

/-- Full trace-norm success event; no factor one half is built into the loss. -/
def successProbability {d T : ℕ} (design : Design d T)
    (estimator : Estimator d T) (rho : DensityOperator (Fin d)) (epsilon : ℝ) : ℝ≥0∞ :=
  estimateKernel design estimator rho
      {sigma | hermitianTraceLoss rho sigma ≤ ENNReal.ofReal epsilon}

/-- Strict failure event, complementary to full trace-norm success. -/
def failureProbability {d T : ℕ} (design : Design d T)
    (estimator : Estimator d T) (rho : DensityOperator (Fin d)) (epsilon : ℝ) : ℝ≥0∞ :=
  estimateKernel design estimator rho
    {sigma | ENNReal.ofReal epsilon < hermitianTraceLoss rho sigma}

/-- Success and failure probabilities refer to complementary measurable events. -/
theorem successProbability_eq_one_sub_failureProbability {d T : ℕ}
    (design : Design d T) (estimator : Estimator d T)
    (rho : DensityOperator (Fin d)) (epsilon : ℝ) :
    successProbability design estimator rho epsilon =
      1 - failureProbability design estimator rho epsilon := by
  let mu := estimateKernel design estimator rho
  have hloss : Measurable (hermitianTraceLoss rho) := by
    simpa only [Function.comp_def] using
      (hermitianTraceLoss_pair_measurable (D := d)).comp
        (measurable_const.prodMk measurable_id :
          Measurable (fun sigma : DensityOperator (Fin d) => (rho, sigma)))
  have hbad : MeasurableSet
      {sigma | ENNReal.ofReal epsilon < hermitianTraceLoss rho sigma} :=
    measurableSet_lt measurable_const hloss
  have hcompl : {sigma | ENNReal.ofReal epsilon < hermitianTraceLoss rho sigma}ᶜ =
      {sigma | hermitianTraceLoss rho sigma ≤ ENNReal.ofReal epsilon} := by
    ext sigma
    simp
  change mu {sigma | hermitianTraceLoss rho sigma ≤ ENNReal.ofReal epsilon} = _
  rw [← hcompl, measure_compl hbad (measure_ne_top mu _)]
  simp only [measure_univ, failureProbability, mu]

/-- The pointwise tail contribution lower-bounds the expectation. -/
theorem threshold_mul_failureProbability_le_expected {d T : ℕ}
    (design : Design d T) (estimator : Estimator d T)
    (rho : DensityOperator (Fin d)) (epsilon : ℝ) :
    ENNReal.ofReal epsilon * failureProbability design estimator rho epsilon ≤
      statewiseExpectedTraceRisk design estimator rho := by
  have hloss : Measurable (hermitianTraceLoss rho) := by
    simpa only [Function.comp_def] using
      (hermitianTraceLoss_pair_measurable (D := d)).comp
        (measurable_const.prodMk measurable_id :
          Measurable (fun sigma : DensityOperator (Fin d) => (rho, sigma)))
  calc
    _ ≤ ENNReal.ofReal epsilon * estimateKernel design estimator rho
        {sigma | ENNReal.ofReal epsilon ≤ hermitianTraceLoss rho sigma} := by
      gcongr 1
      exact measure_mono (fun sigma
        (h : ENNReal.ofReal epsilon < hermitianTraceLoss rho sigma) => le_of_lt h)
    _ ≤ _ := mul_meas_ge_le_lintegral hloss (ENNReal.ofReal epsilon)

/-- The physical coordinate sigma-algebra is standard Borel. -/
theorem density_standard_borel (d : ℕ) : StandardBorelSpace (DensityOperator (Fin d)) := by
  have hm : Isometry (DensityOperator.matrix :
      DensityOperator (Fin d) → Matrix (Fin d) (Fin d) ℂ) := fun _ _ => rfl
  have hc : Continuous (PhysicalPOVM.densityCoordinates d) := by
    exact continuous_pi fun p =>
      (continuous_apply p.2).comp ((continuous_apply p.1).comp hm.continuous)
  have hb : BorelSpace (DensityOperator (Fin d)) := by
    constructor
    apply le_antisymm
    · change MeasurableSpace.comap (PhysicalPOVM.densityCoordinates d) _ ≤ _
      have h := hc.borel_measurable
      rw [← (BorelSpace.measurable_eq (α := Fin d × Fin d → ℂ))] at h
      exact measurable_iff_comap_le.mp h
    · exact OpensMeasurableSpace.borel_le
  let : BorelSpace (DensityOperator (Fin d)) := hb
  let : CompactSpace (DensityOperator (Fin d)) :=
    ⟨DensityCompact.isCompact_univ_densityOperator⟩
  let : SecondCountableTopology (DensityOperator (Fin d)) := hm.isEmbedding.secondCountableTopology
  infer_instance

/-- A physical randomized reconstruction is a measurable function of its data
and one independent uniform seed (Kallenberg, Lemma 4.22). -/
theorem estimator_uniform_seed_representation {d T : ℕ} (hd : 0 < d)
    (estimator : Estimator d T) :
    ∃ f : Data T → unitInterval → DensityOperator (Fin d),
      Measurable (Function.uncurry f) ∧
      ∀ data, Measure.map (f data) volume = estimator.kernel data := by
  let : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  let : Nonempty (DensityOperator (Fin d)) := DensityGrid.densityOperator_nonempty
  let : StandardBorelSpace (DensityOperator (Fin d)) := density_standard_borel d
  exact Kernel.exists_measurable_map_eq_unitInterval estimator.kernel

/-- Markov's inequality on the actual output measure, with the strict failure
event complementary to the success event used by the cited theorem. -/
theorem successProbability_ge_two_thirds_of_expected_le {d T : ℕ}
    (design : Design d T) (estimator : Estimator d T)
    (rho : DensityOperator (Fin d)) {epsilon : ℝ} (he : 0 < epsilon)
    (hrisk : statewiseExpectedTraceRisk design estimator rho ≤
      ENNReal.ofReal (epsilon / 3)) :
    (2 / 3 : ℝ≥0∞) ≤ successProbability design estimator rho epsilon := by
  let mu := estimateKernel design estimator rho
  let loss := hermitianTraceLoss rho
  have hloss : Measurable loss := by
    simpa only [Function.comp_def] using
      (hermitianTraceLoss_pair_measurable (D := d)).comp
        (measurable_const.prodMk measurable_id :
          Measurable (fun sigma : DensityOperator (Fin d) => (rho, sigma)))
  have he0 : ENNReal.ofReal epsilon ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr he)
  have htail : mu {sigma | ENNReal.ofReal epsilon < loss sigma} ≤ (1 / 3 : ℝ≥0∞) := by
    calc
      _ ≤ mu {sigma | ENNReal.ofReal epsilon ≤ loss sigma} :=
        measure_mono (fun sigma (h : ENNReal.ofReal epsilon < loss sigma) => le_of_lt h)
      _ ≤ (∫⁻ sigma, loss sigma ∂mu) / ENNReal.ofReal epsilon :=
        meas_ge_le_lintegral_div hloss.aemeasurable he0 ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (epsilon / 3) / ENNReal.ofReal epsilon :=
        ENNReal.div_le_div_right hrisk _
      _ = (1 / 3 : ℝ≥0∞) := by
        rw [← ENNReal.ofReal_div_of_pos he]
        have h : epsilon / 3 / epsilon = (1 / 3 : ℝ) := by field_simp
        rw [h, ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
        norm_num
  have hbad : MeasurableSet {sigma | ENNReal.ofReal epsilon < loss sigma} :=
    measurableSet_lt measurable_const hloss
  have hcompl : {sigma | ENNReal.ofReal epsilon < loss sigma}ᶜ =
      {sigma | loss sigma ≤ ENNReal.ofReal epsilon} := by
    ext sigma
    simp
  change (2 / 3 : ℝ≥0∞) ≤ mu {sigma | loss sigma ≤ ENNReal.ofReal epsilon}
  rw [← hcompl, measure_compl hbad (measure_ne_top mu _)]
  have hprob : mu Set.univ = 1 := measure_univ
  rw [hprob]
  calc
    (2 / 3 : ℝ≥0∞) = 1 - (1 / 3 : ℝ≥0∞) := by
      have h := ENNReal.ofReal_sub (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 3)
      norm_num only [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at h
      simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
        ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h
    _ ≤ 1 - mu {sigma | ENNReal.ofReal epsilon < loss sigma} :=
      tsub_le_tsub_left htail 1

/-- The exact external sample lower bound needed by the revised corollary.
Its constants are uniform in dimension, rank, sample count, design, and fit.
The theorem argument is deliberately not filled by a new axiom. -/
structure LiteratureLowerBound where
  sampleConstant : ℝ
  errorRadius : ℝ
  sampleConstant_pos : 0 < sampleConstant
  errorRadius_pos : 0 < errorRadius
  sample_bound :
    ∀ {d T r : ℕ}, 2 ≤ d → 1 ≤ T → 1 ≤ r → r ≤ d →
    ∀ (design : Design d T) (estimator : Estimator d T)
      (epsilon : ℝ), 0 < epsilon → epsilon ≤ errorRadius →
      (∀ rho : DensityOperator (Fin d), rho.matrix.rank ≤ r →
        (2 / 3 : ℝ≥0∞) ≤ successProbability design estimator rho epsilon) →
      sampleConstant * (d : ℝ) * (r : ℝ) ^ 2 / epsilon ^ 2 ≤ (T : ℝ)

namespace LiteratureLowerBound

/-- A single universal accuracy scale valid in both capped regimes. -/
def accuracyScale (input : LiteratureLowerBound) : ℝ :=
  min input.errorRadius (Real.sqrt input.sampleConstant / 2)

/-- The lower constant used in the manuscript proof of Corollary 4. -/
def riskConstant (input : LiteratureLowerBound) : ℝ := input.accuracyScale / 3

theorem accuracyScale_pos (input : LiteratureLowerBound) : 0 < input.accuracyScale :=
  lt_min input.errorRadius_pos (div_pos (Real.sqrt_pos.mpr input.sampleConstant_pos) (by norm_num))

theorem riskConstant_pos (input : LiteratureLowerBound) : 0 < input.riskConstant :=
  div_pos input.accuracyScale_pos (by norm_num)

theorem accuracyScale_le_errorRadius (input : LiteratureLowerBound) :
    input.accuracyScale ≤ input.errorRadius := min_le_left _ _

theorem four_mul_accuracyScale_sq_le (input : LiteratureLowerBound) :
    4 * input.accuracyScale ^ 2 ≤ input.sampleConstant := by
  have hle : input.accuracyScale ≤ Real.sqrt input.sampleConstant / 2 := min_le_right _ _
  have hpos := input.accuracyScale_pos
  have hs := Real.sq_sqrt input.sampleConstant_pos.le
  have hsq := sq_le_sq₀ hpos.le (show 0 ≤ Real.sqrt input.sampleConstant / 2 by positivity)
  have hmul : input.accuracyScale ^ 2 ≤ (Real.sqrt input.sampleConstant / 2) ^ 2 :=
    hsq.mpr hle
  nlinarith

end LiteratureLowerBound

/-- The contrapositive of the cited sample theorem produces a hard state for
each procedure. No uniform success assumption is made in this conclusion. -/
theorem exists_failure_gt_one_third_of_sample_lt (input : LiteratureLowerBound)
    {d T r : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) (hr : 1 ≤ r) (hrd : r ≤ d)
    (design : Design d T) (estimator : Estimator d T)
    {epsilon : ℝ} (he : 0 < epsilon) (hemax : epsilon ≤ input.errorRadius)
    (hsample : (T : ℝ) <
      input.sampleConstant * (d : ℝ) * (r : ℝ) ^ 2 / epsilon ^ 2) :
    ∃ rho : DensityOperator (Fin d), rho.matrix.rank ≤ r ∧
      (1 / 3 : ℝ≥0∞) < failureProbability design estimator rho epsilon := by
  have hnot : ¬ ∀ rho : DensityOperator (Fin d), rho.matrix.rank ≤ r →
      (2 / 3 : ℝ≥0∞) ≤ successProbability design estimator rho epsilon := by
    intro hsuccess
    exact (not_le_of_gt hsample)
      (input.sample_bound hd hT hr hrd design estimator epsilon he hemax hsuccess)
  push Not at hnot
  obtain ⟨rho, hrho, hsuccess⟩ := hnot
  refine ⟨rho, hrho, ?_⟩
  by_contra! hfailure
  have hthird : (2 / 3 : ℝ≥0∞) = 1 - (1 / 3 : ℝ≥0∞) := by
    have h := ENNReal.ofReal_sub (1 : ℝ) (by norm_num : (0 : ℝ) ≤ 1 / 3)
    norm_num only [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num] at h
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3),
      ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h
  apply (not_le_of_gt hsuccess)
  rw [successProbability_eq_one_sub_failureProbability, hthird]
  exact tsub_le_tsub_left hfailure 1

/-- Direct conversion of a hard state's failure probability to expected loss. -/
theorem expected_gt_third_of_failure_gt_one_third {d T : ℕ}
    (design : Design d T) (estimator : Estimator d T)
    (rho : DensityOperator (Fin d)) {epsilon : ℝ} (he : 0 < epsilon)
    (hfailure : (1 / 3 : ℝ≥0∞) < failureProbability design estimator rho epsilon) :
    ENNReal.ofReal (epsilon / 3) < statewiseExpectedTraceRisk design estimator rho := by
  have heq : ENNReal.ofReal (epsilon / 3) = ENNReal.ofReal epsilon * (1 / 3 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 3)]
    simp only [ENNReal.ofReal_ofNat, div_eq_mul_inv, one_mul]
  calc
    _ = ENNReal.ofReal epsilon * (1 / 3 : ℝ≥0∞) := heq
    _ < ENNReal.ofReal epsilon * failureProbability design estimator rho epsilon :=
      ENNReal.mul_lt_mul_right (ne_of_gt (ENNReal.ofReal_pos.mpr he))
        ENNReal.ofReal_ne_top hfailure
    _ ≤ _ := threshold_mul_failureProbability_le_expected design estimator rho epsilon

theorem rankRate_pos {d T r : ℕ} (hd : 0 < d) (hT : 0 < T) (hr : 0 < r) :
    0 < rankRate d T r := by
  unfold rankRate
  apply lt_min zero_lt_one
  apply mul_pos (by exact_mod_cast hr)
  exact Real.sqrt_pos.mpr (div_pos (by exact_mod_cast hd) (by exact_mod_cast hT))

/-- The exact sample/accuracy inequality used in the contrapositive, including
the saturation regime where the rank rate is capped by one. -/
theorem scaled_rankRate_sample_bound (input : LiteratureLowerBound)
    {d T r : ℕ} (hd : 0 < d) (hT : 0 < T) (hr : 0 < r) :
    4 * (T : ℝ) * (input.accuracyScale * rankRate d T r) ^ 2 ≤
      input.sampleConstant * (d : ℝ) * (r : ℝ) ^ 2 := by
  have hTr : (0 : ℝ) < T := by exact_mod_cast hT
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hq := (rankRate_pos hd hT hr).le
  have hqle : rankRate d T r ≤ (r : ℝ) * Real.sqrt ((d : ℝ) / (T : ℝ)) :=
    min_le_right _ _
  have hsq : rankRate d T r ^ 2 ≤ (r : ℝ) ^ 2 * ((d : ℝ) / (T : ℝ)) := by
    calc
      _ ≤ ((r : ℝ) * Real.sqrt ((d : ℝ) / (T : ℝ))) ^ 2 :=
        (sq_le_sq₀ hq (by positivity)).mpr hqle
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hTq : (T : ℝ) * rankRate d T r ^ 2 ≤ (d : ℝ) * (r : ℝ) ^ 2 := by
    calc
      _ ≤ (T : ℝ) * ((r : ℝ) ^ 2 * ((d : ℝ) / (T : ℝ))) :=
        mul_le_mul_of_nonneg_left hsq hTr.le
      _ = _ := by field_simp
  calc
    _ = (4 * input.accuracyScale ^ 2) * ((T : ℝ) * rankRate d T r ^ 2) := by ring
    _ ≤ input.sampleConstant * ((d : ℝ) * (r : ℝ) ^ 2) :=
      mul_le_mul input.four_mul_accuracyScale_sq_le hTq (by positivity) input.sampleConstant_pos.le
    _ = _ := by ring

/-- Every physical nonadaptive procedure has the capped expected-risk lower
bound, conditional only on the explicitly stated literature sample theorem. -/
theorem rankClass_expected_lower_of_literature (input : LiteratureLowerBound)
    {d T r : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) (hr : 1 ≤ r) (hrd : r ≤ d)
    (design : Design d T) (estimator : Estimator d T) :
    ENNReal.ofReal (input.riskConstant * rankRate d T r) ≤
      rankClassWorstCaseRisk d T r design estimator := by
  have hd0 : 0 < d := by omega
  have hT0 : 0 < T := by omega
  have hr0 : 0 < r := by omega
  let epsilon := input.accuracyScale * rankRate d T r
  have he : 0 < epsilon := mul_pos input.accuracyScale_pos (rankRate_pos hd0 hT0 hr0)
  have hemax : epsilon ≤ input.errorRadius := by
    calc
      _ ≤ input.accuracyScale * 1 :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) input.accuracyScale_pos.le
      _ ≤ input.errorRadius := by simpa using input.accuracyScale_le_errorRadius
  have hbound := scaled_rankRate_sample_bound input hd0 hT0 hr0
  have he2 : 0 < epsilon ^ 2 := sq_pos_of_pos he
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT0
  change 4 * (T : ℝ) * epsilon ^ 2 ≤ _ at hbound
  have hfour : 4 * (T : ℝ) ≤
      input.sampleConstant * (d : ℝ) * (r : ℝ) ^ 2 / epsilon ^ 2 :=
    (le_div_iff₀ he2).mpr hbound
  have hsample : (T : ℝ) <
      input.sampleConstant * (d : ℝ) * (r : ℝ) ^ 2 / epsilon ^ 2 :=
    (by linarith : (T : ℝ) < 4 * T).trans_le hfour
  obtain ⟨rho, hrho, hfailure⟩ :=
    exists_failure_gt_one_third_of_sample_lt input hd hT hr hrd design estimator he hemax hsample
  have heq : input.riskConstant * rankRate d T r = epsilon / 3 := by
    dsimp [LiteratureLowerBound.riskConstant, epsilon]
    ring
  rw [heq]
  exact (expected_gt_third_of_failure_gt_one_third design estimator rho he hfailure).le.trans
    (le_iSup (fun state : {state : DensityOperator (Fin d) // state.matrix.rank ≤ r} =>
      statewiseExpectedTraceRisk design estimator state.val) ⟨rho, hrho⟩)

/-- Optimization over the entire physical design and reconstruction classes. -/
theorem rank_minimax_lower_of_literature (input : LiteratureLowerBound)
    {d T r : ℕ} (hd : 2 ≤ d) (hT : 1 ≤ T) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (input.riskConstant * rankRate d T r) ≤
      Model.minimaxRiskOn (T := T) (rankClass d r) := by
  exact le_iInf fun design => le_iInf fun estimator =>
    rankClass_expected_lower_of_literature input hd hT hr hrd design estimator

/-- Equation (28), including both lower and upper bounds, for the implemented
rational OMD estimator. The only literature input is the sample lower bound. -/
theorem corollary4_minimax_sandwich (input : LiteratureLowerBound)
    {n K T r : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hr : 1 ≤ r) (hrD : r ≤ 2 ^ n) :
    ENNReal.ofReal (input.riskConstant * rankRate (2 ^ n) T r) ≤
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
  have hd : 2 ≤ 2 ^ n := by
    exact (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn)
  refine ⟨rank_minimax_lower_of_literature input hd hT hr hrD, ?_,
    dimensionRational_rankClass_physicalUpper h hn hT hr hrD⟩
  exact (iInf_le _ _).trans (iInf_le _ _)

end
end TomographyOracleCore.PaperMatch.RankMinimax
