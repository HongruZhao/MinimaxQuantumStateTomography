import TomographyOracleCore.Revision.NonadaptiveFanoPhysical
import TomographyOracleCore.LowerInformationAlgebra
import TomographyOracleCore.GrassmannThreshold

namespace TomographyOracleCore.Revision.NonadaptiveFano

open MeasureTheory ProbabilityTheory InformationTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators ENNReal
noncomputable section
set_option maxHeartbeats 1200000

section GeneralGeometry
variable {D N : ℕ} [NeZero N]
  {Orientation Record : Type*}
  [MeasurableSpace Orientation]
  [MeasurableSpace Record]

/-- Run the physical estimator on `(seed,outcomes)` while copying the genie
orientation unchanged into its output. -/
noncomputable def augmentedEstimateKernel
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator] :
    Kernel (Orientation × Record)
      (Orientation × DensityOperator (Fin D)) :=
  (Kernel.deterministic (fun p : Orientation × Record ↦ p.1)
      measurable_fst) ×ₖ
    Kernel.prodMkLeft Orientation estimator

instance augmentedEstimateKernel_isMarkov
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator] :
    IsMarkovKernel (augmentedEstimateKernel
      (Orientation := Orientation) estimator) := by
  unfold augmentedEstimateKernel
  infer_instance

/-- The genie estimator followed by the measurable orientation-dependent
nearest-state decoder. -/
noncomputable def nearestDecodeKernel
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (_hstate : ∀ a, Measurable (state a)) :
    Kernel (Orientation × Record) (Fin N) :=
  (augmentedEstimateKernel (Orientation := Orientation) estimator).map
    (orientedFiniteTraceNearestDecoder state)

instance nearestDecodeKernel_isMarkov
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    IsMarkovKernel (nearestDecodeKernel estimator state hstate) := by
  unfold nearestDecodeKernel
  exact Kernel.IsMarkovKernel.map _
    (orientedFiniteTraceNearestDecoder_measurable state hstate)

/-- The finite Markov experiment obtained by drawing one common orientation,
running the physical experiment at the corresponding hard state, estimating,
and decoding with access to that orientation. -/
noncomputable def nearestDecodedLaw
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    Kernel (Fin N) (Fin N) where
  toFun a :=
    (nearestDecodeKernel estimator state hstate) ∘ₘ
      (orientationLaw ⊗ₘ
        (experiment.comap (state a) (hstate a)))
  measurable' := Measurable.of_discrete

instance nearestDecodedLaw_isMarkov
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    IsMarkovKernel
      (nearestDecodedLaw experiment estimator orientationLaw
        state hstate) := by
  constructor
  intro a
  change IsProbabilityMeasure
    ((nearestDecodeKernel estimator state hstate) ∘ₘ
      (orientationLaw ⊗ₘ
        (experiment.comap (state a) (hstate a))))
  infer_instance

noncomputable def augmentedEstimateLaw
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    Measure (Orientation × DensityOperator (Fin D)) :=
  (augmentedEstimateKernel (Orientation := Orientation) estimator) ∘ₘ
    (orientationLaw ⊗ₘ
      (experiment.comap state hstate))

instance augmentedEstimateLaw_isProbability
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    IsProbabilityMeasure
      (augmentedEstimateLaw experiment estimator orientationLaw
        state hstate) := by
  unfold augmentedEstimateLaw
  infer_instance

theorem nearestDecodedLaw_apply_eq_map_genieEstimate
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (a : Fin N) :
    nearestDecodedLaw experiment estimator orientationLaw
        state hstate a =
      (augmentedEstimateLaw experiment estimator orientationLaw
        (state a) (hstate a)).map
          (orientedFiniteTraceNearestDecoder state) := by
  unfold nearestDecodedLaw augmentedEstimateLaw
  rw [Measure.map_comp _ _
    (orientedFiniteTraceNearestDecoder_measurable state hstate)]
  rfl

/-- The estimator sees only the ordinary measurement record. -/
def estimateLawKernel
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment]
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator] :
    Kernel (DensityOperator (Fin D)) (DensityOperator (Fin D)) :=
  estimator ∘ₖ experiment

instance estimateLawKernel_markov
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment]
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator] :
    IsMarkovKernel (estimateLawKernel experiment estimator) := by
  unfold estimateLawKernel
  infer_instance

/-- Expected trace-norm loss for the same fixed state used in the tail event. -/
def expectedTraceLoss
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment]
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (rho : DensityOperator (Fin D)) : ENNReal :=
  ∫⁻ estimate, hermitianTraceLoss rho estimate ∂estimateLawKernel experiment estimator rho

/-- Disintegrate an arbitrary nonnegative measurable loss on the genie output;
the estimator still receives only its ordinary physical data. -/
theorem lintegral_genie_eq (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (mu : Measure Orientation) [IsProbabilityMeasure mu]
    (state : Orientation → DensityOperator (Fin D)) (hs : Measurable state)
    (g : Orientation × DensityOperator (Fin D) → ENNReal) (hg : Measurable g) :
    (∫⁻ p, g p ∂augmentedEstimateLaw experiment estimator mu state hs) =
      ∫⁻ w, ∫⁻ estimate, g (w, estimate)
        ∂estimateLawKernel experiment estimator (state w) ∂mu := by
  have hinner (p : Orientation × Record) :
      (∫⁻ q, g q ∂augmentedEstimateKernel (Orientation := Orientation) estimator p) =
        ∫⁻ estimate, g (p.1, estimate) ∂estimator p.2 := by
    rw [augmentedEstimateKernel, Kernel.lintegral_deterministic_prod
      measurable_fst (Kernel.prodMkLeft Orientation estimator) p hg]
    rfl
  have hfull : Measurable (fun q : (Orientation × Record) × DensityOperator (Fin D) =>
      g (q.1.1, q.2)) := hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hintermediate : Measurable (fun p : Orientation × Record =>
      ∫⁻ estimate, g (p.1, estimate) ∂estimator p.2) := by
    simpa only [Kernel.lintegral_prodMkLeft] using
      hfull.lintegral_kernel_prod_right' (κ := Kernel.prodMkLeft Orientation estimator)
  unfold augmentedEstimateLaw
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hg.aemeasurable]
  simp_rw [hinner]
  rw [Measure.lintegral_compProd hintermediate]
  apply lintegral_congr
  intro w
  unfold estimateLawKernel
  have hgw : Measurable (fun estimate : DensityOperator (Fin D) => g (w, estimate)) :=
    hg.comp (measurable_const.prodMk measurable_id)
  exact (Kernel.lintegral_comp estimator experiment (state w) hgw).symm

/-- The probability of exceeding a specified physical trace-loss threshold. -/
def tailProbability (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (radius : ℝ) (rho : DensityOperator (Fin D)) : ENNReal :=
  estimateLawKernel experiment estimator rho
    {estimate | ENNReal.ofReal radius ≤ hermitianTraceLoss rho estimate}

/-- The tail probability of a Haar mixture is the average of its statewise
probabilities; this keeps the fixed-state quantifier separate from expected risk. -/
theorem augmented_tail_eq (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (mu : Measure Orientation) [IsProbabilityMeasure mu]
    (state : Orientation → DensityOperator (Fin D)) (hs : Measurable state)
    (radius : ℝ) :
    augmentedEstimateLaw experiment estimator mu state hs
      {p | ENNReal.ofReal radius ≤ hermitianTraceLoss (state p.1) p.2} =
      ∫⁻ w, tailProbability experiment estimator radius (state w) ∂mu := by
  let event : Set (Orientation × DensityOperator (Fin D)) :=
    {p | ENNReal.ofReal radius ≤ hermitianTraceLoss (state p.1) p.2}
  have hf : Measurable (fun p : Orientation × DensityOperator (Fin D) => (state p.1, p.2)) :=
    (hs.comp measurable_fst).prodMk measurable_snd
  have hloss : Measurable (fun p : Orientation × DensityOperator (Fin D) =>
      hermitianTraceLoss (state p.1) p.2) := by
    simpa only [Function.comp_def] using (hermitianTraceLoss_pair_measurable (D := D)).comp hf
  have hevent : MeasurableSet event := measurableSet_le measurable_const hloss
  rw [← lintegral_indicator_one hevent]
  have hind : Measurable (event.indicator (1 : (Orientation × DensityOperator (Fin D)) → ENNReal)) :=
    measurable_const.indicator hevent
  rw [lintegral_genie_eq experiment estimator mu state hs (event.indicator 1) hind]
  apply lintegral_congr
  intro w
  change (∫⁻ estimate, ({estimate | ENNReal.ofReal radius ≤
      hermitianTraceLoss (state w) estimate} : Set _).indicator 1 estimate
      ∂estimateLawKernel experiment estimator (state w)) = _
  rw [lintegral_indicator_one]
  · rfl
  · have hfsection : Measurable (fun estimate : DensityOperator (Fin D) => (w, estimate)) :=
      measurable_const.prodMk measurable_id
    have hsection : Measurable (fun estimate : DensityOperator (Fin D) =>
        hermitianTraceLoss (state w) estimate) := by
      simpa only [Function.comp_def] using hloss.comp hfsection
    exact measurableSet_le measurable_const hsection

/-- A tail event at radius r forces expected trace loss at least r times
its probability, for this same state and estimator. -/
theorem radius_mul_tail_le_expected (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment] (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (radius : ℝ) (rho : DensityOperator (Fin D)) :
    ENNReal.ofReal radius * tailProbability experiment estimator radius rho ≤
      expectedTraceLoss experiment estimator rho := by
  classical
  let event : Set (DensityOperator (Fin D)) :=
    {estimate | ENNReal.ofReal radius ≤ hermitianTraceLoss rho estimate}
  have hf : Measurable (fun estimate : DensityOperator (Fin D) => (rho, estimate)) :=
    measurable_const.prodMk measurable_id
  have hloss : Measurable (hermitianTraceLoss rho) := by
    simpa only [Function.comp_def] using (hermitianTraceLoss_pair_measurable (D := D)).comp hf
  have hevent : MeasurableSet event := measurableSet_le measurable_const hloss
  rw [tailProbability, ← lintegral_indicator_const hevent]
  apply lintegral_mono
  intro estimate
  by_cases he : estimate ∈ event
  · rw [Set.indicator_of_mem he]
    exact he
  · rw [Set.indicator_of_notMem he]
    exact bot_le

/-- Geometry and averaging: a Fano error bound for the nearest-state
rule yields one fixed packing label and orientation with both lower bounds. -/
theorem fixed_pair_probability_and_expectation
    (experiment : Kernel (DensityOperator (Fin D)) Record) [IsMarkovKernel experiment]
    (estimator : Kernel Record (DensityOperator (Fin D))) [IsMarkovKernel estimator]
    (mu : Measure Orientation) [IsProbabilityMeasure mu]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ x, Measurable (state x))
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hseparated : ∀ w x y, x ≠ y →
      2 * radius ≤ realHermitianTraceLoss (state x w) (state y w))
    (hfano : (11 : ℝ) / 16 ≤
      labelError (nearestDecodedLaw experiment estimator mu state hstate)) :
    ∃ x w,
      (11 / 16 : ENNReal) ≤ tailProbability experiment estimator radius (state x w) ∧
      ENNReal.ofReal (11 * radius / 16) ≤
        expectedTraceLoss experiment estimator (state x w) := by
  classical
  let kappa := nearestDecodedLaw experiment estimator mu state hstate
  let J := FiniteUniformJoint.ofMarkovKernel kappa
  have hfano' : (11 : ℝ) / 16 ≤ (J.toPosteriorExperiment id).errorProbability := by
    simpa [J, labelError, FiniteUniformJoint.ofMarkovKernel_errorProbability_id_eq] using hfano
  have hcfin : (11 / 16 : ENNReal) ≠ ∞ := ENNReal.div_ne_top (by norm_num) (by norm_num)
  have hex : ∃ x w, (11 / 16 : ENNReal) ≤ tailProbability experiment estimator radius (state x w) := by
    by_contra hnone
    push Not at hnone
    have hpoint (a : Fin N) : kappa a {y | y ≠ a} < (11 / 16 : ENNReal) := by
      let event : Set (Orientation × DensityOperator (Fin D)) :=
        {p | orientedFiniteTraceNearestDecoder state p ≠ a}
      have hdecode := orientedFiniteTraceNearestDecoder_measurable state hstate
      have hwrong : {y : Fin N | y ≠ a} = ({a} : Set (Fin N))ᶜ := by
        ext y
        simp [eq_comm]
      have hmap : kappa a {y | y ≠ a} =
          augmentedEstimateLaw experiment estimator mu (state a) (hstate a) event := by
        dsimp [kappa]
        rw [nearestDecodedLaw_apply_eq_map_genieEstimate, hwrong,
          Measure.map_apply hdecode (measurableSet_singleton a).compl]
        rfl
      have hsubset : event ⊆ {p | ENNReal.ofReal radius ≤ hermitianTraceLoss (state a p.1) p.2} := by
        intro p hp
        change orientedFiniteTraceNearestDecoder state p ≠ a at hp
        rw [orientedFiniteTraceNearestDecoder_eq] at hp
        exact ofReal_radius_le_hermitianTraceLoss_of_finiteTraceNearestDecoder_ne
          (fun b => state b p.1) radius (hseparated p.1) a p.2 hp
      calc
        _ ≤ augmentedEstimateLaw experiment estimator mu (state a) (hstate a)
            {p | ENNReal.ofReal radius ≤ hermitianTraceLoss (state a p.1) p.2} := by
          rw [hmap]
          exact measure_mono hsubset
        _ = ∫⁻ w, tailProbability experiment estimator radius (state a w) ∂mu :=
          augmented_tail_eq experiment estimator mu (state a) (hstate a) radius
        _ < ∫⁻ _w, (11 / 16 : ENNReal) ∂mu := by
          apply lintegral_strict_mono (by exact MeasureTheory.IsProbabilityMeasure.ne_zero mu)
            measurable_const.aemeasurable
          · apply ne_top_of_le_ne_top (by simpa using hcfin : (∫⁻ _w, (11 / 16 : ENNReal) ∂mu) ≠ ∞)
            exact lintegral_mono (fun w => (hnone a w).le)
          · exact Filter.Eventually.of_forall (fun w => hnone a w)
        _ = 11 / 16 := by simp
    have herror : ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) <
        (11 / 16 : ENNReal) := by
      rw [show ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) =
          (N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a} from
        ofReal_ofMarkovKernel_errorProbability_id_eq kappa]
      calc
        _ < (N : ENNReal)⁻¹ * ∑ _a : Fin N, (11 / 16 : ENNReal) :=
          ENNReal.mul_lt_mul_right (by simp) (by simpa using (NeZero.ne N))
            (ENNReal.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun a _ => hpoint a))
        _ = (N : ENNReal)⁻¹ * ((N : ENNReal) * (11 / 16 : ENNReal)) := by
          simp [nsmul_eq_mul]
        _ = 11 / 16 := ENNReal.inv_mul_cancel_left (by exact_mod_cast (NeZero.ne N)) (by simp)
    have hbad := (ENNReal.ofReal_le_ofReal hfano').trans_lt herror
    have hbadr := (ENNReal.toReal_lt_toReal (by simp) hcfin).mpr hbad
    norm_num at hbadr

  obtain ⟨x, w, hp⟩ := hex
  refine ⟨x, w, hp, ?_⟩
  have hconst : ENNReal.ofReal ((11 : ℝ) / 16) = (11 / 16 : ENNReal) := by
    apply (ENNReal.toReal_eq_toReal_iff' (by simp) hcfin).mp
    norm_num
  calc
    _ = ENNReal.ofReal radius * (11 / 16 : ENNReal) := by
      rw [show 11 * radius / 16 = radius * ((11 : ℝ) / 16) by ring,
        ENNReal.ofReal_mul hradius, hconst]
    _ ≤ ENNReal.ofReal radius * tailProbability experiment estimator radius (state x w) :=
      mul_le_mul' le_rfl hp
    _ ≤ _ := radius_mul_tail_le_expected experiment estimator radius (state x w)

end GeneralGeometry

section PhysicalApplication
variable {k m T N : ℕ} [NeZero N]
    {Seed Outcome : Type*}
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- Equations (fixed-hard-state-probability) and (fixed-hard-state-expectation)
from Lemmas 12--13 and the actual Grassmann packing separation. The same
fixed pair occurs in both conclusions, and the estimator has no rotation input. -/
theorem fixed_state_bounds_from_lemma13
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin (k + 2))))
    [IsMarkovKernel estimator]
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b alpha L : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hbclass : b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha))
    (hN : 2 ≤ N)
    (hseparated : ∀ x y, x ≠ y →
      (m : ℝ) / 2 ≤ projectorHermitianTraceDistance (P x) (P y))
    (hinformation : (T : ℝ) * (8 * b ^ 2 / (3 * (m : ℝ))) ≤ Real.log N / 16)
    (hlog : 4 * Real.log 2 ≤ Real.log N) :
    ∃ (x : Fin N) (w : Rotation k),
      let rho := orientedHardProjectorDensityOperator w (P x) b hm hb.le hbquarter
      rho ∈ spectralDecayClass (k + 2) alpha L ∧
      (11 / 16 : ENNReal) ≤ tailProbability design.experimentKernel estimator (b / 4) rho ∧
      ENNReal.ofReal (11 * b / 64) ≤ expectedTraceLoss design.experimentKernel estimator rho := by
  let state := fun x U => orientedHardProjectorDensityOperator U (P x) b hm hb.le hbquarter
  have hstate : ∀ x, Measurable (state x) :=
    fun x => measurable_orientedHardProjectorDensityOperator (P x) b hm hb.le hbquarter
  have hsep : ∀ w x y, x ≠ y →
      2 * (b / 4) ≤ realHermitianTraceLoss (state x w) (state y w) := by
    intro w x y hxy
    have h := orientedHardProjectorDensityOperator_traceDistance_ge_half_mass
      w (P y) (P x) b hm hb.le hbquarter (hseparated y x hxy.symm)
    simpa only [state, realHermitianTraceLoss,
      show 2 * (b / 4) = b / 2 by ring] using h
  have hfano : (11 : ℝ) / 16 ≤
      labelError (nearestDecodedLaw design.experimentKernel estimator
        (unitaryHaarProbability (k + 2)) state hstate) := by
    exact lemma13_eleven_sixteenths design P b hm hk hb hbquarter hN hinformation hlog
      (nearestDecodeKernel estimator state hstate)
  obtain ⟨x, w, htail, hexpected⟩ := fixed_pair_probability_and_expectation
    design.experimentKernel estimator (unitaryHaarProbability (k + 2))
    state hstate (b / 4) (by positivity) hsep hfano
  refine ⟨x, w, ?_, htail, ?_⟩
  · exact orientedHardProjectorDensityOperator_mem_spectralDecayClass
      w (P x) alpha L b hm halpha hL hb.le hbquarter hbclass
  · convert hexpected using 1
    congr 1
    ring

/-- The entire main-text application, with exactly the mass restriction
`beta ≤ c_I m sqrt(d_perp/T)` and the packing exponent from Section VI-A.
Neither a Fano inequality nor an information budget is an input here. -/
theorem sectionC_fixed_state_bounds
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin (k + 2))))
    [IsMarkovKernel estimator]
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b alpha L : ℝ)
    (hm : 1 ≤ m) (hD : 514 ≤ k + 2) (hT : 1 ≤ T)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hbclass : b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha))
    (hseparated : ∀ x y, x ≠ y →
      (m : ℝ) / 2 ≤ projectorHermitianTraceDistance (P x) (P y))
    (hpacking : grassmannGamma0 * (m : ℝ) * (k : ℝ) ≤ Real.log N)
    (hbscale : b ≤ lowerInformationConstant * (m : ℝ) * Real.sqrt ((k : ℝ) / T)) :
    ∃ (x : Fin N) (w : Rotation k),
      let rho := orientedHardProjectorDensityOperator w (P x) b hm hb.le hbquarter
      rho ∈ spectralDecayClass (k + 2) alpha L ∧
      (11 / 16 : ENNReal) ≤ tailProbability design.experimentKernel estimator (b / 4) rho ∧
      ENNReal.ofReal (11 * b / 64) ≤ expectedTraceLoss design.experimentKernel estimator rho := by
  have hlog : 4 * Real.log 2 ≤ Real.log (N : ℝ) := by
    exact (four_log_two_le_grassmann_exponent (k + 2) m hD hm).trans
      (by simpa [lowerAmbientDimension] using hpacking)
  have hN : 2 ≤ N := by
    have hlogpos : 0 < Real.log (N : ℝ) :=
      (mul_pos (by norm_num) (Real.log_pos (by norm_num))).trans_le hlog
    have hcardone : 1 < (N : ℝ) := (Real.log_pos_iff (by positivity)).mp hlogpos
    exact_mod_cast hcardone
  apply fixed_state_bounds_from_lemma13 design estimator P b alpha L hm (by omega)
    hb hbquarter halpha hL hbclass hN hseparated _ hlog
  exact informationRadius_le_logCardinality_div_sixteen (m : ℝ) (k : ℝ) (T : ℝ) b
    (Real.log N) (by exact_mod_cast hm) (by exact_mod_cast (show 0 < k by omega))
    (by exact_mod_cast hT) hb.le hbscale hpacking

end PhysicalApplication
end
end TomographyOracleCore.Revision.NonadaptiveFano
