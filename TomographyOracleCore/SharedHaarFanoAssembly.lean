import TomographyOracleCore.SharedHaarTensorization
import TomographyOracleCore.PhysicalNearestDecoder
import TomographyOracleCore.PhysicalLowerDecision
import TomographyOracleCore.FiniteKLFormula

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

/-!
# Shared-Haar Fano assembly

This module keeps the common orientation in a genie-aided transcript while
the estimator itself sees only the public seed and outcomes.  It supplies
the two measure-theoretic interfaces that the finite Fano theorem needs:

* a support-aware finite information-radius inequality, so the decoded
  reference law need not charge labels that are never output; and
* a measurable orientation-dependent nearest-state decoder.

The final physical theorem uses only one-copy shared-orientation KL bounds,
hard-family membership and separation, and the two scalar cardinality
inequalities used by the proved finite Fano theorem.
-/

section FiniteSupportInformationRadius

variable {Y : Type*} [Fintype Y] [MeasurableSpace Y]
  [MeasurableSingletonClass Y]

/-- Atomwise Radon--Nikodym formula assuming absolute continuity explicitly.
Unlike the positive-reference version, this needs positivity only at the
single atom under consideration. -/
theorem toReal_rnDeriv_eq_measureReal_singleton_div_of_ac
    (mu nu : Measure Y) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hac : mu ≪ nu) (y : Y) (hnu : 0 < nu.real {y}) :
    (mu.rnDeriv nu y).toReal = mu.real {y} / nu.real {y} := by
  have hmass : mu.rnDeriv nu y * nu {y} = mu {y} := by
    simpa only [lintegral_singleton] using
      (Measure.setLIntegral_rnDeriv' (μ := mu) (ν := nu) hac
        (measurableSet_singleton y))
  have hmassReal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hmassReal
  exact (eq_div_iff (ne_of_gt hnu)).2 hmassReal

/-- Finite-alphabet KL formula with zero reference atoms allowed.  Absolute
continuity makes every corresponding target contribution vanish. -/
theorem toReal_klDiv_eq_sum_measureReal_mul_log_div_of_ac
    (mu nu : Measure Y) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (hac : mu ≪ nu) :
    (klDiv mu nu).toReal =
      ∑ y, mu.real {y} * Real.log (mu.real {y} / nu.real {y}) := by
  have hint : Integrable (llr mu nu) mu := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ := mu) (f := llr mu nu)
        Set.finite_univ)
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_fintype hint]
  apply Finset.sum_congr rfl
  intro y _hy
  change mu.real {y} • Real.log (mu.rnDeriv nu y).toReal = _
  by_cases hnu0 : nu.real {y} = 0
  · have hnumeasure : nu {y} = 0 := by
      rw [measureReal_def] at hnu0
      exact ((ENNReal.toReal_eq_zero_iff _).mp hnu0).resolve_right
        (measure_ne_top nu {y})
    have hmumeasure : mu {y} = 0 := hac hnumeasure
    have hmureal : mu.real {y} = 0 := by
      simp [measureReal_def, hmumeasure]
    simp [hmureal]
  · have hnupos : 0 < nu.real {y} :=
      lt_of_le_of_ne measureReal_nonneg (Ne.symm hnu0)
    rw [toReal_rnDeriv_eq_measureReal_singleton_div_of_ac
      mu nu hac y hnupos]
    simp only [smul_eq_mul]

namespace FiniteUniformJoint

variable {Label Observation : Type*}
  [Fintype Label] [Nonempty Label] [Fintype Observation]

/-- Gibbs' inequality when the reference vector is only nonnegative.
The support hypothesis is exactly the one forced by absolute continuity. -/
theorem finiteReferenceInformation_nonnegative_of_support
    (p q : Observation → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 ≤ q y)
    (hsupport : ∀ y, q y = 0 → p y = 0)
    (hpsum : ∑ y, p y = 1) (hqsum : ∑ y, q y = 1) :
    0 ≤ ∑ y, p y * Real.log (p y / q y) := by
  have hpoint (y : Observation) :
      p y - q y ≤ p y * Real.log (p y / q y) := by
    by_cases hqzero : q y = 0
    · simp [hqzero, hsupport y hqzero]
    have hqpos : 0 < q y := lt_of_le_of_ne (hq y) (Ne.symm hqzero)
    by_cases hpzero : p y = 0
    · simp [hpzero, hqpos.le]
    · have hppos : 0 < p y := lt_of_le_of_ne (hp y) (Ne.symm hpzero)
      have hlog := Real.log_le_sub_one_of_pos (div_pos hqpos hppos)
      have hmul :
          p y * Real.log (q y / p y) ≤ p y * (q y / p y - 1) :=
        mul_le_mul_of_nonneg_left hlog hppos.le
      have hright : p y * (q y / p y - 1) = q y - p y := by
        field_simp [hpzero]
      have hlogneg :
          Real.log (p y / q y) = -Real.log (q y / p y) := by
        rw [Real.log_div hpzero (ne_of_gt hqpos),
          Real.log_div (ne_of_gt hqpos) hpzero]
        ring
      rw [hright] at hmul
      rw [hlogneg]
      linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Observation))
    fun y _hy ↦ hpoint y
  rw [Finset.sum_sub_distrib, hpsum, hqsum, sub_self] at hsum
  exact hsum

/-- Pointwise information-radius factorization on the support of a
nonnegative reference vector. -/
theorem joint_log_reference_factorization_of_support
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) (hq : ∀ y, 0 ≤ q y)
    (hsupport : ∀ y, q y = 0 → J.observationWeight y = 0)
    (y : Observation) (a : Label) :
    J.joint a y *
        Real.log (((Fintype.card Label : ℝ) * J.joint a y) / q y) =
      J.joint a y *
          Real.log ((Fintype.card Label : ℝ) * J.posterior y a) +
        J.joint a y *
          Real.log (J.observationWeight y / q y) := by
  have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hqzero : q y = 0
  · have hweight : J.observationWeight y = 0 := hsupport y hqzero
    have hle : J.joint a y ≤ J.observationWeight y := by
      unfold observationWeight
      exact Finset.single_le_sum
        (fun b _hb ↦ J.joint_nonneg b y) (Finset.mem_univ a)
    have hjoint : J.joint a y = 0 :=
      le_antisymm (by simpa [hweight] using hle) (J.joint_nonneg a y)
    simp [hjoint]
  have hqpos : 0 < q y := lt_of_le_of_ne (hq y) (Ne.symm hqzero)
  by_cases hjoint : J.joint a y = 0
  · simp [hjoint]
  have hweight : J.observationWeight y ≠ 0 := by
    intro hzero
    have hle : J.joint a y ≤ J.observationWeight y := by
      unfold observationWeight
      exact Finset.single_le_sum
        (fun b _hb ↦ J.joint_nonneg b y) (Finset.mem_univ a)
    rw [hzero] at hle
    exact hjoint (le_antisymm hle (J.joint_nonneg a y))
  rw [posterior, if_neg hweight]
  rw [Real.log_div (mul_ne_zero hcard hjoint) hqzero,
    Real.log_mul hcard hjoint,
    Real.log_mul hcard (div_ne_zero hjoint hweight),
    Real.log_div hjoint hweight,
    Real.log_div hweight hqzero]
  ring

/-- Support-aware information-radius decomposition. -/
theorem referenceInformation_eq_posteriorKLSum_add_marginal_of_support
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) (hq : ∀ y, 0 ≤ q y)
    (hsupport : ∀ y, q y = 0 → J.observationWeight y = 0) :
    J.referenceInformation q =
      J.posteriorKLSum + J.marginalReferenceInformation q := by
  unfold referenceInformation posteriorKLSum marginalReferenceInformation
  simp_rw [J.joint_log_reference_factorization_of_support q hq hsupport]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  rw [← Finset.sum_mul]
  rfl

/-- Information-radius inequality without a full-support assumption. -/
theorem posteriorKLSum_le_referenceInformation_of_support
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) (hq : ∀ y, 0 ≤ q y)
    (hsupport : ∀ y, q y = 0 → J.observationWeight y = 0)
    (hqsum : ∑ y, q y = 1) :
    J.posteriorKLSum ≤ J.referenceInformation q := by
  have hmarginal : 0 ≤ J.marginalReferenceInformation q := by
    exact finiteReferenceInformation_nonnegative_of_support
      J.observationWeight q J.observationWeight_nonneg hq hsupport
        J.observationWeight_sum_one hqsum
  rw [J.referenceInformation_eq_posteriorKLSum_add_marginal_of_support
    q hq hsupport]
  linarith

/-- A finite-output reference measure controls the posterior information
even when some of its atoms have zero mass. -/
theorem ofMarkovKernel_posteriorKLSum_le_klDiv_reference
    [MeasurableSpace Label]
    [MeasurableSpace Observation] [MeasurableSingletonClass Observation]
    (kappa : Kernel Label Observation) [IsMarkovKernel kappa]
    (reference : Measure Observation) [IsProbabilityMeasure reference]
    (information : ℝ)
    (hfinite : ∀ a, klDiv (kappa a) reference ≠ ∞)
    (hlabel : ∀ a, (klDiv (kappa a) reference).toReal ≤ information) :
    (ofMarkovKernel kappa).posteriorKLSum ≤ information := by
  let q : Observation → ℝ := fun y ↦ reference.real {y}
  have hac (a : Label) : kappa a ≪ reference :=
    (klDiv_ne_top_iff.mp (hfinite a)).1
  have hq : ∀ y, 0 ≤ q y := fun _ ↦ measureReal_nonneg
  have hqsum : ∑ y, q y = 1 := by
    simpa [q] using
      (sum_measureReal_singleton
        (μ := reference) (Finset.univ : Finset Observation))
  have hzero (a : Label) (y : Observation) (hy : q y = 0) :
      (kappa a).real {y} = 0 := by
    have hrefMeasure : reference {y} = 0 := by
      change reference.real {y} = 0 at hy
      rw [measureReal_def] at hy
      exact ((ENNReal.toReal_eq_zero_iff _).mp hy).resolve_right
        (measure_ne_top reference {y})
    have hkMeasure : kappa a {y} = 0 := hac a hrefMeasure
    simp [measureReal_def, hkMeasure]
  have hsupport : ∀ y, q y = 0 →
      (ofMarkovKernel kappa).observationWeight y = 0 := by
    intro y hy
    unfold observationWeight
    simp only [ofMarkovKernel_joint]
    simp [hzero _ y hy]
  calc
    (ofMarkovKernel kappa).posteriorKLSum ≤
        (ofMarkovKernel kappa).referenceInformation q :=
      posteriorKLSum_le_referenceInformation_of_support
        _ q hq hsupport hqsum
    _ = (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, ∑ y, (kappa a).real {y} *
          Real.log ((kappa a).real {y} / q y) :=
      ofMarkovKernel_referenceInformation_eq kappa q
    _ = (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, (klDiv (kappa a) reference).toReal := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [toReal_klDiv_eq_sum_measureReal_mul_log_div_of_ac
        (kappa a) reference (hac a)]
    _ ≤ (Fintype.card Label : ℝ)⁻¹ * ∑ _a : Label, information := by
      gcongr with a
      exact hlabel a
    _ = information := by
      have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp [nsmul_eq_mul, hcard]

end FiniteUniformJoint

end FiniteSupportInformationRadius

namespace PhysicalRisk

/-! ## Joint nearest-decoder measurability -/

/-- The physical trace loss is jointly measurable in the true and estimated
states.  Separate continuity in the first variable and measurable continuity
in the second are sufficient in the second-countable state space. -/
theorem realHermitianTraceLoss_pair_measurable {D : ℕ} :
    Measurable (fun p : DensityOperator (Fin D) × DensityOperator (Fin D) ↦
      realHermitianTraceLoss p.1 p.2) := by
  letI : SecondCountableTopology (DensityOperator (Fin D)) :=
    (show Isometry
      (DensityOperator.matrix :
        DensityOperator (Fin D) → Matrix (Fin D) (Fin D) ℂ) from
      fun _ _ ↦ rfl).isEmbedding.secondCountableTopology
  apply measurable_uncurry_of_continuous_of_measurable
      (u := fun ρ estimate ↦ realHermitianTraceLoss ρ estimate)
  · intro estimate
    have h := realHermitianTraceLoss_continuous estimate
    simpa only [realHermitianTraceLoss_symm] using h
  · exact realHermitianTraceLoss_measurable

/-- Joint measurability of the `ENNReal` physical trace loss. -/
theorem hermitianTraceLoss_pair_measurable {D : ℕ} :
    Measurable (fun p : DensityOperator (Fin D) × DensityOperator (Fin D) ↦
      hermitianTraceLoss p.1 p.2) := by
  change Measurable
    (ENNReal.ofReal ∘ fun p : DensityOperator (Fin D) ×
      DensityOperator (Fin D) ↦ realHermitianTraceLoss p.1 p.2)
  exact ENNReal.measurable_ofReal.comp
    (realHermitianTraceLoss_pair_measurable (D := D))

/-- Trace-distance score for a hard state that varies with a common
orientation.  Naming this map keeps the finite argmin proof compact. -/
noncomputable def orientedTraceScore
    {D N : ℕ} [NeZero N]
    {Orientation : Type*} [MeasurableSpace Orientation]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (a : Fin N) (p : Orientation × DensityOperator (Fin D)) : ℝ :=
  realHermitianTraceLoss (state a p.1) p.2

theorem orientedTraceScore_measurable
    {D N : ℕ} [NeZero N]
    {Orientation : Type*} [MeasurableSpace Orientation]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) (a : Fin N) :
    Measurable (orientedTraceScore state a) := by
  change Measurable
    ((fun q : DensityOperator (Fin D) × DensityOperator (Fin D) ↦
        realHermitianTraceLoss q.1 q.2) ∘
      (fun p : Orientation × DensityOperator (Fin D) ↦
        (state a p.1, p.2)))
  apply @Measurable.comp
  · exact realHermitianTraceLoss_pair_measurable
  · exact ((hstate a).comp measurable_fst).prodMk measurable_snd

/-- Tie-broken nearest label when the finite hard family depends on the
orientation carried by the genie transcript. -/
noncomputable def orientedFiniteTraceNearestDecoder
    {D N : ℕ} [NeZero N]
    {Orientation : Type*} [MeasurableSpace Orientation]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (p : Orientation × DensityOperator (Fin D)) : Fin N :=
  finiteLeastArgmin (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
    (fun a ↦ orientedTraceScore state a p)

set_option maxHeartbeats 800000 in
/-- The orientation-dependent nearest-state decoder is measurable. -/
theorem orientedFiniteTraceNearestDecoder_measurable
    {D N : ℕ} [NeZero N]
    {Orientation : Type*} [MeasurableSpace Orientation]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    Measurable (orientedFiniteTraceNearestDecoder state) := by
  apply measurable_to_countable'
  intro a
  change MeasurableSet {p |
    finiteLeastArgmin (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
      (fun b ↦ orientedTraceScore state b p) = a}
  exact finiteLeastArgmin_fiber_measurable
    (Finset.univ : Finset (Fin N)) Finset.univ_nonempty
    (orientedTraceScore state)
    (fun b _hb ↦ orientedTraceScore_measurable state hstate b)
    (Finset.mem_univ a)

@[simp]
theorem orientedFiniteTraceNearestDecoder_eq
    {D N : ℕ} [NeZero N]
    {Orientation : Type*} [MeasurableSpace Orientation]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (p : Orientation × DensityOperator (Fin D)) :
    orientedFiniteTraceNearestDecoder state p =
      finiteTraceNearestDecoder (fun a ↦ state a p.1) p.2 :=
  rfl

end PhysicalRisk

namespace PhysicalPOVM.RandomizedNonadaptiveDesign

section AssociatedSharedOrientation

variable {D T : ℕ} {Orientation Seed Outcome : Type*}
  [MeasurableSpace Orientation] [StandardBorelSpace Orientation]
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- Reassociate the genie transcript from `((W,seed),outcomes)` to
`(W,(seed,outcomes))`.  The latter is exactly an orientation law followed by
the ordinary physical experiment at the oriented state. -/
theorem map_prodAssoc_sharedOrientation_eq_orientation_compProd_experiment
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    (((orientationLaw.prod design.seed) ⊗ₘ
      sharedOrientationOutcomesKernel design state hstate).map
        (MeasurableEquiv.prodAssoc :
          ((Orientation × Seed) × (Fin T → Outcome)) ≃ᵐ
            (Orientation × (Seed × (Fin T → Outcome))))) =
      orientationLaw ⊗ₘ
        (design.experimentKernel.comap state hstate) := by
  letI : IsProbabilityMeasure design.seed := design.seed_probability
  let seedKernel : Kernel Orientation Seed :=
    Kernel.const Orientation design.seed
  letI : IsMarkovKernel seedKernel := by
    dsimp [seedKernel]
    infer_instance
  have hkernel :
      seedKernel ⊗ₖ sharedOrientationOutcomesKernel design state hstate =
        design.experimentKernel.comap state hstate := by
    apply Kernel.ext
    intro w
    rw [Kernel.compProd_apply_eq_compProd_sectR]
    rw [Kernel.comap_apply]
    rw [experimentKernel_apply_eq_seed_compProd]
    congr 1
  rw [← Measure.compProd_const]
  rw [show Kernel.const Orientation design.seed = seedKernel by rfl]
  rw [Measure.compProd_assoc', hkernel]

/-- Exact KL tensorization after the transcript has been reassociated to
the orientation followed by the ordinary physical data. -/
theorem orientationCompProdExperiment_klDiv_eq_sum
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state reference : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (hreference : Measurable reference) :
    klDiv
        (orientationLaw ⊗ₘ
          (design.experimentKernel.comap state hstate))
        (orientationLaw ⊗ₘ
          (design.experimentKernel.comap reference hreference)) =
      ∑ t, klDiv
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design state hstate t)
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design reference hreference t) := by
  letI : IsProbabilityMeasure design.seed := design.seed_probability
  rw [← map_prodAssoc_sharedOrientation_eq_orientation_compProd_experiment
      design orientationLaw state hstate,
    ← map_prodAssoc_sharedOrientation_eq_orientation_compProd_experiment
      design orientationLaw reference hreference]
  rw [klDiv_map_measurableEquiv]
  exact sharedOrientation_klDiv_eq_sum
    design orientationLaw state reference hstate hreference

end AssociatedSharedOrientation

end PhysicalPOVM.RandomizedNonadaptiveDesign

namespace PhysicalRisk

section GenieExperiment

variable {D T N : ℕ} [NeZero N]
  {Orientation : Type*} [MeasurableSpace Orientation]
  [StandardBorelSpace Orientation]

/-- Run the physical estimator on `(seed,outcomes)` while copying the genie
orientation unchanged into its output. -/
noncomputable def genieEstimateKernel
    (estimator : Estimator D T) :
    Kernel (Orientation × Data T)
      (Orientation × DensityOperator (Fin D)) :=
  (Kernel.deterministic (fun p : Orientation × Data T ↦ p.1)
      measurable_fst) ×ₖ
    Kernel.prodMkLeft Orientation estimator.kernel

instance genieEstimateKernel_isMarkov
    (estimator : Estimator D T) :
    IsMarkovKernel (genieEstimateKernel
      (Orientation := Orientation) estimator) := by
  unfold genieEstimateKernel
  infer_instance

/-- The genie estimator followed by the measurable orientation-dependent
nearest-state decoder. -/
noncomputable def genieDecodedKernel
    (estimator : Estimator D T)
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    Kernel (Orientation × Data T) (Fin N) :=
  (genieEstimateKernel (Orientation := Orientation) estimator).map
    (orientedFiniteTraceNearestDecoder state)

instance genieDecodedKernel_isMarkov
    (estimator : Estimator D T)
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    IsMarkovKernel (genieDecodedKernel estimator state hstate) := by
  unfold genieDecodedKernel
  exact Kernel.IsMarkovKernel.map _
    (orientedFiniteTraceNearestDecoder_measurable state hstate)

/-- The finite Markov experiment obtained by drawing one common orientation,
running the physical experiment at the corresponding hard state, estimating,
and decoding with access to that orientation. -/
noncomputable def sharedHaarDecodedLabelKernel
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    Kernel (Fin N) (Fin N) where
  toFun a :=
    (genieDecodedKernel estimator state hstate) ∘ₘ
      (orientationLaw ⊗ₘ
        (design.experimentKernel.comap (state a) (hstate a)))
  measurable' := Measurable.of_discrete

instance sharedHaarDecodedLabelKernel_isMarkov
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a)) :
    IsMarkovKernel
      (sharedHaarDecodedLabelKernel design estimator orientationLaw
        state hstate) := by
  constructor
  intro a
  change IsProbabilityMeasure
    ((genieDecodedKernel estimator state hstate) ∘ₘ
      (orientationLaw ⊗ₘ
        (design.experimentKernel.comap (state a) (hstate a))))
  infer_instance

/-- The decoded reference measure for the same genie estimator and decoder. -/
noncomputable def sharedHaarDecodedReference
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (reference : Orientation → DensityOperator (Fin D))
    (hreference : Measurable reference) : Measure (Fin N) :=
  (genieDecodedKernel estimator state hstate) ∘ₘ
    (orientationLaw ⊗ₘ
      (design.experimentKernel.comap reference hreference))

instance sharedHaarDecodedReference_isProbability
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (reference : Orientation → DensityOperator (Fin D))
    (hreference : Measurable reference) :
    IsProbabilityMeasure
      (sharedHaarDecodedReference design estimator orientationLaw
        state hstate reference hreference) := by
  unfold sharedHaarDecodedReference
  infer_instance

/-- Full-genie analogue of `sharedHaar_referenceKL_informationRadius`.
Its hypotheses are the same genuine one-copy KL bounds; tensorization is
proved by the shared-orientation identity rather than supplied as a premise. -/
theorem genieSharedHaar_referenceKL_informationRadius
    (design : Design D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (reference : Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (hreference : Measurable reference)
    (budget : Fin T → ENNReal)
    (honeCopy : ∀ a t,
      klDiv
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design (state a) (hstate a) t)
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design reference hreference t) ≤ budget t) :
    ∀ a,
      klDiv
          (orientationLaw ⊗ₘ
            (design.experimentKernel.comap (state a) (hstate a)))
          (orientationLaw ⊗ₘ
            (design.experimentKernel.comap reference hreference)) ≤
        ∑ t, budget t := by
  intro a
  rw [RandomizedNonadaptiveDesign.orientationCompProdExperiment_klDiv_eq_sum
    design orientationLaw (state a) reference (hstate a) hreference]
  exact Finset.sum_le_sum fun t _ht ↦ honeCopy a t

/-- Data processing through the physical estimator and W-dependent nearest
decoder turns the one-copy reference bounds into a decoded finite-alphabet
KL radius. -/
theorem sharedHaarDecodedLabelKernel_klDiv_le_budget
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (reference : Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (hreference : Measurable reference)
    (budget : Fin T → ENNReal)
    (honeCopy : ∀ a t,
      klDiv
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design (state a) (hstate a) t)
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design reference hreference t) ≤ budget t) :
    ∀ a,
      klDiv
          (sharedHaarDecodedLabelKernel design estimator orientationLaw
            state hstate a)
          (sharedHaarDecodedReference design estimator orientationLaw
            state hstate reference hreference) ≤
        ∑ t, budget t := by
  intro a
  exact (klDiv_comp_right_le
    (orientationLaw ⊗ₘ
      (design.experimentKernel.comap (state a) (hstate a)))
    (orientationLaw ⊗ₘ
      (design.experimentKernel.comap reference hreference))
    (genieDecodedKernel estimator state hstate)).trans
      (genieSharedHaar_referenceKL_informationRadius
        design orientationLaw state reference hstate hreference
          budget honeCopy a)

/-- Posterior information used by finite Fano, derived solely from the
one-copy shared-Haar KL budget.  Zero decoded-reference atoms are handled by
the support-aware theorem above. -/
theorem sharedHaarDecoded_posteriorKLSum_le_budget_toReal
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (reference : Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (hreference : Measurable reference)
    (budget : Fin T → ENNReal)
    (hbudgetFinite : (∑ t, budget t) ≠ ∞)
    (honeCopy : ∀ a t,
      klDiv
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design (state a) (hstate a) t)
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design reference hreference t) ≤ budget t) :
    (FiniteUniformJoint.ofMarkovKernel
      (sharedHaarDecodedLabelKernel design estimator orientationLaw
        state hstate)).posteriorKLSum ≤
      (∑ t, budget t).toReal := by
  let kappa := sharedHaarDecodedLabelKernel design estimator
    orientationLaw state hstate
  let referenceDecoded := sharedHaarDecodedReference design estimator
    orientationLaw state hstate reference hreference
  have hkl (a : Fin N) :
      klDiv (kappa a) referenceDecoded ≤ ∑ t, budget t := by
    exact sharedHaarDecodedLabelKernel_klDiv_le_budget
      design estimator orientationLaw state reference hstate hreference
        budget honeCopy a
  have hfinite (a : Fin N) : klDiv (kappa a) referenceDecoded ≠ ∞ :=
    ne_top_of_le_ne_top hbudgetFinite (hkl a)
  apply FiniteUniformJoint.ofMarkovKernel_posteriorKLSum_le_klDiv_reference
    kappa referenceDecoded (∑ t, budget t).toReal hfinite
  intro a
  exact ENNReal.toReal_mono hbudgetFinite (hkl a)

noncomputable def sharedHaarGenieEstimateMeasure
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    Measure (Orientation × DensityOperator (Fin D)) :=
  (genieEstimateKernel (Orientation := Orientation) estimator) ∘ₘ
    (orientationLaw ⊗ₘ
      (design.experimentKernel.comap state hstate))

instance sharedHaarGenieEstimateMeasure_isProbability
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    IsProbabilityMeasure
      (sharedHaarGenieEstimateMeasure design estimator orientationLaw
        state hstate) := by
  unfold sharedHaarGenieEstimateMeasure
  infer_instance

theorem sharedHaarDecodedLabelKernel_apply_eq_map_genieEstimate
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (a : Fin N) :
    sharedHaarDecodedLabelKernel design estimator orientationLaw
        state hstate a =
      (sharedHaarGenieEstimateMeasure design estimator orientationLaw
        (state a) (hstate a)).map
          (orientedFiniteTraceNearestDecoder state) := by
  unfold sharedHaarDecodedLabelKernel sharedHaarGenieEstimateMeasure
  rw [Measure.map_comp _ _
    (orientedFiniteTraceNearestDecoder_measurable state hstate)]
  rfl

theorem lintegral_sharedHaarGenieEstimateMeasure_traceLoss_eq
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    (∫⁻ p : Orientation × DensityOperator (Fin D),
        hermitianTraceLoss (state p.1) p.2
      ∂sharedHaarGenieEstimateMeasure design estimator orientationLaw
        state hstate) =
      ∫⁻ w, statewiseExpectedTraceRisk design estimator (state w)
        ∂orientationLaw := by
  let loss : Orientation × DensityOperator (Fin D) → ENNReal :=
    fun p ↦ hermitianTraceLoss (state p.1) p.2
  have hloss : Measurable loss := by
    change Measurable
      ((fun q : DensityOperator (Fin D) × DensityOperator (Fin D) ↦
          hermitianTraceLoss q.1 q.2) ∘
        (fun p : Orientation × DensityOperator (Fin D) ↦
          (state p.1, p.2)))
    apply @Measurable.comp
    · exact hermitianTraceLoss_pair_measurable
    · exact (hstate.comp measurable_fst).prodMk measurable_snd
  have hinner (p : Orientation × Data T) :
      (∫⁻ q, loss q
          ∂genieEstimateKernel (Orientation := Orientation) estimator p) =
        ∫⁻ estimate, hermitianTraceLoss (state p.1) estimate
          ∂estimator.kernel p.2 := by
    rw [genieEstimateKernel, Kernel.lintegral_deterministic_prod
      measurable_fst (Kernel.prodMkLeft Orientation estimator.kernel)
        p hloss]
    rfl
  have hfull : Measurable
      (fun q : (Orientation × Data T) × DensityOperator (Fin D) ↦
        hermitianTraceLoss (state q.1.1) q.2) := by
    change Measurable
      ((fun q : DensityOperator (Fin D) × DensityOperator (Fin D) ↦
          hermitianTraceLoss q.1 q.2) ∘
        (fun q : (Orientation × Data T) × DensityOperator (Fin D) ↦
          (state q.1.1, q.2)))
    apply @Measurable.comp
    · exact hermitianTraceLoss_pair_measurable
    · exact (hstate.comp (measurable_fst.comp measurable_fst)).prodMk measurable_snd
  have hintermediate : Measurable
      (fun p : Orientation × Data T ↦
        ∫⁻ estimate, hermitianTraceLoss (state p.1) estimate
          ∂estimator.kernel p.2) := by
    simpa only [Kernel.lintegral_prodMkLeft] using
      hfull.lintegral_kernel_prod_right'
        (κ := Kernel.prodMkLeft Orientation estimator.kernel)
  unfold sharedHaarGenieEstimateMeasure
  rw [Measure.lintegral_bind (Kernel.aemeasurable _) hloss.aemeasurable]
  simp_rw [hinner]
  rw [Measure.lintegral_compProd hintermediate]
  apply lintegral_congr
  intro w
  unfold statewiseExpectedTraceRisk estimateKernel
  have hw : Measurable (hermitianTraceLoss (state w)) := by
    change Measurable (ENNReal.ofReal ∘ realHermitianTraceLoss (state w))
    exact ENNReal.measurable_ofReal.comp
      (realHermitianTraceLoss_measurable (state w))
  rw [Kernel.lintegral_comp estimator.kernel design.experimentKernel
    (state w) hw]
  rfl

theorem ofReal_radius_mul_sharedHaar_wrongProbability_le_integratedRisk
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (radius : ℝ) (a : Fin N)
    (hforces : ∀ p : Orientation × DensityOperator (Fin D),
      orientedFiniteTraceNearestDecoder state p ≠ a →
        ENNReal.ofReal radius ≤ hermitianTraceLoss (state a p.1) p.2) :
    ENNReal.ofReal radius *
        (sharedHaarDecodedLabelKernel design estimator orientationLaw
          state hstate a) {y | y ≠ a} ≤
      ∫⁻ w, statewiseExpectedTraceRisk design estimator (state a w)
        ∂orientationLaw := by
  let μ := sharedHaarGenieEstimateMeasure design estimator orientationLaw
    (state a) (hstate a)
  let decode := orientedFiniteTraceNearestDecoder state
  let event : Set (Orientation × DensityOperator (Fin D)) :=
    {p | decode p ≠ a}
  let loss : Orientation × DensityOperator (Fin D) → ENNReal :=
    fun p ↦ hermitianTraceLoss (state a p.1) p.2
  have hdecode : Measurable decode :=
    orientedFiniteTraceNearestDecoder_measurable state hstate
  have hevent : MeasurableSet event := by
    change MeasurableSet (decode ⁻¹' ({a} : Set (Fin N))ᶜ)
    exact hdecode ((measurableSet_singleton a).compl)
  have hkappa :
      (sharedHaarDecodedLabelKernel design estimator orientationLaw
        state hstate a) {y | y ≠ a} = μ event := by
    rw [sharedHaarDecodedLabelKernel_apply_eq_map_genieEstimate]
    have hwrong : {y : Fin N | y ≠ a} = ({a} : Set (Fin N))ᶜ := by
      ext y
      simp [eq_comm]
    rw [hwrong, Measure.map_apply hdecode (measurableSet_singleton a).compl]
    rfl
  have hpoint : event.indicator (fun _ ↦ ENNReal.ofReal radius) ≤ loss := by
    intro p
    by_cases hp : p ∈ event
    · rw [Set.indicator_of_mem hp]
      change ENNReal.ofReal radius ≤
        hermitianTraceLoss (state a p.1) p.2
      apply hforces p
      change orientedFiniteTraceNearestDecoder state p ≠ a at hp
      exact hp
    · rw [Set.indicator_of_notMem hp]
      exact bot_le
  calc
    ENNReal.ofReal radius *
        (sharedHaarDecodedLabelKernel design estimator orientationLaw
          state hstate a) {y | y ≠ a} =
      ENNReal.ofReal radius * μ event := by rw [hkappa]
    _ = ∫⁻ p, event.indicator (fun _ ↦ ENNReal.ofReal radius) p ∂μ :=
      (lintegral_indicator_const hevent (ENNReal.ofReal radius)).symm
    _ ≤ ∫⁻ p, loss p ∂μ := lintegral_mono hpoint
    _ = ∫⁻ w, statewiseExpectedTraceRisk design estimator (state a w)
          ∂orientationLaw := by
      exact lintegral_sharedHaarGenieEstimateMeasure_traceLoss_eq
        design estimator orientationLaw (state a) (hstate a)

theorem ofReal_ofMarkovKernel_errorProbability_id_eq
    (kappa : Kernel (Fin N) (Fin N)) [IsMarkovKernel kappa] :
    ENNReal.ofReal
        (((FiniteUniformJoint.ofMarkovKernel kappa).toPosteriorExperiment
          id).errorProbability) =
      (N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a} := by
  rw [FiniteUniformJoint.ofMarkovKernel_errorProbability_id_eq]
  simp only [Fintype.card_fin]
  have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNnat
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hNreal.le)]
  rw [ENNReal.ofReal_inv_of_pos hNreal, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply congrArg ((N : ENNReal)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro a _ha
    rw [measureReal_def, ENNReal.ofReal_toReal]
    exact measure_ne_top _ _
  · intro a _ha
    exact measureReal_nonneg

theorem ofReal_eleven_mul_radius_div_sixteen_le_classWorstCaseRisk_of_sharedHaar
    {alpha L : ℝ}
    (hN : 2 ≤ N)
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (reference : Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (hreference : Measurable reference)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hmembership : ∀ w a,
      state a w ∈ spectralDecayClass D alpha L)
    (hseparated : ∀ w a b, a ≠ b →
      2 * radius ≤ realHermitianTraceLoss (state a w) (state b w))
    (budget : Fin T → ENNReal)
    (hbudgetFinite : (∑ t, budget t) ≠ ∞)
    (honeCopy : ∀ a t,
      klDiv
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design (state a) (hstate a) t)
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design reference hreference t) ≤ budget t)
    (hinformation : (∑ t, budget t).toReal ≤ Real.log N / 16)
    (hlogTwo : 4 * Real.log 2 ≤ Real.log N) :
    ENNReal.ofReal (11 * radius / 16) ≤
      classWorstCaseRisk D T alpha L design estimator := by
  let kappa := sharedHaarDecodedLabelKernel design estimator
    orientationLaw state hstate
  let J := FiniteUniformJoint.ofMarkovKernel kappa
  have hposterior : J.posteriorKLSum ≤ Real.log N / 16 := by
    exact (sharedHaarDecoded_posteriorKLSum_le_budget_toReal
      design estimator orientationLaw state reference hstate hreference
        budget hbudgetFinite honeCopy).trans hinformation
  have hfano : (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment id).errorProbability := by
    apply J.eleven_sixteenths_le_errorProbability_of_posteriorKLSum_proved
    · simpa [Fintype.card_fin] using hN
    · simpa [J, Fintype.card_fin] using hposterior
    · simpa [Fintype.card_fin] using hlogTwo
  have hfanoENN : ENNReal.ofReal ((11 : ℝ) / 16) ≤
      ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) :=
    ENNReal.ofReal_le_ofReal hfano
  let worst := classWorstCaseRisk D T alpha L design estimator
  have hpoint (a : Fin N) :
      ENNReal.ofReal radius * kappa a {y | y ≠ a} ≤ worst := by
    have hforces : ∀ p : Orientation × DensityOperator (Fin D),
        orientedFiniteTraceNearestDecoder state p ≠ a →
          ENNReal.ofReal radius ≤ hermitianTraceLoss (state a p.1) p.2 := by
      intro p hp
      rw [orientedFiniteTraceNearestDecoder_eq] at hp
      exact
        ofReal_radius_le_hermitianTraceLoss_of_finiteTraceNearestDecoder_ne
          (fun b ↦ state b p.1) radius (hseparated p.1) a p.2 hp
    calc
      ENNReal.ofReal radius * kappa a {y | y ≠ a} ≤
          ∫⁻ w, statewiseExpectedTraceRisk design estimator (state a w)
            ∂orientationLaw := by
        exact ofReal_radius_mul_sharedHaar_wrongProbability_le_integratedRisk
          design estimator orientationLaw state hstate radius a hforces
      _ ≤ ∫⁻ _w, worst ∂orientationLaw := by
        apply lintegral_mono
        intro w
        exact statewiseExpectedTraceRisk_le_classWorstCaseRisk
          design estimator (state a w) (hmembership w a)
      _ = worst := by simp
  have hsum :
      ENNReal.ofReal radius * ∑ a, kappa a {y | y ≠ a} ≤
        ∑ _a : Fin N, worst := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ha ↦ hpoint a
  have havgWrong :
      ENNReal.ofReal radius *
          ((N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a}) ≤ worst := by
    have hcard0 : (N : ENNReal) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) hN)
    have hcardtop : (N : ENNReal) ≠ ∞ := by simp
    calc
      ENNReal.ofReal radius *
          ((N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a}) =
        (N : ENNReal)⁻¹ *
          (ENNReal.ofReal radius * ∑ a, kappa a {y | y ≠ a}) := by
            ac_rfl
      _ ≤ (N : ENNReal)⁻¹ * ∑ _a : Fin N, worst :=
        mul_le_mul' le_rfl hsum
      _ = (N : ENNReal)⁻¹ * ((N : ENNReal) * worst) := by
        simp [nsmul_eq_mul]
      _ = worst := ENNReal.inv_mul_cancel_left hcard0 hcardtop
  have herrorENN :
      ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) =
        (N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a} := by
    simpa [J] using
      (ofReal_ofMarkovKernel_errorProbability_id_eq (N := N) kappa)
  calc
    ENNReal.ofReal (11 * radius / 16) =
        ENNReal.ofReal radius * ENNReal.ofReal ((11 : ℝ) / 16) := by
      rw [show 11 * radius / 16 = radius * ((11 : ℝ) / 16) by ring,
        ENNReal.ofReal_mul hradius]
    _ ≤ ENNReal.ofReal radius *
        ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) :=
      mul_le_mul' le_rfl hfanoENN
    _ = ENNReal.ofReal radius *
        ((N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a}) := by
      rw [herrorENN]
    _ ≤ worst := havgWrong

/-- Procedurewise shared-orientation Fano data.  All tensorization and Fano
assembly are conclusions; the statistical input is only the family geometry
and the per-shot one-copy KL budget. -/
noncomputable def ProcedurewiseSharedHaarFanoFamily
    (Orientation : Type*) [MeasurableSpace Orientation]
    [StandardBorelSpace Orientation]
    (D T : ℕ) (alpha L radius : ℝ) : Prop :=
  ∀ (design : Design D T) (estimator : Estimator D T),
    ∃ N : ℕ, ∃ hN : 2 ≤ N,
      ∃ orientationLaw : Measure Orientation,
        IsProbabilityMeasure orientationLaw ∧
        ∃ state : Fin N → Orientation → DensityOperator (Fin D),
          ∃ reference : Orientation → DensityOperator (Fin D),
            ∃ hstate : ∀ a, Measurable (state a),
            ∃ hreference : Measurable reference,
            (∀ w a, state a w ∈ spectralDecayClass D alpha L) ∧
            (∀ w a b, a ≠ b →
              2 * radius ≤
                realHermitianTraceLoss (state a w) (state b w)) ∧
            ∃ budget : Fin T → ENNReal,
              (∑ t, budget t) ≠ ∞ ∧
              (∀ a t,
                klDiv
                    ((orientationLaw.prod design.seed) ⊗ₘ
                      RandomizedNonadaptiveDesign.sharedOrientationShotKernel
                        design (state a) (hstate a) t)
                    ((orientationLaw.prod design.seed) ⊗ₘ
                      RandomizedNonadaptiveDesign.sharedOrientationShotKernel
                        design reference hreference t) ≤ budget t) ∧
              (∑ t, budget t).toReal ≤ Real.log N / 16 ∧
              4 * Real.log 2 ≤ Real.log N

/-- The exact procedurewise shared-Haar lower interface.  The hidden
orientation law, hard family, reference state and one-copy budgets may all
depend on the fixed design-estimator pair, matching the minimax quantifier
order. -/
theorem ofReal_eleven_mul_radius_div_sixteen_le_unrestrictedRisk_of_procedurewiseSharedHaar
    {Orientation : Type*} [MeasurableSpace Orientation]
    [StandardBorelSpace Orientation]
    {D T : ℕ} {alpha L radius : ℝ}
    (hradius : 0 ≤ radius)
    (hfamily : ProcedurewiseSharedHaarFanoFamily
      Orientation D T alpha L radius) :
    ENNReal.ofReal (11 * radius / 16) ≤
      unrestrictedRisk D T alpha L := by
  apply le_unrestrictedRisk_of_forall_design_estimator
  intro design estimator
  rcases hfamily design estimator with
    ⟨N, hN, orientationLaw, hprobability, state, reference,
      hstate, hreference, hmembership, hseparated,
      budget, hbudgetFinite, honeCopy, hinformation, hlogTwo⟩
  letI : NeZero N := ⟨by omega⟩
  letI : IsProbabilityMeasure orientationLaw := hprobability
  exact
    ofReal_eleven_mul_radius_div_sixteen_le_classWorstCaseRisk_of_sharedHaar
      hN design estimator orientationLaw state reference hstate hreference
        radius hradius hmembership hseparated budget hbudgetFinite honeCopy
        hinformation hlogTwo

end GenieExperiment

end PhysicalRisk

end TomographyOracleCore
