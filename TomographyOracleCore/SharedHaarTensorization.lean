import TomographyOracleCore.PhysicalTranscriptKL

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ENNReal

/-!
# Reference-KL tensorization with one shared Haar orientation

The latent variable in this file is shared by every shot.  In the physical
application it is the pair consisting of one common Haar orientation and the
public seed of a randomized nonadaptive design.  Conditional on that pair,
the shots form a finite product.

The main identity tensorizes KL *before* the latent variable is discarded.
Data processing then hides the orientation while retaining the public seed.
Thus no false product assertion is made for the Haar-mixture marginals, and
no conditional-mutual-information API is needed.
-/

section KernelAlgebra

/-- A composition-product whose second kernel ignores the first outcome is
the ordinary conditional product of the two kernels. -/
theorem kernelCompProd_prodMkRight_eq_prod
    {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B]
    (kappa : Kernel Z A) [IsMarkovKernel kappa]
    (eta : Kernel Z B) [IsMarkovKernel eta] :
    kappa ⊗ₖ Kernel.prodMkRight A eta = kappa ×ₖ eta := by
  ext z s hs
  rw [Kernel.compProd_apply hs, Kernel.prod_apply, Measure.prod_apply hs]
  rfl

/-- Exchange the two conditionally independent outcomes while leaving their
shared latent coordinate first. -/
def sharedLatentSwap (Z A B : Type*) [MeasurableSpace Z]
    [MeasurableSpace A] [MeasurableSpace B] :
    ((Z × A) × B) ≃ᵐ ((Z × B) × A) :=
  MeasurableEquiv.prodAssoc.trans
    ((MeasurableEquiv.refl Z).prodCongr MeasurableEquiv.prodComm) |>.trans
      MeasurableEquiv.prodAssoc.symm

/-- Reassociate a shared-latent conditional product as sequential sampling. -/
theorem measureCompProd_prod_map_assoc
    {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (kappa : Kernel Z A) [IsMarkovKernel kappa]
    (eta : Kernel Z B) [IsMarkovKernel eta] :
    (mu ⊗ₘ (kappa ×ₖ eta)).map MeasurableEquiv.prodAssoc.symm =
      (mu ⊗ₘ kappa) ⊗ₘ Kernel.prodMkRight A eta := by
  rw [← kernelCompProd_prodMkRight_eq_prod kappa eta]
  exact Measure.compProd_assoc

/-- Sequentially sampling `A` and then `B`, with both kernels depending only
on the same latent variable, is carried by `sharedLatentSwap` to the reverse
sampling order. -/
theorem map_sharedLatentSwap_measureCompProd
    {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (kappa : Kernel Z A) [IsMarkovKernel kappa]
    (eta : Kernel Z B) [IsMarkovKernel eta] :
    ((mu ⊗ₘ kappa) ⊗ₘ Kernel.prodMkRight A eta).map
        (sharedLatentSwap Z A B) =
      (mu ⊗ₘ eta) ⊗ₘ Kernel.prodMkRight B kappa := by
  rw [← measureCompProd_prod_map_assoc mu kappa eta]
  rw [Measure.map_map (sharedLatentSwap Z A B).measurable
    MeasurableEquiv.prodAssoc.symm.measurable]
  rw [show
      (sharedLatentSwap Z A B : ((Z × A) × B) → ((Z × B) × A)) ∘
          (MeasurableEquiv.prodAssoc.symm :
            Z × (A × B) → (Z × A) × B) =
        (MeasurableEquiv.prodAssoc.symm :
            Z × (B × A) → (Z × B) × A) ∘
          Prod.map id Prod.swap by rfl]
  rw [← Measure.map_map MeasurableEquiv.prodAssoc.symm.measurable
    (measurable_id.prodMap measurable_swap)]
  rw [← Measure.compProd_map measurable_swap]
  rw [Kernel.map_prod_swap]
  exact measureCompProd_prod_map_assoc mu eta kappa

/-- Exact two-coordinate KL tensorization when both coordinates share the
same latent variable and are conditionally independent given it. -/
theorem klDiv_sharedLatent_prod_eq_add
    {Z A B : Type*} [MeasurableSpace Z] [MeasurableSpace A]
    [MeasurableSpace B]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (kappa kappa' : Kernel Z A) [IsMarkovKernel kappa]
    [IsMarkovKernel kappa']
    (eta eta' : Kernel Z B) [IsMarkovKernel eta]
    [IsMarkovKernel eta'] :
    klDiv (mu ⊗ₘ (kappa ×ₖ eta))
        (mu ⊗ₘ (kappa' ×ₖ eta')) =
      klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ kappa') +
        klDiv (mu ⊗ₘ eta) (mu ⊗ₘ eta') := by
  let liftEta : Kernel (Z × A) B := Kernel.prodMkRight A eta
  let liftEta' : Kernel (Z × A) B := Kernel.prodMkRight A eta'
  have hleft :
      klDiv (mu ⊗ₘ (kappa ×ₖ eta))
          (mu ⊗ₘ (kappa' ×ₖ eta')) =
        klDiv ((mu ⊗ₘ kappa) ⊗ₘ liftEta)
          ((mu ⊗ₘ kappa') ⊗ₘ liftEta') := by
    rw [← measureCompProd_prod_map_assoc mu kappa eta,
      ← measureCompProd_prod_map_assoc mu kappa' eta']
    exact (klDiv_map_measurableEquiv _ _
      MeasurableEquiv.prodAssoc.symm).symm
  rw [hleft, klDiv_compProd_eq_add]
  congr 1
  rw [show liftEta = Kernel.prodMkRight A eta by rfl,
    show liftEta' = Kernel.prodMkRight A eta' by rfl]
  rw [← klDiv_map_measurableEquiv
    ((mu ⊗ₘ kappa) ⊗ₘ Kernel.prodMkRight A eta)
    ((mu ⊗ₘ kappa) ⊗ₘ Kernel.prodMkRight A eta')
    (sharedLatentSwap Z A B)]
  rw [map_sharedLatentSwap_measureCompProd mu kappa eta,
    map_sharedLatentSwap_measureCompProd mu kappa eta']
  exact klDiv_compProd_left (mu ⊗ₘ eta) (mu ⊗ₘ eta')
    (Kernel.prodMkRight B kappa)

end KernelAlgebra

section FiniteConditionalProduct

/-- Exact KL tensorization for finite conditionally independent products
with one shared latent variable.  The full kernels are supplied explicitly;
their two final hypotheses certify their pointwise product laws. -/
theorem klDiv_sharedLatent_pi_eq_sum
    {Z Outcome : Type*} [MeasurableSpace Z] [MeasurableSpace Outcome]
    (n : ℕ) (mu : Measure Z) [IsProbabilityMeasure mu]
    (kappa eta : Fin n → Kernel Z Outcome)
    [∀ t, IsMarkovKernel (kappa t)] [∀ t, IsMarkovKernel (eta t)]
    (K E : Kernel Z (Fin n → Outcome))
    [IsMarkovKernel K] [IsMarkovKernel E]
    (hK : ∀ z, K z = Measure.pi fun t ↦ kappa t z)
    (hE : ∀ z, E z = Measure.pi fun t ↦ eta t z) :
    klDiv (mu ⊗ₘ K) (mu ⊗ₘ E) =
      ∑ t, klDiv (mu ⊗ₘ kappa t) (mu ⊗ₘ eta t) := by
  induction n with
  | zero =>
      have hKE : K = E := by
        apply Kernel.ext
        intro z
        exact probabilityMeasure_eq_of_subsingleton (K z) (E z)
      rw [hKE, klDiv_self]
      simp
  | succ n ih =>
      let first : Fin (n + 1) := 0
      let e : (Fin (n + 1) → Outcome) ≃ᵐ
          Outcome × (Fin n → Outcome) :=
        MeasurableEquiv.piFinSuccAbove (fun _ ↦ Outcome) first
      let tail : (Fin (n + 1) → Outcome) → (Fin n → Outcome) :=
        fun y j ↦ y (first.succAbove j)
      have htail : Measurable tail := by
        apply measurable_pi_lambda
        intro j
        exact measurable_pi_apply (first.succAbove j)
      let kappaTail : Fin n → Kernel Z Outcome :=
        fun j ↦ kappa (first.succAbove j)
      let etaTail : Fin n → Kernel Z Outcome :=
        fun j ↦ eta (first.succAbove j)
      let KTail : Kernel Z (Fin n → Outcome) := K.map tail
      let ETail : Kernel Z (Fin n → Outcome) := E.map tail
      letI : IsMarkovKernel KTail := Kernel.IsMarkovKernel.map K htail
      letI : IsMarkovKernel ETail := Kernel.IsMarkovKernel.map E htail
      have hKTail (z : Z) :
          KTail z = Measure.pi fun j ↦ kappaTail j z := by
        change (K.map tail) z = _
        rw [Kernel.map_apply K htail, hK z]
        have hsplit :=
          (measurePreserving_piFinSuccAbove
            (fun t : Fin (n + 1) ↦ kappa t z) first).map_eq
        rw [show tail = Prod.snd ∘ e by rfl]
        rw [← Measure.map_map measurable_snd e.measurable]
        rw [hsplit]
        simp [kappaTail]
      have hETail (z : Z) :
          ETail z = Measure.pi fun j ↦ etaTail j z := by
        change (E.map tail) z = _
        rw [Kernel.map_apply E htail, hE z]
        have hsplit :=
          (measurePreserving_piFinSuccAbove
            (fun t : Fin (n + 1) ↦ eta t z) first).map_eq
        rw [show tail = Prod.snd ∘ e by rfl]
        rw [← Measure.map_map measurable_snd e.measurable]
        rw [hsplit]
        simp [etaTail]
      have hKmap : K.map e = kappa first ×ₖ KTail := by
        apply Kernel.ext
        intro z
        rw [Kernel.map_apply K e.measurable, hK z]
        rw [Kernel.prod_apply, hKTail z]
        simpa [e] using (measurePreserving_piFinSuccAbove
          (fun t : Fin (n + 1) ↦ kappa t z) first).map_eq
      have hEmap : E.map e = eta first ×ₖ ETail := by
        apply Kernel.ext
        intro z
        rw [Kernel.map_apply E e.measurable, hE z]
        rw [Kernel.prod_apply, hETail z]
        simpa [e] using (measurePreserving_piFinSuccAbove
          (fun t : Fin (n + 1) ↦ eta t z) first).map_eq
      calc
        klDiv (mu ⊗ₘ K) (mu ⊗ₘ E) =
            klDiv ((mu ⊗ₘ K).map (Prod.map id e))
              ((mu ⊗ₘ E).map (Prod.map id e)) :=
          (klDiv_map_measurableEquiv _ _
            ((MeasurableEquiv.refl Z).prodCongr e)).symm
        _ = klDiv (mu ⊗ₘ (kappa first ×ₖ KTail))
            (mu ⊗ₘ (eta first ×ₖ ETail)) := by
          rw [← Measure.compProd_map e.measurable,
            ← Measure.compProd_map e.measurable, hKmap, hEmap]
        _ = klDiv (mu ⊗ₘ kappa first) (mu ⊗ₘ eta first) +
            klDiv (mu ⊗ₘ KTail) (mu ⊗ₘ ETail) :=
          klDiv_sharedLatent_prod_eq_add
            mu (kappa first) (eta first) KTail ETail
        _ = klDiv (mu ⊗ₘ kappa first) (mu ⊗ₘ eta first) +
            ∑ j, klDiv (mu ⊗ₘ kappaTail j) (mu ⊗ₘ etaTail j) := by
          rw [ih kappaTail etaTail KTail ETail hKTail hETail]
        _ = ∑ t, klDiv (mu ⊗ₘ kappa t) (mu ⊗ₘ eta t) := by
          rw [Fin.sum_univ_succAbove
            (fun t ↦ klDiv (mu ⊗ₘ kappa t) (mu ⊗ₘ eta t)) first]

/-- Any statistic of the latent variable and outcome vector has KL bounded
by the sum of the one-shot shared-latent KL divergences. -/
theorem klDiv_map_sharedLatent_pi_le_sum
    {Z Outcome Decoded : Type*} [MeasurableSpace Z]
    [MeasurableSpace Outcome] [MeasurableSpace Decoded]
    (n : ℕ) (mu : Measure Z) [IsProbabilityMeasure mu]
    (kappa eta : Fin n → Kernel Z Outcome)
    [∀ t, IsMarkovKernel (kappa t)] [∀ t, IsMarkovKernel (eta t)]
    (K E : Kernel Z (Fin n → Outcome))
    [IsMarkovKernel K] [IsMarkovKernel E]
    (hK : ∀ z, K z = Measure.pi fun t ↦ kappa t z)
    (hE : ∀ z, E z = Measure.pi fun t ↦ eta t z)
    (decode : Z × (Fin n → Outcome) → Decoded)
    (hdecode : Measurable decode) :
    klDiv ((mu ⊗ₘ K).map decode) ((mu ⊗ₘ E).map decode) ≤
      ∑ t, klDiv (mu ⊗ₘ kappa t) (mu ⊗ₘ eta t) := by
  exact (klDiv_map_le _ _ hdecode).trans_eq
    (klDiv_sharedLatent_pi_eq_sum n mu kappa eta K E hK hE)

/-- A list of genuine one-copy reference-KL estimates implies the full
shared-latent bound.  The conclusion is proved here rather than assumed. -/
theorem klDiv_map_sharedLatent_pi_le_budget
    {Z Outcome Decoded : Type*} [MeasurableSpace Z]
    [MeasurableSpace Outcome] [MeasurableSpace Decoded]
    (n : ℕ) (mu : Measure Z) [IsProbabilityMeasure mu]
    (kappa eta : Fin n → Kernel Z Outcome)
    [∀ t, IsMarkovKernel (kappa t)] [∀ t, IsMarkovKernel (eta t)]
    (K E : Kernel Z (Fin n → Outcome))
    [IsMarkovKernel K] [IsMarkovKernel E]
    (hK : ∀ z, K z = Measure.pi fun t ↦ kappa t z)
    (hE : ∀ z, E z = Measure.pi fun t ↦ eta t z)
    (decode : Z × (Fin n → Outcome) → Decoded)
    (hdecode : Measurable decode) (budget : Fin n → ENNReal)
    (hone : ∀ t, klDiv (mu ⊗ₘ kappa t) (mu ⊗ₘ eta t) ≤ budget t) :
    klDiv ((mu ⊗ₘ K).map decode) ((mu ⊗ₘ E).map decode) ≤
      ∑ t, budget t := by
  exact (klDiv_map_sharedLatent_pi_le_sum
    n mu kappa eta K E hK hE decode hdecode).trans
      (Finset.sum_le_sum fun t _ ↦ hone t)

end FiniteConditionalProduct

namespace PhysicalPOVM.RandomizedNonadaptiveDesign

section SharedOrientation

variable {D T : ℕ} {Orientation Seed Outcome : Type*}
  [MeasurableSpace Orientation] [StandardBorelSpace Orientation]
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- Feed one oriented state and the public seed into a physical design. -/
def orientationContext
    (state : Orientation → DensityOperator (Fin D)) :
    Orientation × Seed → DensityOperator (Fin D) × Seed :=
  fun z ↦ (state z.1, z.2)

theorem measurable_orientationContext
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    Measurable (orientationContext (Seed := Seed) state) :=
  (hstate.comp measurable_fst).prodMk measurable_snd

/-- The `t`th Born kernel as a kernel of the common orientation/public-seed
pair. -/
noncomputable def sharedOrientationShotKernel
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (t : Fin T) :
    Kernel (Orientation × Seed) Outcome :=
  (design.shotKernel t).comap
    (orientationContext (Seed := Seed) state)
    (measurable_orientationContext state hstate)

instance sharedOrientationShotKernel_isMarkov
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (t : Fin T) :
    IsMarkovKernel (sharedOrientationShotKernel design state hstate t) := by
  unfold sharedOrientationShotKernel
  infer_instance

@[simp]
theorem sharedOrientationShotKernel_apply
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (t : Fin T) (z : Orientation × Seed) :
    sharedOrientationShotKernel design state hstate t z =
      (design.measurement t z.2).bornMeasure (state z.1) :=
  rfl

/-- The conditionally product outcome-vector kernel under one oriented
state. -/
noncomputable def sharedOrientationOutcomesKernel
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    Kernel (Orientation × Seed) (Fin T → Outcome) :=
  design.outcomes.comap
    (orientationContext (Seed := Seed) state)
    (measurable_orientationContext state hstate)

instance sharedOrientationOutcomesKernel_isMarkov
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) :
    IsMarkovKernel (sharedOrientationOutcomesKernel design state hstate) := by
  unfold sharedOrientationOutcomesKernel
  infer_instance

theorem sharedOrientationOutcomesKernel_eq_pi
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (state : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (z : Orientation × Seed) :
    sharedOrientationOutcomesKernel design state hstate z =
      Measure.pi fun t ↦ sharedOrientationShotKernel design state hstate t z := by
  simpa [sharedOrientationOutcomesKernel, sharedOrientationShotKernel,
    orientationContext] using
      design.outcomes_eq_pi (state z.1, z.2)

/-- Hide the Haar orientation from a genie-aided transcript while retaining
the public seed and every observed outcome. -/
def hideOrientationTranscript :
    ((Orientation × Seed) × (Fin T → Outcome)) →
      Seed × (Fin T → Outcome) :=
  fun p ↦ (p.1.2, p.2)

theorem measurable_hideOrientationTranscript :
    Measurable
      (hideOrientationTranscript
        (Orientation := Orientation) (Seed := Seed) (Outcome := Outcome)
        (T := T)) :=
  (measurable_snd.comp measurable_fst).prodMk measurable_snd

/-- Exact reference-KL tensorization for a randomized nonadaptive design,
one common orientation, and one public seed shared by all shots. -/
theorem sharedOrientation_klDiv_eq_sum
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state reference : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (hreference : Measurable reference) :
    klDiv
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationOutcomesKernel design state hstate)
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationOutcomesKernel design reference hreference) =
      ∑ t, klDiv
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design state hstate t)
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design reference hreference t) := by
  letI : IsProbabilityMeasure design.seed := design.seed_probability
  exact klDiv_sharedLatent_pi_eq_sum T
    (orientationLaw.prod design.seed)
    (sharedOrientationShotKernel design state hstate)
    (sharedOrientationShotKernel design reference hreference)
    (sharedOrientationOutcomesKernel design state hstate)
    (sharedOrientationOutcomesKernel design reference hreference)
    (sharedOrientationOutcomesKernel_eq_pi design state hstate)
    (sharedOrientationOutcomesKernel_eq_pi design reference hreference)

/-- After the common orientation is hidden, data processing bounds the
physical public-seed transcript KL by the same sum of one-copy joint KLs. -/
theorem hiddenOrientationTranscript_klDiv_le_sum
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state reference : Orientation → DensityOperator (Fin D))
    (hstate : Measurable state) (hreference : Measurable reference) :
    klDiv
        (((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationOutcomesKernel design state hstate).map
            (hideOrientationTranscript
              (Orientation := Orientation) (Seed := Seed)
              (Outcome := Outcome) (T := T)))
        (((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationOutcomesKernel design reference hreference).map
            (hideOrientationTranscript
              (Orientation := Orientation) (Seed := Seed)
              (Outcome := Outcome) (T := T))) ≤
      ∑ t, klDiv
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design state hstate t)
        ((orientationLaw.prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design reference hreference t) := by
  letI : IsProbabilityMeasure design.seed := design.seed_probability
  exact klDiv_map_sharedLatent_pi_le_sum T
    (orientationLaw.prod design.seed)
    (sharedOrientationShotKernel design state hstate)
    (sharedOrientationShotKernel design reference hreference)
    (sharedOrientationOutcomesKernel design state hstate)
    (sharedOrientationOutcomesKernel design reference hreference)
    (sharedOrientationOutcomesKernel_eq_pi design state hstate)
    (sharedOrientationOutcomesKernel_eq_pi design reference hreference)
    (hideOrientationTranscript
      (Orientation := Orientation) (Seed := Seed) (Outcome := Outcome)
      (T := T))
    measurable_hideOrientationTranscript

/-- The shared-Haar information-radius operation.  Its only substantive
input is a one-copy reference-KL bound for each label and preselected shot;
the `T`-copy conclusion follows internally. -/
theorem sharedHaar_referenceKL_informationRadius
    {Label : Type*}
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Label → Orientation → DensityOperator (Fin D))
    (reference : Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (hreference : Measurable reference)
    (budget : Fin T → ENNReal)
    (honeCopy : ∀ a t,
      klDiv
          ((orientationLaw.prod design.seed) ⊗ₘ
            sharedOrientationShotKernel design (state a) (hstate a) t)
          ((orientationLaw.prod design.seed) ⊗ₘ
            sharedOrientationShotKernel design reference hreference t) ≤
        budget t) :
    ∀ a,
      klDiv
          (((orientationLaw.prod design.seed) ⊗ₘ
            sharedOrientationOutcomesKernel design (state a) (hstate a)).map
              (hideOrientationTranscript
                (Orientation := Orientation) (Seed := Seed)
                (Outcome := Outcome) (T := T)))
          (((orientationLaw.prod design.seed) ⊗ₘ
            sharedOrientationOutcomesKernel design reference hreference).map
              (hideOrientationTranscript
                (Orientation := Orientation) (Seed := Seed)
                (Outcome := Outcome) (T := T))) ≤
        ∑ t, budget t := by
  intro a
  exact (hiddenOrientationTranscript_klDiv_le_sum
    design orientationLaw (state a) reference (hstate a) hreference).trans
      (Finset.sum_le_sum fun t _ ↦ honeCopy a t)

end SharedOrientation

end PhysicalPOVM.RandomizedNonadaptiveDesign

end TomographyOracleCore
