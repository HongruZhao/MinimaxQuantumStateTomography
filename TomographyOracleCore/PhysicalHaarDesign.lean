import TomographyOracleCore.MatrixRealEncoding
import TomographyOracleCore.PhysicalRisk

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped ENNReal

noncomputable section

/-!
# The exact repeated projective-Haar physical design

This module transports a matrix-valued dominated POVM through a measurable
equivalence, then specializes that construction to the projective-Haar POVM
and the canonical real coding of complex matrices.  A constant public seed
selects the same one-copy POVM on every shot, and the outcome kernel is the
finite product of the one-copy Born laws.
-/

namespace PhysicalPOVM.DominatedPOVM

variable {D : ℕ} {Outcome Code : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
  [MeasurableSpace Code] [StandardBorelSpace Code]

/-- A measure-preserving measurable equivalence transports a tilted measure
to the correspondingly tilted pushforward measure. -/
private theorem map_withDensity_comp_measurableEquiv
    {mu : Measure Outcome} (e : Outcome ≃ᵐ Code)
    (f : Code → ℝ≥0∞) (hf : Measurable f) :
    Measure.map e (mu.withDensity (f ∘ e)) =
      (Measure.map e mu).withDensity f := by
  let he : MeasurePreserving e mu (Measure.map e mu) :=
    ⟨e.measurable, rfl⟩
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map' hg.aemeasurable he.measurable.aemeasurable]
  change (∫⁻ x, (g ∘ e) x ∂mu.withDensity (f ∘ e)) =
    ∫⁻ y, g y ∂(Measure.map e mu).withDensity f
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp e.measurable)
      (hg.comp e.measurable),
    lintegral_withDensity_eq_lintegral_mul _ hf hg]
  simpa only [Function.comp_apply, Pi.mul_apply] using
    he.lintegral_comp (hf.fun_mul hg)

/-- The fixed-state Born density of a measurably transported effect is
measurable on the coded outcome space. -/
theorem measurable_bornDensityFrom_comp_measurableEquiv
    (M : DominatedPOVM D Outcome) (e : Outcome ≃ᵐ Code)
    (rho : DensityOperator (Fin D)) :
    Measurable
      (bornDensityFrom (fun z : Code ↦ M.effect (e.symm z)) rho) := by
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ (fun i _ ↦
    Finset.measurable_sum Finset.univ (fun j _ ↦
      measurable_const.mul
        ((M.effect_measurable j i).comp e.symm.measurable)))

/-- Transporting the scalar base and pulling the effect back through a
measurable equivalence transports every Born law by the same equivalence. -/
theorem bornMeasureFrom_map_measurableEquiv
    (M : DominatedPOVM D Outcome) (e : Outcome ≃ᵐ Code)
    (rho : DensityOperator (Fin D)) :
    bornMeasureFrom (Measure.map e M.base)
        (fun z : Code ↦ M.effect (e.symm z)) rho =
      Measure.map e (bornMeasureFrom M.base M.effect rho) := by
  symm
  unfold bornMeasureFrom
  have h := map_withDensity_comp_measurableEquiv
    (mu := M.base) e
    (bornDensityFrom (fun z : Code ↦ M.effect (e.symm z)) rho)
    (measurable_bornDensityFrom_comp_measurableEquiv M e rho)
  have hdensity :
      (bornDensityFrom (fun z : Code ↦ M.effect (e.symm z)) rho ∘ e) =
        bornDensityFrom M.effect rho := by
    funext z
    simp only [Function.comp_apply, bornDensityFrom, e.symm_apply_apply]
  rw [hdensity] at h
  exact h

/-- A dominated POVM transported through a Borel isomorphism of its outcome
space.  No statistical or geometric assumption is added. -/
noncomputable def mapMeasurableEquiv
    (M : DominatedPOVM D Outcome) (e : Outcome ≃ᵐ Code) :
    DominatedPOVM D Code := by
  letI : IsFiniteMeasure M.base := M.base_finite
  refine
    { dimension_pos := M.dimension_pos
      base := Measure.map e M.base
      base_finite := by infer_instance
      effect := fun z ↦ M.effect (e.symm z)
      effect_measurable := fun i j ↦
        (M.effect_measurable i j).comp e.symm.measurable
      effect_integrable := fun i j ↦ by
        rw [integrable_map_equiv e]
        convert M.effect_integrable i j using 1
        funext z
        simp only [Function.comp_apply, e.symm_apply_apply]
      effect_ae_posSemidef := by
        rw [e.measurableEmbedding.ae_map_iff]
        simpa only [e.symm_apply_apply] using M.effect_ae_posSemidef
      effect_ae_trace_one := by
        rw [e.measurableEmbedding.ae_map_iff]
        simpa only [e.symm_apply_apply] using M.effect_ae_trace_one
      integral_effect_eq_one := fun i j ↦ by
        rw [integral_map_equiv e]
        simpa only [e.symm_apply_apply] using M.integral_effect_eq_one i j
      born_density_ae_nonnegative := fun rho ↦ by
        rw [e.measurableEmbedding.ae_map_iff]
        simpa only [e.symm_apply_apply] using
          M.born_density_ae_nonnegative rho
      born_measurable := by
        change Measurable (fun rho : DensityOperator (Fin D) ↦
          bornMeasureFrom (Measure.map e M.base)
            (fun z : Code ↦ M.effect (e.symm z)) rho)
        have hfun :
            (fun rho : DensityOperator (Fin D) ↦
              bornMeasureFrom (Measure.map e M.base)
                (fun z : Code ↦ M.effect (e.symm z)) rho) =
              fun rho ↦
                Measure.map e (bornMeasureFrom M.base M.effect rho) := by
          funext rho
          exact bornMeasureFrom_map_measurableEquiv M e rho
        rw [hfun]
        exact (Measure.measurable_map e e.measurable).comp M.born_measurable
      born_probability := fun rho ↦ by
        rw [bornMeasureFrom_map_measurableEquiv M e rho]
        letI : IsProbabilityMeasure
            (bornMeasureFrom M.base M.effect rho) := M.born_probability rho
        exact Measure.isProbabilityMeasure_map e.measurable.aemeasurable }

@[simp]
theorem mapMeasurableEquiv_base
    (M : DominatedPOVM D Outcome) (e : Outcome ≃ᵐ Code) :
    (M.mapMeasurableEquiv e).base = Measure.map e M.base :=
  rfl

@[simp]
theorem mapMeasurableEquiv_effect
    (M : DominatedPOVM D Outcome) (e : Outcome ≃ᵐ Code) (z : Code) :
    (M.mapMeasurableEquiv e).effect z = M.effect (e.symm z) :=
  rfl

theorem mapMeasurableEquiv_bornMeasure
    (M : DominatedPOVM D Outcome) (e : Outcome ≃ᵐ Code)
    (rho : DensityOperator (Fin D)) :
    (M.mapMeasurableEquiv e).bornMeasure rho =
      Measure.map e (M.bornMeasure rho) := by
  exact bornMeasureFrom_map_measurableEquiv M e rho

end PhysicalPOVM.DominatedPOVM

namespace PhysicalRisk

open Set MeasurableSpace

/-! ## Measurability of finite product probability laws -/

/-- A finite product of a measurably varying family of probability measures
is itself a measurably varying measure. -/
theorem measurable_measure_pi_probability
    {Parameter Index : Type*} {X : Index → Type*}
    [MeasurableSpace Parameter] [Fintype Index]
    [∀ i, MeasurableSpace (X i)]
    (mu : Parameter → ∀ i, Measure (X i))
    (hmu : ∀ i, Measurable fun p ↦ mu p i)
    (hprob : ∀ p i, IsProbabilityMeasure (mu p i)) :
    Measurable fun p ↦ Measure.pi (mu p) := by
  classical
  letI (p : Parameter) (i : Index) : IsProbabilityMeasure (mu p i) :=
    hprob p i
  refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    (μ := fun p ↦ Measure.pi (mu p))
    (S := Set.pi Set.univ '' Set.pi Set.univ
      (fun i ↦ {s : Set (X i) | MeasurableSet s}))
    generateFrom_pi.symm isPiSystem_pi ?_
  intro s hs
  rcases hs with ⟨t, ht, rfl⟩
  simp_rw [Measure.pi_pi]
  exact Finset.measurable_fun_prod Finset.univ (fun i _ ↦
    (Measure.measurable_coe (ht i (mem_univ i))).comp (hmu i))

/-! ## The real-coded projective-Haar POVM -/

variable {D T : ℕ}

/-- The named Borel isomorphism used for both encoding and decoding.  Naming
it keeps all downstream identities independent of the proof term that
supplies nonemptiness of `Fin D`. -/
noncomputable def haarOutcomeRealMeasurableEquiv
    (D : ℕ) (hD : 0 < D) :
    Matrix (Fin D) (Fin D) ℂ ≃ᵐ ℝ := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  exact complexMatrixRealMeasurableEquiv (Fin D)

/-- Decode a universal real outcome back to the exact complex matrix sampled
by the projective-Haar POVM. -/
noncomputable def decodeHaarOutcome (D : ℕ) (hD : 0 < D) :
    ℝ → Matrix (Fin D) (Fin D) ℂ :=
  fun z ↦ (haarOutcomeRealMeasurableEquiv D hD).symm z

/-- Encode a matrix-valued projective-Haar outcome as a real number. -/
noncomputable def encodeHaarOutcome (D : ℕ) (hD : 0 < D) :
    Matrix (Fin D) (Fin D) ℂ → ℝ :=
  fun B ↦ haarOutcomeRealMeasurableEquiv D hD B

theorem measurable_decodeHaarOutcome (D : ℕ) (hD : 0 < D) :
    Measurable (decodeHaarOutcome D hD) := by
  exact (haarOutcomeRealMeasurableEquiv D hD).symm.measurable

theorem measurable_encodeHaarOutcome (D : ℕ) (hD : 0 < D) :
    Measurable (encodeHaarOutcome D hD) := by
  exact (haarOutcomeRealMeasurableEquiv D hD).measurable

@[simp]
theorem decodeHaarOutcome_encodeHaarOutcome
    (D : ℕ) (hD : 0 < D) (B : Matrix (Fin D) (Fin D) ℂ) :
    decodeHaarOutcome D hD (encodeHaarOutcome D hD B) = B := by
  exact (haarOutcomeRealMeasurableEquiv D hD).symm_apply_apply B

@[simp]
theorem encodeHaarOutcome_decodeHaarOutcome
    (D : ℕ) (hD : 0 < D) (z : ℝ) :
    encodeHaarOutcome D hD (decodeHaarOutcome D hD z) = z := by
  exact (haarOutcomeRealMeasurableEquiv D hD).apply_symm_apply z

/-- The exact projective-Haar POVM with outcomes transported to `ℝ`. -/
noncomputable def realCodedProjectiveHaarPOVM
    (D : ℕ) (hD : 0 < D) : DominatedPOVM D ℝ :=
  (projectiveHaarPOVM D hD).mapMeasurableEquiv
    (haarOutcomeRealMeasurableEquiv D hD)

@[simp]
theorem realCodedProjectiveHaarPOVM_effect
    (D : ℕ) (hD : 0 < D) (z : ℝ) :
    (realCodedProjectiveHaarPOVM D hD).effect z =
      decodeHaarOutcome D hD z := by
  rfl

theorem realCodedProjectiveHaarPOVM_bornMeasure
    (D : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    (realCodedProjectiveHaarPOVM D hD).bornMeasure rho =
      Measure.map (encodeHaarOutcome D hD)
        ((projectiveHaarPOVM D hD).bornMeasure rho) := by
  exact DominatedPOVM.mapMeasurableEquiv_bornMeasure
    (projectiveHaarPOVM D hD) (haarOutcomeRealMeasurableEquiv D hD) rho

/-- Decoding the real-coded one-copy Born law recovers the original
matrix-valued projective-Haar Born law exactly. -/
theorem map_decodeHaarOutcome_realCodedProjectiveHaarPOVM_bornMeasure
    (D : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    Measure.map (decodeHaarOutcome D hD)
        ((realCodedProjectiveHaarPOVM D hD).bornMeasure rho) =
      (projectiveHaarPOVM D hD).bornMeasure rho := by
  rw [realCodedProjectiveHaarPOVM_bornMeasure]
  rw [Measure.map_map (measurable_decodeHaarOutcome D hD)
    (measurable_encodeHaarOutcome D hD)]
  have hcomp :
      decodeHaarOutcome D hD ∘ encodeHaarOutcome D hD =
        id := by
    funext B
    exact decodeHaarOutcome_encodeHaarOutcome D hD B
  rw [hcomp, Measure.map_id]

/-! ## Independent repetition and the concrete physical design -/

/-- Conditional on the state (and the unused public seed), the repeated
outcome law is the finite product of the real-coded one-copy Born law. -/
noncomputable def repeatedProjectiveHaarOutcomesKernel
    (D T : ℕ) (hD : 0 < D) :
    Kernel (DensityOperator (Fin D) × ℝ) (Fin T → ℝ) where
  toFun := fun p ↦ Measure.pi fun _ : Fin T ↦
    (realCodedProjectiveHaarPOVM D hD).bornMeasure p.1
  measurable' := by
    apply measurable_measure_pi_probability
    · intro t
      exact (realCodedProjectiveHaarPOVM D hD).born_measurable.comp measurable_fst
    · intro p t
      exact (realCodedProjectiveHaarPOVM D hD).born_probability p.1

instance repeatedProjectiveHaarOutcomesKernel_isMarkov
    (D T : ℕ) (hD : 0 < D) :
    IsMarkovKernel (repeatedProjectiveHaarOutcomesKernel D T hD) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure
      (Measure.pi fun _ : Fin T ↦
        (realCodedProjectiveHaarPOVM D hD).bornMeasure p.1)
    letI : IsProbabilityMeasure
        ((realCodedProjectiveHaarPOVM D hD).bornMeasure p.1) :=
      (realCodedProjectiveHaarPOVM D hD).born_probability p.1
    infer_instance

@[simp]
theorem repeatedProjectiveHaarOutcomesKernel_apply
    (D T : ℕ) (hD : 0 < D)
    (p : DensityOperator (Fin D) × ℝ) :
    repeatedProjectiveHaarOutcomesKernel D T hD p =
      Measure.pi fun _ : Fin T ↦
        (realCodedProjectiveHaarPOVM D hD).bornMeasure p.1 :=
  rfl

/-- Exact physical design consisting of `T` conditionally independent
projective-Haar one-copy measurements and a deterministic public seed. -/
noncomputable def projectiveHaarPhysicalDesign
    (D T : ℕ) (hD : 0 < D) : Design D T :=
  { dimension_pos := hD
    seed := Measure.dirac (0 : ℝ)
    seed_probability := by infer_instance
    measurement := fun _ _ ↦ realCodedProjectiveHaarPOVM D hD
    shot_measurable := fun _ ↦
      (realCodedProjectiveHaarPOVM D hD).born_measurable.comp measurable_fst
    outcomes := repeatedProjectiveHaarOutcomesKernel D T hD
    outcomes_markov := by infer_instance
    outcomes_eq_pi := fun _ ↦ rfl }

@[simp]
theorem projectiveHaarPhysicalDesign_seed
    (D T : ℕ) (hD : 0 < D) :
    (projectiveHaarPhysicalDesign D T hD).seed = Measure.dirac (0 : ℝ) :=
  rfl

@[simp]
theorem projectiveHaarPhysicalDesign_measurement
    (D T : ℕ) (hD : 0 < D) (t : Fin T) (seed : ℝ) :
    (projectiveHaarPhysicalDesign D T hD).measurement t seed =
      realCodedProjectiveHaarPOVM D hD :=
  rfl

@[simp]
theorem projectiveHaarPhysicalDesign_outcomes
    (D T : ℕ) (hD : 0 < D)
    (p : DensityOperator (Fin D) × ℝ) :
    (projectiveHaarPhysicalDesign D T hD).outcomes p =
      Measure.pi fun _ : Fin T ↦
        (realCodedProjectiveHaarPOVM D hD).bornMeasure p.1 :=
  rfl

/-- Decode every component of a real-coded repeated outcome vector. -/
noncomputable def decodeHaarOutcomes
    (D T : ℕ) (hD : 0 < D) :
    (Fin T → ℝ) → (Fin T → Matrix (Fin D) (Fin D) ℂ) :=
  fun z t ↦ decodeHaarOutcome D hD (z t)

theorem measurable_decodeHaarOutcomes
    (D T : ℕ) (hD : 0 < D) :
    Measurable (decodeHaarOutcomes D T hD) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_decodeHaarOutcome D hD).comp (measurable_pi_apply t)

@[simp]
theorem decodeHaarOutcomes_apply
    (D T : ℕ) (hD : 0 < D) (z : Fin T → ℝ) (t : Fin T) :
    decodeHaarOutcomes D T hD z t = decodeHaarOutcome D hD (z t) :=
  rfl

/-- Decoding every coordinate of the conditionally independent repeated law
recovers the finite product of the original matrix-valued Born laws. -/
theorem map_decodeHaarOutcomes_projectiveHaarPhysicalDesign_outcomes
    (D T : ℕ) (hD : 0 < D)
    (p : DensityOperator (Fin D) × ℝ) :
    Measure.map (decodeHaarOutcomes D T hD)
        ((projectiveHaarPhysicalDesign D T hD).outcomes p) =
      Measure.pi fun _ : Fin T ↦
        (projectiveHaarPOVM D hD).bornMeasure p.1 := by
  letI : IsProbabilityMeasure
      ((projectiveHaarPOVM D hD).bornMeasure p.1) :=
    (projectiveHaarPOVM D hD).born_probability p.1
  let hcoord (t : Fin T) :
      MeasurePreserving (decodeHaarOutcome D hD)
        ((realCodedProjectiveHaarPOVM D hD).bornMeasure p.1)
        ((projectiveHaarPOVM D hD).bornMeasure p.1) :=
    { measurable := measurable_decodeHaarOutcome D hD
      map_eq :=
        map_decodeHaarOutcome_realCodedProjectiveHaarPOVM_bornMeasure
          D hD p.1 }
  exact (measurePreserving_pi
    (fun _ : Fin T ↦
      (realCodedProjectiveHaarPOVM D hD).bornMeasure p.1)
    (fun _ : Fin T ↦ (projectiveHaarPOVM D hD).bornMeasure p.1)
    hcoord).map_eq

end PhysicalRisk

end

end TomographyOracleCore
