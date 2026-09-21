import TomographyOracleCore.PhysicalHaarProductLaw

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM

noncomputable section

/-!
# Prefixes of the repeated physical projective-Haar experiment

The concrete design is defined for every number `T` of shots.  This module
decodes all of them and proves that retaining any initial `K ≤ T` coordinates
is measure preserving from the physical transcript to the `K`-fold matrix
product law.  The specialization `K = B * m` is the exact decoder required
to describe any retained prefix of the independent measurement record.
-/

namespace PhysicalRisk

/-! ## A generic prefix of a finite product probability measure -/

/-- Restriction to the first `K ≤ T` coordinates preserves an identically
distributed finite product probability law. -/
theorem measurePreserving_finPrefix
    {T K : ℕ} {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsProbabilityMeasure mu] (hK : K ≤ T) :
    MeasurePreserving
      (fun x : Fin T → X ↦ fun k : Fin K ↦ x (Fin.castLE hK k))
      (Measure.pi fun _ : Fin T ↦ mu)
      (Measure.pi fun _ : Fin K ↦ mu) := by
  let f : Fin K → Fin T := Fin.castLE hK
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact congrArg (fun z : Fin T ↦ z.val) hij
  have hall : iIndepFun
      (fun t : Fin T ↦ fun x : Fin T → X ↦ x t)
      (Measure.pi fun _ : Fin T ↦ mu) := by
    simpa using
      (iIndepFun_pi
        (μ := fun _ : Fin T ↦ mu)
        (X := fun _ : Fin T ↦ id)
        (fun _ ↦ aemeasurable_id))
  have hindep : iIndepFun
      (fun k : Fin K ↦ fun x : Fin T → X ↦ x (f k))
      (Measure.pi fun _ : Fin T ↦ mu) :=
    iIndepFun.precomp hf hall
  refine ⟨measurable_pi_lambda _ (fun k ↦ measurable_pi_apply (f k)), ?_⟩
  have hjoint := hindep.map_fun_eq_pi_map
    (fun k ↦ (measurable_pi_apply (f k)).aemeasurable)
  calc
    Measure.map
        (fun x : Fin T → X ↦ fun k : Fin K ↦ x (Fin.castLE hK k))
        (Measure.pi fun _ : Fin T ↦ mu) =
        Measure.pi (fun k : Fin K ↦
          Measure.map (fun x : Fin T → X ↦ x (f k))
            (Measure.pi fun _ : Fin T ↦ mu)) := by
      simpa [f] using hjoint
    _ = Measure.pi (fun _ : Fin K ↦ mu) := by
      have hcoord :
          (fun k : Fin K ↦
              Measure.map (fun x : Fin T → X ↦ x (f k))
                (Measure.pi fun _ : Fin T ↦ mu)) =
            (fun _ : Fin K ↦ mu) := by
        funext k
        exact
          (measurePreserving_eval (fun _ : Fin T ↦ mu) (f k)).map_eq
      rw [hcoord]

/-! ## Decode all shots, then retain a prefix -/

/-- Discard the deterministic public seed and decode all `T` real-coded
outcomes back to matrices. -/
noncomputable def decodeAllHaarExperiment
    (D T : ℕ) (hD : 0 < D) :
    Data T → (Fin T → Matrix (Fin D) (Fin D) ℂ) :=
  decodeHaarOutcomes D T hD ∘ Prod.snd

theorem measurable_decodeAllHaarExperiment
    (D T : ℕ) (hD : 0 < D) :
    Measurable (decodeAllHaarExperiment D T hD) := by
  exact (measurable_decodeHaarOutcomes D T hD).comp measurable_snd

@[simp]
theorem decodeAllHaarExperiment_apply
    (D T : ℕ) (hD : 0 < D) (data : Data T) (t : Fin T) :
    decodeAllHaarExperiment D T hD data t =
      decodeHaarOutcome D hD (data.2 t) :=
  rfl

/- The outcome marginal of the full experiment is the conditional repeated
outcome law at its deterministic seed. -/
private theorem map_snd_projectiveHaarPhysicalDesign_experimentKernel
    (D T : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    Measure.map Prod.snd
        ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho) =
      (projectiveHaarPhysicalDesign D T hD).outcomes (rho, 0) := by
  change
    ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho).snd =
      (projectiveHaarPhysicalDesign D T hD).outcomes (rho, 0)
  rw [PhysicalPOVM.RandomizedNonadaptiveDesign.experimentKernel,
    Kernel.compProd_apply_eq_compProd_sectR,
    PhysicalPOVM.RandomizedNonadaptiveDesign.seedKernel_apply,
    projectiveHaarPhysicalDesign_seed,
    Measure.snd_compProd,
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

/-- Decoding the entire physical transcript gives exactly the `T`-fold
matrix-valued Born product law. -/
theorem map_decodeAllHaarExperiment_projectiveHaarPhysicalDesign_experimentKernel
    (D T : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    Measure.map (decodeAllHaarExperiment D T hD)
        ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho) =
      Measure.pi fun _ : Fin T ↦
        (projectiveHaarPOVM D hD).bornMeasure rho := by
  change
    Measure.map (decodeHaarOutcomes D T hD ∘ Prod.snd)
        ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho) = _
  rw [← Measure.map_map
      (measurable_decodeHaarOutcomes D T hD) measurable_snd,
    map_snd_projectiveHaarPhysicalDesign_experimentKernel]
  exact
    map_decodeHaarOutcomes_projectiveHaarPhysicalDesign_outcomes
      D T hD (rho, 0)

/-- The all-shot matrix decoder is measure preserving. -/
theorem measurePreserving_decodeAllHaarExperiment
    (D T : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    MeasurePreserving (decodeAllHaarExperiment D T hD)
      ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho)
      (Measure.pi fun _ : Fin T ↦
        (projectiveHaarPOVM D hD).bornMeasure rho) :=
  { measurable := measurable_decodeAllHaarExperiment D T hD
    map_eq :=
      map_decodeAllHaarExperiment_projectiveHaarPhysicalDesign_experimentKernel
        D T hD rho }

/-- Decode exactly the first `B * m` shots of a longer physical transcript. -/
noncomputable def decodeHaarExperimentPrefix
    (D T B m : ℕ) (hD : 0 < D) (hused : B * m ≤ T) :
    Data T → (Fin (B * m) → Matrix (Fin D) (Fin D) ℂ) :=
  fun data k ↦ decodeAllHaarExperiment D T hD data (Fin.castLE hused k)

theorem measurable_decodeHaarExperimentPrefix
    (D T B m : ℕ) (hD : 0 < D) (hused : B * m ≤ T) :
    Measurable (decodeHaarExperimentPrefix D T B m hD hused) := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_decodeHaarOutcome D hD).comp
    ((measurable_pi_apply (Fin.castLE hused k)).comp measurable_snd)

@[simp]
theorem decodeHaarExperimentPrefix_apply
    (D T B m : ℕ) (hD : 0 < D) (hused : B * m ≤ T)
    (data : Data T) (k : Fin (B * m)) :
    decodeHaarExperimentPrefix D T B m hD hused data k =
      decodeHaarOutcome D hD (data.2 (Fin.castLE hused k)) :=
  rfl

/-- Exact law of the decoded `B * m`-shot prefix of a `T`-shot physical
experiment. -/
theorem map_decodeHaarExperimentPrefix_projectiveHaarPhysicalDesign_experimentKernel
    (D T B m : ℕ) (hD : 0 < D) (hused : B * m ≤ T)
    (rho : DensityOperator (Fin D)) :
    Measure.map (decodeHaarExperimentPrefix D T B m hD hused)
        ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho) =
      PhysicalProductScore.finProductLaw B m
        ((projectiveHaarPOVM D hD).bornMeasure rho) := by
  let nu := (projectiveHaarPOVM D hD).bornMeasure rho
  letI : IsProbabilityMeasure nu :=
    (projectiveHaarPOVM D hD).born_probability rho
  have hall := measurePreserving_decodeAllHaarExperiment D T hD rho
  have hprefix := measurePreserving_finPrefix nu hused
  have hcomp := hprefix.comp hall
  change
    Measure.map
        (fun data : Data T ↦ fun k : Fin (B * m) ↦
          decodeHaarOutcome D hD (data.2 (Fin.castLE hused k)))
        ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho) =
      Measure.pi fun _ : Fin (B * m) ↦
        (projectiveHaarPOVM D hD).bornMeasure rho
  simpa [decodeAllHaarExperiment, Function.comp_def, nu] using hcomp.map_eq

/-- Retaining and decoding the first `B * m` shots is measure preserving to
the flat product law of the independent score coordinates. -/
theorem measurePreserving_decodeHaarExperimentPrefix
    (D T B m : ℕ) (hD : 0 < D) (hused : B * m ≤ T)
    (rho : DensityOperator (Fin D)) :
    MeasurePreserving (decodeHaarExperimentPrefix D T B m hD hused)
      ((projectiveHaarPhysicalDesign D T hD).experimentKernel rho)
      (PhysicalProductScore.finProductLaw B m
        ((projectiveHaarPOVM D hD).bornMeasure rho)) :=
  { measurable :=
      measurable_decodeHaarExperimentPrefix D T B m hD hused
    map_eq :=
      map_decodeHaarExperimentPrefix_projectiveHaarPhysicalDesign_experimentKernel
        D T B m hD hused rho }

end PhysicalRisk

end

end TomographyOracleCore
