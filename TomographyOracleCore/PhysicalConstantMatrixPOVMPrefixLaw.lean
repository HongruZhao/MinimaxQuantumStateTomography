import TomographyOracleCore.PhysicalConstantMatrixPOVMProductLaw
import TomographyOracleCore.PhysicalHaarPrefixLaw

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM

noncomputable section

namespace PhysicalRisk

/-!
# Prefix law for an arbitrary repeated matrix-valued POVM

The first `B * m` decoded outcomes of a longer `T`-shot constant design have
exactly the flat product law for the retained independent measurements.
-/

noncomputable def decodeAllMatrixPOVMExperiment
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    Data T → (Fin T → Matrix (Fin D) (Fin D) ℂ) :=
  decodeMatrixPOVMOutcomes M T ∘ Prod.snd

theorem measurable_decodeAllMatrixPOVMExperiment
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    Measurable (decodeAllMatrixPOVMExperiment M T) :=
  (measurable_decodeMatrixPOVMOutcomes M T).comp measurable_snd

@[simp]
theorem decodeAllMatrixPOVMExperiment_apply
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (data : Data T) (t : Fin T) :
    decodeAllMatrixPOVMExperiment M T data t =
      decodeHaarOutcome D M.dimension_pos (data.2 t) :=
  rfl

theorem map_snd_constantMatrixPOVMPhysicalDesign_experimentKernel_all
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (rho : DensityOperator (Fin D)) :
    Measure.map Prod.snd
        ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho) =
      (constantMatrixPOVMPhysicalDesign M T).outcomes (rho, 0) := by
  change
    ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho).snd =
      (constantMatrixPOVMPhysicalDesign M T).outcomes (rho, 0)
  rw [PhysicalPOVM.RandomizedNonadaptiveDesign.experimentKernel,
    Kernel.compProd_apply_eq_compProd_sectR,
    PhysicalPOVM.RandomizedNonadaptiveDesign.seedKernel_apply,
    constantMatrixPOVMPhysicalDesign_seed,
    Measure.snd_compProd,
    Measure.dirac_bind (Kernel.measurable _)]
  rfl

theorem map_decodeAllMatrixPOVMExperiment_constantDesign_experimentKernel
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (rho : DensityOperator (Fin D)) :
    Measure.map (decodeAllMatrixPOVMExperiment M T)
        ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho) =
      Measure.pi fun _ : Fin T ↦ M.bornMeasure rho := by
  change
    Measure.map (decodeMatrixPOVMOutcomes M T ∘ Prod.snd)
        ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho) = _
  rw [← Measure.map_map
      (measurable_decodeMatrixPOVMOutcomes M T) measurable_snd,
    map_snd_constantMatrixPOVMPhysicalDesign_experimentKernel_all]
  exact map_decodeMatrixPOVMOutcomes_constantDesign_outcomes M T (rho, 0)

theorem measurePreserving_decodeAllMatrixPOVMExperiment
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (rho : DensityOperator (Fin D)) :
    MeasurePreserving (decodeAllMatrixPOVMExperiment M T)
      ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho)
      (Measure.pi fun _ : Fin T ↦ M.bornMeasure rho) :=
  { measurable := measurable_decodeAllMatrixPOVMExperiment M T
    map_eq :=
      map_decodeAllMatrixPOVMExperiment_constantDesign_experimentKernel
        M T rho }

noncomputable def decodeMatrixPOVMExperimentPrefix
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (T B m : ℕ) (hused : B * m ≤ T) :
    Data T → (Fin (B * m) → Matrix (Fin D) (Fin D) ℂ) :=
  fun data k ↦ decodeAllMatrixPOVMExperiment M T data (Fin.castLE hused k)

theorem measurable_decodeMatrixPOVMExperimentPrefix
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (T B m : ℕ) (hused : B * m ≤ T) :
    Measurable (decodeMatrixPOVMExperimentPrefix M T B m hused) := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_decodeHaarOutcome D M.dimension_pos).comp
    ((measurable_pi_apply (Fin.castLE hused k)).comp measurable_snd)

@[simp]
theorem decodeMatrixPOVMExperimentPrefix_apply
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (T B m : ℕ) (hused : B * m ≤ T)
    (data : Data T) (k : Fin (B * m)) :
    decodeMatrixPOVMExperimentPrefix M T B m hused data k =
      decodeHaarOutcome D M.dimension_pos
        (data.2 (Fin.castLE hused k)) :=
  rfl

theorem map_decodeMatrixPOVMExperimentPrefix_constantDesign_experimentKernel
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (T B m : ℕ) (hused : B * m ≤ T)
    (rho : DensityOperator (Fin D)) :
    Measure.map (decodeMatrixPOVMExperimentPrefix M T B m hused)
        ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho) =
      PhysicalProductScore.finProductLaw B m (M.bornMeasure rho) := by
  let nu := M.bornMeasure rho
  letI : IsProbabilityMeasure nu := M.born_probability rho
  have hall := measurePreserving_decodeAllMatrixPOVMExperiment M T rho
  have hprefix := measurePreserving_finPrefix nu hused
  have hcomp := hprefix.comp hall
  change
    Measure.map
        (fun data : Data T ↦ fun k : Fin (B * m) ↦
          decodeHaarOutcome D M.dimension_pos
            (data.2 (Fin.castLE hused k)))
        ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho) =
      Measure.pi fun _ : Fin (B * m) ↦ M.bornMeasure rho
  simpa [decodeAllMatrixPOVMExperiment, Function.comp_def, nu] using
    hcomp.map_eq

theorem measurePreserving_decodeMatrixPOVMExperimentPrefix
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (T B m : ℕ) (hused : B * m ≤ T)
    (rho : DensityOperator (Fin D)) :
    MeasurePreserving (decodeMatrixPOVMExperimentPrefix M T B m hused)
      ((constantMatrixPOVMPhysicalDesign M T).experimentKernel rho)
      (PhysicalProductScore.finProductLaw B m (M.bornMeasure rho)) :=
  { measurable := measurable_decodeMatrixPOVMExperimentPrefix M T B m hused
    map_eq :=
      map_decodeMatrixPOVMExperimentPrefix_constantDesign_experimentKernel
        M T B m hused rho }

end PhysicalRisk

end

end TomographyOracleCore
