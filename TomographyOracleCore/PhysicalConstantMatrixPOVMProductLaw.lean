import TomographyOracleCore.PhysicalConstantMatrixPOVMDesign
import TomographyOracleCore.PhysicalProductScore

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM

noncomputable section

/-!
# Product-law decoder for a repeated matrix-valued POVM

This is the ensemble-independent counterpart of the projective-Haar decoder.
It identifies the complete real-coded physical transcript with the flat
matrix-valued product law for independent measurement outcomes.
-/

namespace PhysicalRisk

variable {D B m : ℕ}

/-- Decode every coordinate of a real-coded repeated matrix-POVM outcome. -/
noncomputable def decodeMatrixPOVMOutcomes
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    (Fin T → ℝ) → (Fin T → Matrix (Fin D) (Fin D) ℂ) :=
  fun z t => decodeHaarOutcome D M.dimension_pos (z t)

theorem measurable_decodeMatrixPOVMOutcomes
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    Measurable (decodeMatrixPOVMOutcomes M T) := by
  apply measurable_pi_lambda
  intro t
  exact (measurable_decodeHaarOutcome D M.dimension_pos).comp
    (measurable_pi_apply t)

@[simp]
theorem decodeMatrixPOVMOutcomes_apply
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (z : Fin T → ℝ) (t : Fin T) :
    decodeMatrixPOVMOutcomes M T z t =
      decodeHaarOutcome D M.dimension_pos (z t) :=
  rfl

/-- Coordinatewise decoding sends the repeated coded law to the repeated
original matrix Born law. -/
theorem map_decodeMatrixPOVMOutcomes_constantDesign_outcomes
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (p : DensityOperator (Fin D) × ℝ) :
    Measure.map (decodeMatrixPOVMOutcomes M T)
        ((constantMatrixPOVMPhysicalDesign M T).outcomes p) =
      Measure.pi fun _ : Fin T => M.bornMeasure p.1 := by
  letI : IsProbabilityMeasure (M.bornMeasure p.1) :=
    M.born_probability p.1
  let hcoord (t : Fin T) :
      MeasurePreserving (decodeHaarOutcome D M.dimension_pos)
        ((realCodedMatrixPOVM M).bornMeasure p.1)
        (M.bornMeasure p.1) :=
    { measurable := measurable_decodeHaarOutcome D M.dimension_pos
      map_eq :=
        map_decodeHaarOutcome_realCodedMatrixPOVM_bornMeasure M p.1 }
  exact (measurePreserving_pi
    (fun _ : Fin T => (realCodedMatrixPOVM M).bornMeasure p.1)
    (fun _ : Fin T => M.bornMeasure p.1) hcoord).map_eq

/-- Discard the deterministic seed and decode the complete physical
transcript to matrix outcomes. -/
noncomputable def decodeMatrixPOVMExperiment
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (B m : ℕ) :
    Data (B * m) →
      (Fin (B * m) → Matrix (Fin D) (Fin D) ℂ) :=
  decodeMatrixPOVMOutcomes M (B * m) ∘ Prod.snd

theorem measurable_decodeMatrixPOVMExperiment
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (B m : ℕ) :
    Measurable (decodeMatrixPOVMExperiment M B m) :=
  (measurable_decodeMatrixPOVMOutcomes M (B * m)).comp measurable_snd

@[simp]
theorem decodeMatrixPOVMExperiment_apply
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (B m : ℕ)
    (data : Data (B * m)) (t : Fin (B * m)) :
    decodeMatrixPOVMExperiment M B m data t =
      decodeHaarOutcome D M.dimension_pos (data.2 t) :=
  rfl

private theorem map_snd_constantMatrixPOVMPhysicalDesign_experimentKernel
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

/-- Exact map identity from the complete physical transcript to the flat
matrix-valued product law. -/
theorem map_decodeMatrixPOVMExperiment_constantDesign_experimentKernel
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (B m : ℕ)
    (rho : DensityOperator (Fin D)) :
    Measure.map (decodeMatrixPOVMExperiment M B m)
        ((constantMatrixPOVMPhysicalDesign M (B * m)).experimentKernel rho) =
      PhysicalProductScore.finProductLaw B m (M.bornMeasure rho) := by
  change
    Measure.map (decodeMatrixPOVMOutcomes M (B * m) ∘ Prod.snd)
        ((constantMatrixPOVMPhysicalDesign M (B * m)).experimentKernel rho) =
      PhysicalProductScore.finProductLaw B m (M.bornMeasure rho)
  rw [← Measure.map_map
      (measurable_decodeMatrixPOVMOutcomes M (B * m)) measurable_snd,
    map_snd_constantMatrixPOVMPhysicalDesign_experimentKernel]
  exact map_decodeMatrixPOVMOutcomes_constantDesign_outcomes
    M (B * m) (rho, 0)

/-- The transcript decoder is measure preserving. -/
theorem measurePreserving_decodeMatrixPOVMExperiment
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (B m : ℕ)
    (rho : DensityOperator (Fin D)) :
    MeasurePreserving (decodeMatrixPOVMExperiment M B m)
      ((constantMatrixPOVMPhysicalDesign M (B * m)).experimentKernel rho)
      (PhysicalProductScore.finProductLaw B m (M.bornMeasure rho)) :=
  { measurable := measurable_decodeMatrixPOVMExperiment M B m
    map_eq :=
      map_decodeMatrixPOVMExperiment_constantDesign_experimentKernel
        M B m rho }

end PhysicalRisk

end

end TomographyOracleCore
