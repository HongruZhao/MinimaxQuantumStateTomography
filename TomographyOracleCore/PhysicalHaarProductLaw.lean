import TomographyOracleCore.PhysicalHaarDesign
import TomographyOracleCore.PhysicalProductScore

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM

noncomputable section

/-!
# The full physical projective-Haar experiment has the flat product law

The design in `PhysicalHaarDesign` first emits its deterministic public real
seed and then a real-coded vector of independent projective-Haar outcomes.
This module gives the exact measurable decoder from that complete physical
transcript to the matrix-valued `Fin (B * m)` product space used by
`PhysicalProductScore`.
-/

namespace PhysicalRisk

variable {D B m : ℕ}

/-- Discard the deterministic public seed and decode every real-coded Haar
outcome back to its matrix value. -/
noncomputable def decodeHaarExperiment
    (D B m : ℕ) (hD : 0 < D) :
    Data (B * m) →
      (Fin (B * m) → Matrix (Fin D) (Fin D) ℂ) :=
  decodeHaarOutcomes D (B * m) hD ∘ Prod.snd

theorem measurable_decodeHaarExperiment
    (D B m : ℕ) (hD : 0 < D) :
    Measurable (decodeHaarExperiment D B m hD) := by
  exact (measurable_decodeHaarOutcomes D (B * m) hD).comp measurable_snd

@[simp]
theorem decodeHaarExperiment_apply
    (D B m : ℕ) (hD : 0 < D)
    (data : Data (B * m)) (t : Fin (B * m)) :
    decodeHaarExperiment D B m hD data t =
      decodeHaarOutcome D hD (data.2 t) :=
  rfl

/- The outcome marginal of the full experiment is its conditional outcome
law evaluated at the deterministic seed. -/
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

/-- The exact map identity from the complete physical transcript to the flat
matrix-valued product law. -/
theorem map_decodeHaarExperiment_projectiveHaarPhysicalDesign_experimentKernel
    (D B m : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    Measure.map (decodeHaarExperiment D B m hD)
        ((projectiveHaarPhysicalDesign D (B * m) hD).experimentKernel rho) =
      PhysicalProductScore.finProductLaw B m
        ((projectiveHaarPOVM D hD).bornMeasure rho) := by
  change
    Measure.map
        (decodeHaarOutcomes D (B * m) hD ∘ Prod.snd)
        ((projectiveHaarPhysicalDesign D (B * m) hD).experimentKernel rho) =
      PhysicalProductScore.finProductLaw B m
        ((projectiveHaarPOVM D hD).bornMeasure rho)
  rw [← Measure.map_map
      (measurable_decodeHaarOutcomes D (B * m) hD) measurable_snd,
    map_snd_projectiveHaarPhysicalDesign_experimentKernel]
  exact
    map_decodeHaarOutcomes_projectiveHaarPhysicalDesign_outcomes
      D (B * m) hD (rho, 0)

/-- The full experiment-to-flat-product decoder is measure preserving.  This
is the hypothesis required by
`PhysicalProductScore.pullbackFinRawScore_product_obligations`. -/
theorem measurePreserving_decodeHaarExperiment
    (D B m : ℕ) (hD : 0 < D) (rho : DensityOperator (Fin D)) :
    MeasurePreserving (decodeHaarExperiment D B m hD)
      ((projectiveHaarPhysicalDesign D (B * m) hD).experimentKernel rho)
      (PhysicalProductScore.finProductLaw B m
        ((projectiveHaarPOVM D hD).bornMeasure rho)) :=
  { measurable := measurable_decodeHaarExperiment D B m hD
    map_eq :=
      map_decodeHaarExperiment_projectiveHaarPhysicalDesign_experimentKernel
        D B m hD rho }

end PhysicalRisk

end

end TomographyOracleCore
