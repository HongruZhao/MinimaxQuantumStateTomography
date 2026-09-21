import TomographyOracleCore.FiniteProductKL
import TomographyOracleCore.PhysicalDecodedKL

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open MatrixReduction
open scoped BigOperators ENNReal

namespace PhysicalPOVM.RandomizedNonadaptiveDesign

/-!
# KL structure of a randomized nonadaptive physical transcript

The outcomes of a randomized nonadaptive design are independent only after
the public seed is fixed.  Thus the exact tensorization theorem below is
conditional on a seed.  The full transcript law is separately identified as
the composition-product of the common state-independent seed law with the
state-dependent conditional outcome kernel.

No declaration in this file is an axiom.
-/

variable {D T : ℕ} {Seed Outcome : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- At a fixed state, the complete transcript is the public seed law
composition-product with that state's conditional outcome kernel. -/
theorem experimentKernel_apply_eq_seed_compProd
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (rho : DensityOperator (Fin D)) :
    design.experimentKernel rho =
      design.seed ⊗ₘ Kernel.sectR design.outcomes rho := by
  rw [experimentKernel,
    Kernel.compProd_apply_eq_compProd_sectR, seedKernel_apply]

/-- Conditional on a fixed public seed, the outcome-vector KL is exactly the
sum of the `T` one-copy Born-law KL divergences. -/
theorem outcomes_klDiv_eq_sum_shot
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (rho sigma : DensityOperator (Fin D)) (seed : Seed) :
    klDiv (design.outcomes (rho, seed))
        (design.outcomes (sigma, seed)) =
      ∑ t : Fin T,
        klDiv ((design.measurement t seed).bornMeasure rho)
          ((design.measurement t seed).bornMeasure sigma) := by
  letI (t : Fin T) :
      IsProbabilityMeasure
        ((design.measurement t seed).bornMeasure rho) :=
    (design.measurement t seed).born_probability rho
  letI (t : Fin T) :
      IsProbabilityMeasure
        ((design.measurement t seed).bornMeasure sigma) :=
    (design.measurement t seed).born_probability sigma
  rw [design.outcomes_eq_pi (rho, seed),
    design.outcomes_eq_pi (sigma, seed), klDiv_pi_fin_eq_sum]

/-- Any measurable statistic of the conditionally independent outcome
vector has KL at most the sum of the one-copy KL divergences. -/
theorem klDiv_map_outcomes_le_sum_shot
    {Decoded : Type*} [MeasurableSpace Decoded]
    (design : RandomizedNonadaptiveDesign D T Seed Outcome)
    (rho sigma : DensityOperator (Fin D)) (seed : Seed)
    (decode : (Fin T → Outcome) → Decoded)
    (hdecode : Measurable decode) :
    klDiv ((design.outcomes (rho, seed)).map decode)
        ((design.outcomes (sigma, seed)).map decode) ≤
      ∑ t : Fin T,
        klDiv ((design.measurement t seed).bornMeasure rho)
          ((design.measurement t seed).bornMeasure sigma) := by
  calc
    klDiv ((design.outcomes (rho, seed)).map decode)
        ((design.outcomes (sigma, seed)).map decode) ≤
        klDiv (design.outcomes (rho, seed))
          (design.outcomes (sigma, seed)) :=
      klDiv_map_le _ _ hdecode
    _ = ∑ t : Fin T,
        klDiv ((design.measurement t seed).bornMeasure rho)
          ((design.measurement t seed).bornMeasure sigma) :=
      outcomes_klDiv_eq_sum_shot design rho sigma seed

end PhysicalPOVM.RandomizedNonadaptiveDesign

namespace PhysicalRisk

/-! ## Transcript-to-estimator and transcript-to-decoder data processing -/

/-- Passing the raw physical transcript through any randomized physical
estimator cannot increase KL divergence. -/
theorem estimateKernel_klDiv_le_experimentKernel_klDiv
    {D T : ℕ} (design : Design D T) (estimator : Estimator D T)
    (rho sigma : DensityOperator (Fin D)) :
    klDiv (estimateKernel design estimator rho)
        (estimateKernel design estimator sigma) ≤
      klDiv (design.experimentKernel rho)
        (design.experimentKernel sigma) := by
  change
    klDiv (estimator.kernel ∘ₘ design.experimentKernel rho)
        (estimator.kernel ∘ₘ design.experimentKernel sigma) ≤ _
  exact klDiv_comp_right_le
    (design.experimentKernel rho) (design.experimentKernel sigma)
      estimator.kernel

/-- Mapping the estimator output through a measurable finite decoder also
cannot increase KL, so decoded pairwise KL is controlled by raw transcript
KL for the same two states. -/
theorem decodedEstimateKernel_klDiv_le_experimentKernel_klDiv
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) (a b : Fin N) :
    klDiv
        (decodedEstimateKernel design estimator stateOf hstate
          decode hdecode a)
        (decodedEstimateKernel design estimator stateOf hstate
          decode hdecode b) ≤
      klDiv (design.experimentKernel (stateOf a))
        (design.experimentKernel (stateOf b)) := by
  calc
    klDiv
        (decodedEstimateKernel design estimator stateOf hstate
          decode hdecode a)
        (decodedEstimateKernel design estimator stateOf hstate
          decode hdecode b) ≤
        klDiv (estimateKernel design estimator (stateOf a))
          (estimateKernel design estimator (stateOf b)) := by
      rw [decodedEstimateKernel_apply_eq_map design estimator stateOf
        hstate decode hdecode a,
        decodedEstimateKernel_apply_eq_map design estimator stateOf
          hstate decode hdecode b]
      exact klDiv_map_le _ _ hdecode
    _ ≤ klDiv (design.experimentKernel (stateOf a))
        (design.experimentKernel (stateOf b)) :=
      estimateKernel_klDiv_le_experimentKernel_klDiv
        design estimator (stateOf a) (stateOf b)

/-- The decoded physical law is the raw transcript law passed through the
single Markov kernel obtained by composing the randomized estimator with the
deterministic decoder. -/
theorem decodedEstimateKernel_apply_eq_decoderEstimator_comp_transcript
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) (a : Fin N) :
    decodedEstimateKernel design estimator stateOf hstate decode hdecode a =
      (estimator.kernel.map decode) ∘ₘ
        design.experimentKernel (stateOf a) := by
  rw [decodedEstimateKernel_apply_eq_map design estimator stateOf hstate
    decode hdecode a]
  change
    (estimator.kernel ∘ₘ design.experimentKernel (stateOf a)).map decode = _
  exact Measure.map_comp _ _ hdecode

/-- Explicit decoded reference likelihood sums are bounded directly by raw
physical transcript KL.  The transcript reference is first passed through
the same randomized estimator and deterministic decoder as the data. -/
theorem decodedEstimateKernel_referenceLikelihoodSum_le_transcriptKL
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (transcriptReference : Measure (Data T))
    [IsProbabilityMeasure transcriptReference]
    (hreference : ∀ y, 0 <
      (((estimator.kernel.map decode) ∘ₘ transcriptReference).real {y}))
    (a : Fin N)
    (hfinite :
      klDiv (design.experimentKernel (stateOf a))
        transcriptReference ≠ ∞) :
    ∑ y,
      (decodedEstimateKernel design estimator stateOf hstate
        decode hdecode a).real {y} *
        Real.log
          ((decodedEstimateKernel design estimator stateOf hstate
            decode hdecode a).real {y} /
            ((estimator.kernel.map decode) ∘ₘ
              transcriptReference).real {y}) ≤
      (klDiv (design.experimentKernel (stateOf a))
        transcriptReference).toReal := by
  let decoderEstimator : Kernel (Data T) (Fin N) :=
    estimator.kernel.map decode
  letI : IsMarkovKernel decoderEstimator :=
    Kernel.IsMarkovKernel.map estimator.kernel hdecode
  have hdecoded :
      decodedEstimateKernel design estimator stateOf hstate decode hdecode a =
        decoderEstimator ∘ₘ design.experimentKernel (stateOf a) := by
    simpa [decoderEstimator] using
      decodedEstimateKernel_apply_eq_decoderEstimator_comp_transcript
        design estimator stateOf hstate decode hdecode a
  rw [hdecoded]
  rw [← toReal_klDiv_eq_sum_measureReal_mul_log_div
    (decoderEstimator ∘ₘ design.experimentKernel (stateOf a))
    (decoderEstimator ∘ₘ transcriptReference)
    (by simpa [decoderEstimator] using hreference)]
  exact ENNReal.toReal_mono hfinite
    (klDiv_comp_right_le
      (design.experimentKernel (stateOf a)) transcriptReference
        decoderEstimator)

/-- A uniform raw-transcript reference KL bound supplies the complete
posterior-information premise for the finite decoded physical experiment. -/
theorem finiteDecodedJoint_posteriorKLSum_le_of_transcriptReferenceKL
    {D T N : ℕ} [NeZero N]
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (transcriptReference : Measure (Data T))
    [IsProbabilityMeasure transcriptReference]
    (hreference : ∀ y, 0 <
      (((estimator.kernel.map decode) ∘ₘ transcriptReference).real {y}))
    (information : ℝ)
    (hfinite : ∀ a,
      klDiv (design.experimentKernel (stateOf a))
        transcriptReference ≠ ∞)
    (hraw : ∀ a,
      (klDiv (design.experimentKernel (stateOf a))
        transcriptReference).toReal ≤ information) :
    (finiteDecodedJoint design estimator stateOf hstate decode hdecode).posteriorKLSum ≤
      information := by
  let decoderEstimator : Kernel (Data T) (Fin N) :=
    estimator.kernel.map decode
  letI : IsMarkovKernel decoderEstimator :=
    Kernel.IsMarkovKernel.map estimator.kernel hdecode
  letI : IsProbabilityMeasure
      (decoderEstimator ∘ₘ transcriptReference) := by infer_instance
  apply finiteDecodedJoint_posteriorKLSum_le_of_reference
    design estimator stateOf decode hdecode
    (fun y ↦ (decoderEstimator ∘ₘ transcriptReference).real {y})
    (by simpa [decoderEstimator] using hreference)
    (by
      simpa using
        (sum_measureReal_singleton
          (μ := decoderEstimator ∘ₘ transcriptReference)
          (Finset.univ : Finset (Fin N))))
    information
  intro a
  exact
    (decodedEstimateKernel_referenceLikelihoodSum_le_transcriptKL
      design estimator stateOf hstate decode hdecode transcriptReference
        hreference a (hfinite a)).trans (hraw a)

end PhysicalRisk

end TomographyOracleCore
