import TomographyOracleCore.FiniteKLFormula
import TomographyOracleCore.PhysicalFiniteInformation

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open MatrixReduction
open scoped BigOperators ENNReal

namespace PhysicalRisk

/-!
# Raw-output KL controls decoded physical information

The physical Fano experiment first produces a density-operator-valued
estimator output and then applies a measurable finite decoder.  This file
uses deterministic data processing to bound every explicit decoded
reference likelihood sum by the KL divergence of the undecoded estimator
output law from an arbitrary raw reference probability law.

No declaration in this file is an axiom.
-/

/-- The decoded kernel at one hard-state label is exactly the map of the raw
estimator-output law through the decoder. -/
theorem decodedEstimateKernel_apply_eq_map
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) (a : Fin N) :
    decodedEstimateKernel design estimator stateOf hstate decode hdecode a =
      (estimateKernel design estimator (stateOf a)).map decode := by
  rw [decodedEstimateKernel, Kernel.map_apply _ hdecode,
    Kernel.comap_apply]

/-- Every explicit decoded likelihood sum is bounded by the real KL of the
undecoded physical estimator-output law. -/
theorem decodedEstimateKernel_referenceLikelihoodSum_le_rawKL
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (reference : Measure (DensityOperator (Fin D)))
    [IsProbabilityMeasure reference]
    (hreference : ∀ y, 0 < (reference.map decode).real {y})
    (a : Fin N)
    (hfinite :
      klDiv (estimateKernel design estimator (stateOf a)) reference ≠ ∞) :
    ∑ y,
      ((decodedEstimateKernel design estimator stateOf hstate
        decode hdecode) a).real {y} *
        Real.log
          (((decodedEstimateKernel design estimator stateOf hstate
            decode hdecode) a).real {y} /
              (reference.map decode).real {y}) ≤
      (klDiv (estimateKernel design estimator (stateOf a))
        reference).toReal := by
  rw [decodedEstimateKernel_apply_eq_map design estimator stateOf hstate
    decode hdecode a]
  exact sum_mapped_measureReal_mul_log_div_le_toReal_klDiv
    (estimateKernel design estimator (stateOf a)) reference
      decode hdecode hreference hfinite

/-- A uniform raw-output KL bound implies the posterior-information premise
for the finite decoded physical experiment. -/
theorem finiteDecodedJoint_posteriorKLSum_le_of_rawReferenceKL
    {D T N : ℕ} [NeZero N]
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (reference : Measure (DensityOperator (Fin D)))
    [IsProbabilityMeasure reference]
    (hreference : ∀ y, 0 < (reference.map decode).real {y})
    (information : ℝ)
    (hfinite : ∀ a,
      klDiv (estimateKernel design estimator (stateOf a)) reference ≠ ∞)
    (hraw : ∀ a,
      (klDiv (estimateKernel design estimator (stateOf a))
        reference).toReal ≤ information) :
    (finiteDecodedJoint design estimator stateOf hstate decode hdecode).posteriorKLSum ≤
      information := by
  letI : IsProbabilityMeasure (reference.map decode) :=
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  apply finiteDecodedJoint_posteriorKLSum_le_of_reference
    design estimator stateOf decode hdecode
    (fun y ↦ (reference.map decode).real {y}) hreference
      (by
        simpa using
          (sum_measureReal_singleton
            (μ := reference.map decode) (Finset.univ : Finset (Fin N))))
    information
  intro a
  exact
    (decodedEstimateKernel_referenceLikelihoodSum_le_rawKL
      design estimator stateOf hstate decode hdecode reference
        hreference a (hfinite a)).trans (hraw a)

end PhysicalRisk

end TomographyOracleCore
