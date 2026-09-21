import TomographyOracleCore.FiniteInformationRadius
import TomographyOracleCore.PhysicalFiniteFanoKernel

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction
open scoped BigOperators ENNReal

namespace PhysicalRisk

/-!
# Physical finite Fano from reference likelihood bounds

This module composes the internally proved finite information-radius identity
with the physical estimator kernel and the finite Fano-to-risk bridge.  The
posterior-information premise is replaced by explicit per-state likelihood
sums relative to one positive finite reference law.
-/

/-- A concrete per-state finite-alphabet likelihood-radius bound implies the
posterior information bound for the decoded physical experiment. -/
theorem finiteDecodedJoint_posteriorKLSum_le_of_reference
    {D T N : ℕ} [NeZero N]
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (q : Fin N → ℝ) (hq : ∀ y, 0 < q y)
    (hqsum : ∑ y, q y = 1)
    (information : ℝ)
    (hlabel : ∀ a, ∑ y,
      ((decodedEstimateKernel design estimator stateOf
        Measurable.of_discrete decode hdecode) a).real {y} *
          Real.log
            (((decodedEstimateKernel design estimator stateOf
              Measurable.of_discrete decode hdecode) a).real {y} / q y) ≤
        information) :
    (finiteDecodedJoint design estimator stateOf Measurable.of_discrete
      decode hdecode).posteriorKLSum ≤ information := by
  exact FiniteUniformJoint.ofMarkovKernel_posteriorKLSum_le
    (decodedEstimateKernel design estimator stateOf
      Measurable.of_discrete decode hdecode)
    q hq hqsum information hlabel

/-- Complete physical finite-family lower bound from explicit decoded
reference likelihood sums.  No posterior distribution, entropy identity, or
mutual-information assertion remains among the hypotheses. -/
theorem ofReal_eleven_mul_radius_div_sixteen_le_finiteAverageTraceRisk_of_reference
    {D T N : ℕ} [NeZero N]
    (hN : 2 ≤ N)
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hforces : ∀ (a : Fin N) (σ : DensityOperator (Fin D)),
      decode σ ≠ a →
        ENNReal.ofReal radius ≤ hermitianTraceLoss (stateOf a) σ)
    (q : Fin N → ℝ) (hq : ∀ y, 0 < q y)
    (hqsum : ∑ y, q y = 1)
    (information : ℝ)
    (hlabel : ∀ a, ∑ y,
      ((decodedEstimateKernel design estimator stateOf
        Measurable.of_discrete decode hdecode) a).real {y} *
          Real.log
            (((decodedEstimateKernel design estimator stateOf
              Measurable.of_discrete decode hdecode) a).real {y} / q y) ≤
        information)
    (hinformation : information ≤ Real.log N / 16)
    (hlogTwo : 4 * Real.log 2 ≤ Real.log N) :
    ENNReal.ofReal (11 * radius / 16) ≤
      finiteAverageTraceRisk design estimator stateOf := by
  apply ofReal_eleven_mul_radius_div_sixteen_le_finiteAverageTraceRisk
    hN design estimator stateOf Measurable.of_discrete decode hdecode radius
      hradius hforces
  · exact (finiteDecodedJoint_posteriorKLSum_le_of_reference
      design estimator stateOf decode hdecode q hq hqsum information
        hlabel).trans hinformation
  · exact hlogTwo

end PhysicalRisk

end TomographyOracleCore
