import TomographyOracleCore.PhysicalPOVM
import TomographyOracleCore.ExactTargets

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction
open scoped ENNReal

/-!
# Physical trace-risk semantics

This module defines the decision-theoretic quantities in the manuscript for
the physical randomized nonadaptive experiment.  Both the public seed and
each one-copy outcome use `ℝ` as a universal standard-Borel coding space.

The definitions below contain no oracle inequality, packing assertion,
information bound, or minimax conclusion.  The only ordering lemmas are the
formal consequences of taking suprema over states and infima over estimators
and designs.
-/

namespace PhysicalRisk

/-- The data revealed to an estimator: the public seed and the `T` coded
one-copy outcomes. -/
abbrev Data (T : ℕ) := ℝ × (Fin T → ℝ)

/-- A physical randomized nonadaptive design using universal real codes for
both its public seed and one-copy outcomes. -/
abbrev Design (D T : ℕ) :=
  PhysicalPOVM.RandomizedNonadaptiveDesign D T ℝ ℝ

/-- A randomized physical estimator is a Markov kernel from all observed data
to a density operator. -/
structure Estimator (D T : ℕ) where
  kernel : Kernel (Data T) (DensityOperator (Fin D))
  markov : IsMarkovKernel kernel

namespace Estimator

instance kernel_isMarkov {D T : ℕ} (estimator : Estimator D T) :
    IsMarkovKernel estimator.kernel :=
  estimator.markov

end Estimator

/-- Hermitian trace loss between a true state and an estimated state, valued
in `ENNReal` as required by Mathlib's decision-risk API. -/
noncomputable def hermitianTraceLoss {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) : ENNReal :=
  ENNReal.ofReal
    (hermitianTraceNorm (estimate.matrix - ρ.matrix)
      (estimate.sub_isHermitian ρ))

theorem hermitianTraceLoss_nonnegative {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) :
    0 ≤ hermitianTraceLoss ρ estimate :=
  bot_le

/-- Distribution of the estimator output at a true state, obtained by
composing the estimator with the physical experiment kernel. -/
noncomputable def estimateKernel {D T : ℕ}
    (design : Design D T) (estimator : Estimator D T) :
    Kernel (DensityOperator (Fin D)) (DensityOperator (Fin D)) :=
  Kernel.comp estimator.kernel design.experimentKernel

instance estimateKernel_isMarkov {D T : ℕ}
    (design : Design D T) (estimator : Estimator D T) :
    IsMarkovKernel (estimateKernel design estimator) := by
  unfold estimateKernel
  infer_instance

/-- Expected Hermitian trace loss at one fixed true state. -/
noncomputable def statewiseExpectedTraceRisk {D T : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (ρ : DensityOperator (Fin D)) : ENNReal :=
  ∫⁻ estimate, hermitianTraceLoss ρ estimate
    ∂(estimateKernel design estimator) ρ

theorem statewiseExpectedTraceRisk_nonnegative {D T : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (ρ : DensityOperator (Fin D)) :
    0 ≤ statewiseExpectedTraceRisk design estimator ρ :=
  bot_le

/-- Worst-case expected trace risk of one design-estimator pair over the
paper's spectral-decay class. -/
noncomputable def classWorstCaseRisk
    (D T : ℕ) (alpha L : ℝ)
    (design : Design D T) (estimator : Estimator D T) : ENNReal :=
  ⨆ ρ : {state : DensityOperator (Fin D) //
      state ∈ spectralDecayClass D alpha L},
    statewiseExpectedTraceRisk design estimator ρ.1

/-- Fixed-design minimax risk: the infimum of the class worst-case risk over
all randomized physical estimators. -/
noncomputable def fixedDesignRisk
    (D T : ℕ) (alpha L : ℝ) (design : Design D T) : ENNReal :=
  ⨅ estimator : Estimator D T,
    classWorstCaseRisk D T alpha L design estimator

/-- Unrestricted physical minimax risk: the infimum of the fixed-design risk
over all randomized nonadaptive one-copy designs. -/
noncomputable def unrestrictedRisk
    (D T : ℕ) (alpha L : ℝ) : ENNReal :=
  ⨅ design : Design D T,
    fixedDesignRisk D T alpha L design

theorem statewiseExpectedTraceRisk_le_classWorstCaseRisk
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (estimator : Estimator D T)
    (ρ : DensityOperator (Fin D))
    (hρ : ρ ∈ spectralDecayClass D alpha L) :
    statewiseExpectedTraceRisk design estimator ρ ≤
      classWorstCaseRisk D T alpha L design estimator := by
  exact le_iSup
    (fun state : {state : DensityOperator (Fin D) //
      state ∈ spectralDecayClass D alpha L} ↦
        statewiseExpectedTraceRisk design estimator state.1)
    ⟨ρ, hρ⟩

theorem fixedDesignRisk_le_estimator
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (estimator : Estimator D T) :
    fixedDesignRisk D T alpha L design ≤
      classWorstCaseRisk D T alpha L design estimator := by
  exact iInf_le _ estimator

theorem unrestrictedRisk_le_fixedDesignRisk
    {D T : ℕ} {alpha L : ℝ} (design : Design D T) :
    unrestrictedRisk D T alpha L ≤
      fixedDesignRisk D T alpha L design := by
  exact iInf_le _ design

theorem classWorstCaseRisk_nonnegative
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (estimator : Estimator D T) :
    0 ≤ classWorstCaseRisk D T alpha L design estimator :=
  bot_le

theorem fixedDesignRisk_nonnegative
    {D T : ℕ} {alpha L : ℝ} (design : Design D T) :
    0 ≤ fixedDesignRisk D T alpha L design :=
  bot_le

theorem unrestrictedRisk_nonnegative
    {D T : ℕ} {alpha L : ℝ} :
    0 ≤ unrestrictedRisk D T alpha L :=
  bot_le

end PhysicalRisk

end TomographyOracleCore
