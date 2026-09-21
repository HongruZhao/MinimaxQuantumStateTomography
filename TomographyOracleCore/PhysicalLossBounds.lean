import TomographyOracleCore.PhysicalRisk
import TomographyOracleCore.DensityGrid

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction
open scoped ENNReal

/-!
# Boundedness of the physical Hermitian trace risk

The trace distance between density operators is deterministically at most
two.  This file transfers the existing real-valued matrix theorem to the
`ENNReal` loss and then through the physical Markov experiment, state-class
supremum, and estimator/design infima.
-/

namespace PhysicalRisk

/-- Physical Hermitian trace loss is at most two pointwise. -/
theorem hermitianTraceLoss_le_two {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) :
    hermitianTraceLoss ρ estimate ≤ 2 := by
  unfold hermitianTraceLoss
  rw [← ENNReal.ofReal_ofNat]
  exact ENNReal.ofReal_le_ofReal
    (density_hermitianTraceNorm_sub_le_two estimate ρ)

/-- Physical Hermitian trace loss is always finite. -/
theorem hermitianTraceLoss_lt_top {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) :
    hermitianTraceLoss ρ estimate < ∞ := by
  exact (hermitianTraceLoss_le_two ρ estimate).trans_lt (by norm_num)

theorem hermitianTraceLoss_ne_top {D : ℕ}
    (ρ estimate : DensityOperator (Fin D)) :
    hermitianTraceLoss ρ estimate ≠ ∞ :=
  (hermitianTraceLoss_lt_top ρ estimate).ne

/-- A constant randomized estimator, represented as a deterministic Markov
kernel.  It is used only to witness that the estimator infimum is nonempty. -/
noncomputable def constantEstimator {D T : ℕ}
    (anchor : DensityOperator (Fin D)) : Estimator D T where
  kernel := Kernel.deterministic (fun _ : Data T ↦ anchor) measurable_const
  markov := by infer_instance

/-- Every statewise expected physical trace risk is at most two. -/
theorem statewiseExpectedTraceRisk_le_two {D T : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (ρ : DensityOperator (Fin D)) :
    statewiseExpectedTraceRisk design estimator ρ ≤ 2 := by
  unfold statewiseExpectedTraceRisk
  calc
    (∫⁻ estimate, hermitianTraceLoss ρ estimate
        ∂(estimateKernel design estimator) ρ) ≤
        ∫⁻ _estimate, (2 : ENNReal)
          ∂(estimateKernel design estimator) ρ := by
      exact lintegral_mono fun estimate ↦ hermitianTraceLoss_le_two ρ estimate
    _ = 2 := by simp

theorem statewiseExpectedTraceRisk_lt_top {D T : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (ρ : DensityOperator (Fin D)) :
    statewiseExpectedTraceRisk design estimator ρ < ∞ :=
  (statewiseExpectedTraceRisk_le_two design estimator ρ).trans_lt (by norm_num)

/-- The class supremum remains bounded by the deterministic loss cap. -/
theorem classWorstCaseRisk_le_two
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (estimator : Estimator D T) :
    classWorstCaseRisk D T alpha L design estimator ≤ 2 := by
  unfold classWorstCaseRisk
  refine iSup_le fun state ↦ ?_
  exact statewiseExpectedTraceRisk_le_two design estimator state.1

theorem classWorstCaseRisk_lt_top
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (estimator : Estimator D T) :
    classWorstCaseRisk D T alpha L design estimator < ∞ :=
  (classWorstCaseRisk_le_two design estimator).trans_lt (by norm_num)

/-- The fixed-design estimator infimum is at most two.  The positive physical
dimension stored in the design supplies a computational-basis anchor state. -/
theorem fixedDesignRisk_le_two
    {D T : ℕ} {alpha L : ℝ} (design : Design D T) :
    fixedDesignRisk D T alpha L design ≤ 2 := by
  let i₀ : Fin D := ⟨0, design.dimension_pos⟩
  let anchor : DensityOperator (Fin D) := DensityGrid.basisDensityOperator i₀
  calc
    fixedDesignRisk D T alpha L design ≤
        classWorstCaseRisk D T alpha L design (constantEstimator anchor) :=
      fixedDesignRisk_le_estimator design (constantEstimator anchor)
    _ ≤ 2 := classWorstCaseRisk_le_two design (constantEstimator anchor)

theorem fixedDesignRisk_lt_top
    {D T : ℕ} {alpha L : ℝ} (design : Design D T) :
    fixedDesignRisk D T alpha L design < ∞ :=
  (fixedDesignRisk_le_two design).trans_lt (by norm_num)

/-- Once one admissible physical design is supplied, the unrestricted design
infimum is also bounded by two. -/
theorem unrestrictedRisk_le_two
    {D T : ℕ} {alpha L : ℝ} (design : Design D T) :
    unrestrictedRisk D T alpha L ≤ 2 :=
  (unrestrictedRisk_le_fixedDesignRisk design).trans
    (fixedDesignRisk_le_two design)

theorem unrestrictedRisk_lt_top
    {D T : ℕ} {alpha L : ℝ} (design : Design D T) :
    unrestrictedRisk D T alpha L < ∞ :=
  (unrestrictedRisk_le_two design).trans_lt (by norm_num)

end PhysicalRisk

end TomographyOracleCore
