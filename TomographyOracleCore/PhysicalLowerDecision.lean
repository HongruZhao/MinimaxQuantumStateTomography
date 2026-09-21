import TomographyOracleCore.PhysicalRisk

namespace TomographyOracleCore

open scoped BigOperators ENNReal
open MatrixReduction

namespace PhysicalRisk

/-!
# Finite hard-family reduction for the physical minimax risk

This file proves only decision-theoretic order facts.  A lower bound on the
uniform average risk of any finite family contained in the decay class lifts
first to the class supremum, then through the estimator and design infima to
the unrestricted physical minimax risk.  No packing or information estimate
is assumed or asserted here.
-/

/-- Uniform finite average of the physical statewise risks. -/
noncomputable def finiteAverageTraceRisk
    {Label : Type*} [Fintype Label]
    {D T : ℕ} (design : Design D T) (estimator : Estimator D T)
    (stateOf : Label → DensityOperator (Fin D)) : ENNReal :=
  (Fintype.card Label : ENNReal)⁻¹ *
    ∑ a, statewiseExpectedTraceRisk design estimator (stateOf a)

/-- A finite uniform average over states in the class is bounded by the
class worst-case risk. -/
theorem finiteAverageTraceRisk_le_classWorstCaseRisk
    {Label : Type*} [Fintype Label] [Nonempty Label]
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Label → DensityOperator (Fin D))
    (hmembership : ∀ a, stateOf a ∈ spectralDecayClass D alpha L) :
    finiteAverageTraceRisk design estimator stateOf ≤
      classWorstCaseRisk D T alpha L design estimator := by
  let worst : ENNReal := classWorstCaseRisk D T alpha L design estimator
  have hpoint (a : Label) :
      statewiseExpectedTraceRisk design estimator (stateOf a) ≤ worst := by
    exact statewiseExpectedTraceRisk_le_classWorstCaseRisk
      design estimator (stateOf a) (hmembership a)
  have hsum :
      (∑ a, statewiseExpectedTraceRisk design estimator (stateOf a)) ≤
        ∑ _a : Label, worst :=
    Finset.sum_le_sum fun a _ha ↦ hpoint a
  have hcard0 : (Fintype.card Label : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hcardtop : (Fintype.card Label : ENNReal) ≠ ⊤ := by simp
  unfold finiteAverageTraceRisk
  calc
    (Fintype.card Label : ENNReal)⁻¹ *
        ∑ a, statewiseExpectedTraceRisk design estimator (stateOf a) ≤
      (Fintype.card Label : ENNReal)⁻¹ * ∑ _a : Label, worst :=
        mul_le_mul' le_rfl hsum
    _ = (Fintype.card Label : ENNReal)⁻¹ *
        ((Fintype.card Label : ENNReal) * worst) := by
      simp [nsmul_eq_mul]
    _ = worst := ENNReal.inv_mul_cancel_left hcard0 hcardtop

/-- A uniform finite-family lower bound for every estimator of one design
lifts to the fixed-design minimax risk. -/
theorem le_fixedDesignRisk_of_forall_estimator_finiteAverage
    {Label : Type*} [Fintype Label] [Nonempty Label]
    {D T : ℕ} {alpha L : ℝ}
    (design : Design D T) (stateOf : Label → DensityOperator (Fin D))
    (hmembership : ∀ a, stateOf a ∈ spectralDecayClass D alpha L)
    (lower : ENNReal)
    (hlower : ∀ estimator : Estimator D T,
      lower ≤ finiteAverageTraceRisk design estimator stateOf) :
    lower ≤ fixedDesignRisk D T alpha L design := by
  unfold fixedDesignRisk
  refine le_iInf fun estimator ↦ ?_
  exact (hlower estimator).trans
    (finiteAverageTraceRisk_le_classWorstCaseRisk
      design estimator stateOf hmembership)

/-- If every physical design admits a finite in-class hard family whose
uniform average defeats every estimator, the same lower bound holds for the
unrestricted minimax risk.  The family may depend on the design, as in the
shared-public-randomness Grassmann construction used by the manuscript. -/
theorem le_unrestrictedRisk_of_designwise_finiteAverage
    {Label : Type*} [Fintype Label] [Nonempty Label]
    {D T : ℕ} {alpha L : ℝ} (lower : ENNReal)
    (hlower : ∀ design : Design D T,
      ∃ stateOf : Label → DensityOperator (Fin D),
        (∀ a, stateOf a ∈ spectralDecayClass D alpha L) ∧
        ∀ estimator : Estimator D T,
          lower ≤ finiteAverageTraceRisk design estimator stateOf) :
    lower ≤ unrestrictedRisk D T alpha L := by
  unfold unrestrictedRisk
  refine le_iInf fun design ↦ ?_
  rcases hlower design with ⟨stateOf, hmembership, havg⟩
  exact le_fixedDesignRisk_of_forall_estimator_finiteAverage
    design stateOf hmembership lower havg

/-- Direct order-theoretic lift when a class-risk lower bound has already
been proved separately for every design-estimator pair. -/
theorem le_unrestrictedRisk_of_forall_design_estimator
    {D T : ℕ} {alpha L : ℝ} (lower : ENNReal)
    (hlower : ∀ (design : Design D T) (estimator : Estimator D T),
      lower ≤ classWorstCaseRisk D T alpha L design estimator) :
    lower ≤ unrestrictedRisk D T alpha L := by
  unfold unrestrictedRisk fixedDesignRisk
  exact le_iInf fun design ↦ le_iInf fun estimator ↦ hlower design estimator

/-- Correct quantifier order for hard families extracted by averaging over a
hidden orientation.  The finite family may depend on both the fixed design
and the estimator, because the minimax class supremum is taken inside the
estimator infimum.  This is the order used by the manuscript's deterministic
orientation extraction. -/
theorem le_unrestrictedRisk_of_procedurewise_finiteAverage
    {D T : ℕ} {alpha L : ℝ} (lower : ENNReal)
    (hlower : ∀ (design : Design D T) (estimator : Estimator D T),
      ∃ N : ℕ, 1 ≤ N ∧
        ∃ stateOf : Fin N → DensityOperator (Fin D),
          (∀ a, stateOf a ∈ spectralDecayClass D alpha L) ∧
          lower ≤ finiteAverageTraceRisk design estimator stateOf) :
    lower ≤ unrestrictedRisk D T alpha L := by
  unfold unrestrictedRisk fixedDesignRisk
  refine le_iInf fun design ↦ le_iInf fun estimator ↦ ?_
  rcases hlower design estimator with
    ⟨N, hN, stateOf, hmembership, havg⟩
  letI : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  exact havg.trans
    (finiteAverageTraceRisk_le_classWorstCaseRisk
      design estimator stateOf hmembership)

end PhysicalRisk

end TomographyOracleCore
