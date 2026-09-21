import TomographyOracleCore.ChoKimOverlapCycle
import TomographyOracleCore.RelativeDesignOrder

namespace TomographyOracleCore

/-!
# Iterating the two-unitary relative-design gluing loss

The analytic Schuster--Haferkamp--Huang two-unitary lemma supplies one
multiplicative recurrence each time a new gate vertex is glued along a
spanning tree.  This module proves the complete iteration and specializes it
to the periodic Cho--Kim overlap cycle.

Thus the remaining analytic input is one local recurrence, not an already
assembled global design statement.
-/

/-- Iterating a multiplicative one-step error recurrence gives the exact
product bound `1 + error r ≤ (1 + localLoss)^r`. -/
theorem one_add_error_le_pow_of_pairwise_gluing
    {r : ℕ} {localLoss : ℝ} (hloss : 0 ≤ localLoss)
    (error : ℕ → ℝ) (hinitial : error 0 ≤ 0)
    (hstep : ∀ i < r,
      1 + error (i + 1) ≤ (1 + error i) * (1 + localLoss)) :
    1 + error r ≤ (1 + localLoss) ^ r := by
  have hbase : 1 + error 0 ≤ (1 + localLoss) ^ 0 := by
    simpa using add_le_add_left hinitial 1
  induction r with
  | zero => exact hbase
  | succ r ihr =>
      have hprevious : 1 + error r ≤ (1 + localLoss) ^ r := by
        apply ihr
        intro i hi
        exact hstep i (hi.trans (Nat.lt_succ_self r))
      calc
        1 + error (r + 1) ≤
            (1 + error r) * (1 + localLoss) := hstep r (Nat.lt_succ_self r)
        _ ≤ (1 + localLoss) ^ r * (1 + localLoss) :=
          mul_le_mul_of_nonneg_right hprevious (by linarith)
        _ = (1 + localLoss) ^ (r + 1) := by rw [pow_succ]

/-- Subtracted form of the same exact iteration. -/
theorem error_le_pow_sub_one_of_pairwise_gluing
    {r : ℕ} {localLoss : ℝ} (hloss : 0 ≤ localLoss)
    (error : ℕ → ℝ) (hinitial : error 0 ≤ 0)
    (hstep : ∀ i < r,
      1 + error (i + 1) ≤ (1 + error i) * (1 + localLoss)) :
    error r ≤ (1 + localLoss) ^ r - 1 := by
  have h := one_add_error_le_pow_of_pairwise_gluing hloss error hinitial hstep
  linarith

/-- Periodic Cho--Kim specialization: a pairwise gluing recurrence along the
`2(n/K)-1` spanning-tree edges already forces the final relative error below
one under the explicit block condition. -/
theorem ChoKimBlockCondition.relativeDesignError_le_one_of_pairwise_gluing
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (error : ℕ → ℝ) (hinitial : error 0 ≤ 0)
    (hstep : ∀ i < choKimGateVertices n K - 1,
      1 + error (i + 1) ≤
        (1 + error i) *
          (1 + choKimFThree (choKimOverlapDimension K))) :
    error (choKimGateVertices n K - 1) ≤ 1 := by
  apply h.relativeDesignError_le_one_of_raw_gluing hn
  apply error_le_pow_sub_one_of_pairwise_gluing
  · exact choKimFThree_nonneg (h.eighteen_le_overlap hn)
  · exact hinitial
  · exact hstep

/-- Typed relative-CP endpoint of the gluing iteration.  The hypothesis
`hfinalDesign` is what the analytic two-unitary gluing lemma produces after
the local recurrences have been assembled; the error threshold is proved
here from the concrete periodic geometry and constants. -/
theorem ChoKimBlockCondition.relativeCPApproximation_error_le_one_of_pairwise_gluing
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (ensemble haar : A →ₗ[ℂ] A)
    (error : ℕ → ℝ) (hinitial : error 0 ≤ 0)
    (hstep : ∀ i < choKimGateVertices n K - 1,
      1 + error (i + 1) ≤
        (1 + error i) *
          (1 + choKimFThree (choKimOverlapDimension K)))
    (hfinalDesign : RelativeCPApproximation
      (error (choKimGateVertices n K - 1)) ensemble haar) :
    ∃ epsilon : ℝ,
      epsilon ≤ 1 ∧ RelativeCPApproximation epsilon ensemble haar := by
  exact ⟨error (choKimGateVertices n K - 1),
    h.relativeDesignError_le_one_of_pairwise_gluing hn error hinitial hstep,
    hfinalDesign⟩

end TomographyOracleCore
