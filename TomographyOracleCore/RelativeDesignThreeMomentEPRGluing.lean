import TomographyOracleCore.RelativeDesignTwoUnitaryGluing
import TomographyOracleCore.ProjectiveHaarThirdMoments

namespace TomographyOracleCore

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-!
# The order-three permutation-Gram estimate in reference gluing

This module isolates the finite-dimensional estimate in
Schuster--Haferkamp--Huang, Lemma 8, Eqs. (B.26)--(B.27), at moment order
three.  It does not assume a design theorem or a reference-channel
comparison.  The coefficients below are the normalized Gram entries of the
six permutation operators on a three-fold tensor power.
-/

/-- The total number of cycles of a permutation of `Fin 3`.  The three
displayed swaps have two cycles, the identity has three, and the remaining
two permutations are three-cycles.  This concrete order-three definition
avoids any choice of a cycle decomposition. -/
def finThreeFullCycleCount (pi : Equiv.Perm (Fin 3)) : ℕ :=
  if pi = 1 then 3
  else if pi = Equiv.swap 0 1 ∨ pi = Equiv.swap 0 2 ∨
      pi = Equiv.swap 1 2 then 2
  else 1

/-- The normalized order-three permutation Gram entry
`D⁻³ Tr(σ τ⁻¹) = D^(#cycles(σ τ⁻¹)-3)`. -/
def normalizedPermutationGramThree (D : ℕ)
    (sigma tau : Equiv.Perm (Fin 3)) : ℝ :=
  (D : ℝ) ^ finThreeFullCycleCount (sigma * tau⁻¹) / (D : ℝ) ^ 3

/-- Difference between the normalized Gram entry and the Kronecker delta. -/
def permutationGramDeltaErrorThree (D : ℕ)
    (sigma tau : Equiv.Perm (Fin 3)) : ℝ :=
  normalizedPermutationGramThree D sigma tau -
    if sigma = tau then 1 else 0

@[simp] theorem finThreeFullCycleCount_one :
    finThreeFullCycleCount (1 : Equiv.Perm (Fin 3)) = 3 := by
  simp [finThreeFullCycleCount]

set_option maxHeartbeats 1200000 in
/-- The exact sum of the normalized Gram entries at order three. -/
theorem sum_normalizedPermutationGramThree_eq
    (D : ℕ) (hD : 0 < D) :
    (∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        normalizedPermutationGramThree D sigma tau) =
      6 + 18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 := by
  simp +decide [finThreePerm_univ_explicit,
    normalizedPermutationGramThree, finThreeFullCycleCount,
    finThreeCycleForward, finThreeCycleBackward]
  field_simp
  ring

/-- The sum of the Kronecker-delta entries over the six-by-six Gram matrix. -/
theorem sum_finThreePermutation_eqIndicator :
    (∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        if sigma = tau then (1 : ℝ) else 0) = 6 := by
  simp
  norm_num [Fintype.card_perm]

set_option maxHeartbeats 1200000 in
/-- At order three, summing the normalized Gram defect over all ordered
pairs gives exactly `18 / D + 12 / D²`. -/
theorem sum_permutationGramDeltaErrorThree_eq
    (D : ℕ) (hD : 0 < D) :
    (∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        permutationGramDeltaErrorThree D sigma tau) =
      18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 := by
  simp_rw [permutationGramDeltaErrorThree, Finset.sum_sub_distrib]
  rw [sum_normalizedPermutationGramThree_eq D hD,
    sum_finThreePermutation_eqIndicator]
  ring

/-- Every order-three normalized Gram defect is nonnegative. -/
theorem permutationGramDeltaErrorThree_nonneg
    (D : ℕ) (hD : 0 < D)
    (sigma tau : Equiv.Perm (Fin 3)) :
    0 ≤ permutationGramDeltaErrorThree D sigma tau := by
  have hDreal : (0 : ℝ) < D := by exact_mod_cast hD
  by_cases hst : sigma = tau
  · subst tau
    simp [permutationGramDeltaErrorThree,
      normalizedPermutationGramThree, finThreeFullCycleCount, hDreal.ne']
  · have hprod : sigma * tau⁻¹ ≠ 1 := by
      simpa [mul_inv_eq_one] using hst
    simp only [permutationGramDeltaErrorThree, hst, if_false, sub_zero,
      normalizedPermutationGramThree, finThreeFullCycleCount, hprod]
    split_ifs <;> positivity

/-- The matrix-valued Gram defect appearing in Eq. (B.26), abstracting only
the norm-one permutation-tensor matrices.  The definition is an explicit
finite weighted sum, not a premise encoding a desired channel comparison. -/
def permutationGramWeightedErrorThree
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → E) : E :=
  ∑ sigma : Equiv.Perm (Fin 3),
    ∑ tau : Equiv.Perm (Fin 3),
      (permutationGramDeltaErrorThree D sigma tau : ℂ) • Q sigma tau

/-- Operator-norm triangle estimate for the concrete order-three Gram
defect.  It applies in particular when `E` is a finite complex matrix space
with the `L2Operator` norm and each `Q σ τ` is a permutation tensor. -/
theorem norm_permutationGramWeightedErrorThree_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (D : ℕ) (hD : 0 < D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → E)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1) :
    ‖permutationGramWeightedErrorThree D Q‖ ≤
      18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 := by
  calc
    ‖permutationGramWeightedErrorThree D Q‖ ≤
        ∑ sigma : Equiv.Perm (Fin 3),
          ∑ tau : Equiv.Perm (Fin 3),
            ‖(permutationGramDeltaErrorThree D sigma tau : ℂ) •
              Q sigma tau‖ := by
      unfold permutationGramWeightedErrorThree
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun sigma _ ↦ norm_sum_le _ _)
    _ ≤ ∑ sigma : Equiv.Perm (Fin 3),
          ∑ tau : Equiv.Perm (Fin 3),
            permutationGramDeltaErrorThree D sigma tau := by
      apply Finset.sum_le_sum
      intro sigma _
      apply Finset.sum_le_sum
      intro tau _
      rw [norm_smul]
      have hcoeff := permutationGramDeltaErrorThree_nonneg D hD sigma tau
      have hnorm :
          ‖(permutationGramDeltaErrorThree D sigma tau : ℂ)‖ =
            permutationGramDeltaErrorThree D sigma tau := by
        simpa using abs_of_nonneg hcoeff
      rw [hnorm]
      exact mul_le_of_le_one_right hcoeff (hQ sigma tau)
    _ = 18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 :=
      sum_permutationGramDeltaErrorThree_eq D hD

/-- The rational order-three Gram defect is bounded by the exponential
factor used in Schuster--Haferkamp--Huang Eq. (B.27). -/
theorem permutationGramDeltaErrorThree_le_exp
    (D : ℕ) (hD : 2 ≤ D) :
    18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 ≤
      6 * (Real.exp (9 / (2 * (D : ℝ))) - 1) := by
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le (by norm_num) hDreal
  have hrat :
      18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 ≤ 27 / (D : ℝ) := by
    field_simp
    nlinarith
  have hx : (0 : ℝ) ≤ 9 / (2 * (D : ℝ)) := by positivity
  have hexp := Real.add_one_le_exp (9 / (2 * (D : ℝ)))
  calc
    18 / (D : ℝ) + 12 / (D : ℝ) ^ 2 ≤ 27 / (D : ℝ) := hrat
    _ = 6 * (9 / (2 * (D : ℝ))) := by field_simp; ring
    _ ≤ 6 * (Real.exp (9 / (2 * (D : ℝ))) - 1) := by nlinarith

/-- Order-three specialization of Eq. (B.27): the EPR error, including the
global normalization `Dglobal⁻⁶`, is controlled by the published exponential
overlap factor. -/
theorem norm_scaled_permutationGramWeightedErrorThree_le_exp
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (Dglobal Doverlap : ℕ) (hglobal : 0 < Dglobal) (hoverlap : 2 ≤ Doverlap)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → E)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1) :
    ‖(((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap Q‖ ≤
      ((Dglobal : ℝ) ^ 6)⁻¹ *
        (6 * (Real.exp (9 / (2 * (Doverlap : ℝ))) - 1)) := by
  have hDoverlap : 0 < Doverlap := lt_of_lt_of_le (by omega) hoverlap
  have hDglobalReal : (0 : ℝ) < Dglobal := by exact_mod_cast hglobal
  rw [norm_smul]
  have hnorm : ‖(((Dglobal : ℝ) ^ 6)⁻¹ : ℂ)‖ =
      ((Dglobal : ℝ) ^ 6)⁻¹ := by
    simp [abs_of_pos hDglobalReal]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (norm_permutationGramWeightedErrorThree_le Doverlap hDoverlap Q hQ).trans
    (permutationGramDeltaErrorThree_le_exp Doverlap hoverlap)

/-- Fully concrete finite-matrix form of the order-three EPR/permutation
estimate.  Any family of permutation tensors is represented by permutations
of a finite tensor-product basis; their `L2Operator` norms are at most one. -/
theorem norm_scaled_permutationMatrixGramWeightedErrorThree_le_exp
    {J : Type*} [Fintype J] [DecidableEq J]
    (Dglobal Doverlap : ℕ) (hglobal : 0 < Dglobal) (hoverlap : 2 ≤ Doverlap)
    (R : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → Equiv.Perm J) :
    ‖(((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap
          (fun sigma tau ↦ (R sigma tau).permMatrix ℂ)‖ ≤
      ((Dglobal : ℝ) ^ 6)⁻¹ *
        (6 * (Real.exp (9 / (2 * (Doverlap : ℝ))) - 1)) := by
  exact norm_scaled_permutationGramWeightedErrorThree_le_exp
    Dglobal Doverlap hglobal hoverlap
    (fun sigma tau ↦ (R sigma tau).permMatrix ℂ)
    (fun sigma tau ↦ Matrix.permMatrix_l2_opNorm_le (R sigma tau))

end

end TomographyOracleCore
