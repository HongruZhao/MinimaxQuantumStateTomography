import TomographyOracleCore.RelativeDesignThreeMomentChoiGluing

namespace TomographyOracleCore

open scoped CStarAlgebra Matrix.Norms.L2Operator

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-!
# Structural identities for the order-three permutation support

This module proves the elementary finite-group facts left as structural
hypotheses in the B.26-to-relative-CP bridge.  They are stated for a concrete
two-index matrix representation `Q`; no positivity or channel comparison is
assumed.
-/

/-- Exhaustive six-element classification of `Perm (Fin 3)`. -/
theorem finThreePerm_eq_six (pi : Equiv.Perm (Fin 3)) :
    pi = 1 ∨ pi = Equiv.swap 1 2 ∨ pi = Equiv.swap 0 1 ∨
      pi = finThreeCycleForward ∨ pi = finThreeCycleBackward ∨
        pi = Equiv.swap 0 2 := by
  have hpi : pi ∈ (Finset.univ : Finset (Equiv.Perm (Fin 3))) :=
    Finset.mem_univ pi
  rw [finThreePerm_univ_explicit] at hpi
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hpi

set_option maxHeartbeats 1200000 in
/-- The concrete order-three full-cycle count is invariant under
conjugation. -/
theorem finThreeFullCycleCount_conj
    (a pi : Equiv.Perm (Fin 3)) :
    finThreeFullCycleCount (a * pi * a⁻¹) =
      finThreeFullCycleCount pi := by
  rcases finThreePerm_eq_six a with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases finThreePerm_eq_six pi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [finThreeFullCycleCount, finThreeCycleForward,
      finThreeCycleBackward, Equiv.swap_apply_def]

set_option maxHeartbeats 1200000 in
/-- The concrete order-three full-cycle count is invariant under inverse. -/
theorem finThreeFullCycleCount_inv
    (pi : Equiv.Perm (Fin 3)) :
    finThreeFullCycleCount pi⁻¹ = finThreeFullCycleCount pi := by
  rcases finThreePerm_eq_six pi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [finThreeFullCycleCount, finThreeCycleForward,
      finThreeCycleBackward, Equiv.swap_apply_def]

/-- Simultaneous left multiplication preserves the order-three Gram
defect. -/
theorem permutationGramDeltaErrorThree_left_mul
    (D : ℕ) (a sigma tau : Equiv.Perm (Fin 3)) :
    permutationGramDeltaErrorThree D (a * sigma) (a * tau) =
      permutationGramDeltaErrorThree D sigma tau := by
  unfold permutationGramDeltaErrorThree normalizedPermutationGramThree
  have hprod : (a * sigma) * (a * tau)⁻¹ =
      a * (sigma * tau⁻¹) * a⁻¹ := by group
  rw [hprod, finThreeFullCycleCount_conj]
  simp

/-- Simultaneous right multiplication preserves the order-three Gram
defect. -/
theorem permutationGramDeltaErrorThree_right_mul
    (D : ℕ) (a sigma tau : Equiv.Perm (Fin 3)) :
    permutationGramDeltaErrorThree D (sigma * a) (tau * a) =
      permutationGramDeltaErrorThree D sigma tau := by
  unfold permutationGramDeltaErrorThree normalizedPermutationGramThree
  have hprod : (sigma * a) * (tau * a)⁻¹ = sigma * tau⁻¹ := by group
  rw [hprod]
  simp

/-- Simultaneous inversion preserves the order-three Gram defect. -/
theorem permutationGramDeltaErrorThree_inv
    (D : ℕ) (sigma tau : Equiv.Perm (Fin 3)) :
    permutationGramDeltaErrorThree D sigma⁻¹ tau⁻¹ =
      permutationGramDeltaErrorThree D sigma tau := by
  unfold permutationGramDeltaErrorThree normalizedPermutationGramThree
  have hcount :
      finThreeFullCycleCount (sigma⁻¹ * (tau⁻¹)⁻¹) =
        finThreeFullCycleCount (sigma * tau⁻¹) := by
    calc
      finThreeFullCycleCount (sigma⁻¹ * (tau⁻¹)⁻¹) =
          finThreeFullCycleCount
            (sigma⁻¹ * (sigma * tau⁻¹)⁻¹ * (sigma⁻¹)⁻¹) := by
              congr 1
              group
      _ = finThreeFullCycleCount (sigma * tau⁻¹)⁻¹ :=
        finThreeFullCycleCount_conj _ _
      _ = finThreeFullCycleCount (sigma * tau⁻¹) :=
        finThreeFullCycleCount_inv _
  rw [hcount]
  simp

/-- The normalized diagonal group average is self-adjoint whenever `Q`
intertwines the star operation with simultaneous inversion. -/
theorem finiteThreeMomentReferenceProjection_isSelfAdjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹) :
    IsSelfAdjoint (finiteThreeMomentReferenceProjection Q) := by
  unfold IsSelfAdjoint finiteThreeMomentReferenceProjection
  rw [star_smul, star_sum]
  simp_rw [hstar]
  have hinv := Equiv.sum_comp
    (Equiv.inv (Equiv.Perm (Fin 3)))
    (fun sigma : Equiv.Perm (Fin 3) ↦ Q sigma sigma)
  have hinv' : (∑ sigma : Equiv.Perm (Fin 3), Q sigma⁻¹ sigma⁻¹) =
      ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma := by
    simpa using hinv
  rw [hinv']
  norm_num

/-- Each diagonal representation matrix fixes the normalized diagonal
average on the left. -/
theorem diagonalQ_mul_finiteThreeMomentReferenceProjection
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (a : Equiv.Perm (Fin 3)) :
    Q a a * finiteThreeMomentReferenceProjection Q =
      finiteThreeMomentReferenceProjection Q := by
  unfold finiteThreeMomentReferenceProjection
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [hmul]
  have hleft := Equiv.sum_comp (Equiv.mulLeft a)
    (fun sigma : Equiv.Perm (Fin 3) ↦ Q sigma sigma)
  have hleft' : (∑ sigma : Equiv.Perm (Fin 3),
      Q (a * sigma) (a * sigma)) =
        ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma := by
    simpa using hleft
  rw [hleft']

/-- The normalized diagonal group average is idempotent whenever `Q` is a
two-index representation. -/
theorem finiteThreeMomentReferenceProjection_isIdempotent
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau')) :
    finiteThreeMomentReferenceProjection Q *
        finiteThreeMomentReferenceProjection Q =
      finiteThreeMomentReferenceProjection Q := by
  change (((6 : ℂ)⁻¹ • ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma) *
      finiteThreeMomentReferenceProjection Q =
        finiteThreeMomentReferenceProjection Q)
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [diagonalQ_mul_finiteThreeMomentReferenceProjection Q hmul]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num [Fintype.card_perm, Nat.factorial]

/-- Simultaneous left translation does not change a double sum over a
finite group. -/
theorem finThree_sum_sum_mulLeft
    {M : Type*} [AddCommMonoid M]
    (a : Equiv.Perm (Fin 3))
    (f : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → M) :
    (∑ sigma, ∑ tau, f (a * sigma) (a * tau)) =
      ∑ sigma, ∑ tau, f sigma tau := by
  calc
    (∑ sigma, ∑ tau, f (a * sigma) (a * tau)) =
        ∑ sigma, ∑ tau, f (a * sigma) tau := by
      apply Fintype.sum_congr
      intro sigma
      simpa using Equiv.sum_comp (Equiv.mulLeft a)
        (fun tau : Equiv.Perm (Fin 3) ↦ f (a * sigma) tau)
    _ = ∑ sigma, ∑ tau, f sigma tau := by
      simpa using Equiv.sum_comp (Equiv.mulLeft a)
        (fun sigma : Equiv.Perm (Fin 3) ↦ ∑ tau, f sigma tau)

/-- Simultaneous right translation does not change a double sum over a
finite group. -/
theorem finThree_sum_sum_mulRight
    {M : Type*} [AddCommMonoid M]
    (a : Equiv.Perm (Fin 3))
    (f : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → M) :
    (∑ sigma, ∑ tau, f (sigma * a) (tau * a)) =
      ∑ sigma, ∑ tau, f sigma tau := by
  calc
    (∑ sigma, ∑ tau, f (sigma * a) (tau * a)) =
        ∑ sigma, ∑ tau, f (sigma * a) tau := by
      apply Fintype.sum_congr
      intro sigma
      simpa using Equiv.sum_comp (Equiv.mulRight a)
        (fun tau : Equiv.Perm (Fin 3) ↦ f (sigma * a) tau)
    _ = ∑ sigma, ∑ tau, f sigma tau := by
      simpa using Equiv.sum_comp (Equiv.mulRight a)
        (fun sigma : Equiv.Perm (Fin 3) ↦ ∑ tau, f sigma tau)

/-- Simultaneous inversion does not change a double sum over a finite
group. -/
theorem finThree_sum_sum_inv
    {M : Type*} [AddCommMonoid M]
    (f : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → M) :
    (∑ sigma, ∑ tau, f sigma⁻¹ tau⁻¹) =
      ∑ sigma, ∑ tau, f sigma tau := by
  calc
    (∑ sigma, ∑ tau, f sigma⁻¹ tau⁻¹) =
        ∑ sigma, ∑ tau, f sigma⁻¹ tau := by
      apply Fintype.sum_congr
      intro sigma
      simpa using Equiv.sum_comp
        (Equiv.inv (Equiv.Perm (Fin 3)))
        (fun tau : Equiv.Perm (Fin 3) ↦ f sigma⁻¹ tau)
    _ = ∑ sigma, ∑ tau, f sigma tau := by
      simpa using Equiv.sum_comp
        (Equiv.inv (Equiv.Perm (Fin 3)))
        (fun sigma : Equiv.Perm (Fin 3) ↦ ∑ tau, f sigma tau)

/-- Each diagonal representation matrix fixes the Gram-error sum on the
left. -/
theorem diagonalQ_mul_permutationGramWeightedErrorThree
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (a : Equiv.Perm (Fin 3)) :
    Q a a * permutationGramWeightedErrorThree D Q =
      permutationGramWeightedErrorThree D Q := by
  unfold permutationGramWeightedErrorThree
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, mul_smul_comm, hmul]
  calc
    (∑ sigma, ∑ tau,
        (permutationGramDeltaErrorThree D sigma tau : ℂ) •
          Q (a * sigma) (a * tau)) =
        ∑ sigma, ∑ tau,
          (permutationGramDeltaErrorThree D (a * sigma) (a * tau) : ℂ) •
            Q (a * sigma) (a * tau) := by
      apply Fintype.sum_congr
      intro sigma
      apply Fintype.sum_congr
      intro tau
      rw [permutationGramDeltaErrorThree_left_mul]
    _ = ∑ sigma, ∑ tau,
          (permutationGramDeltaErrorThree D sigma tau : ℂ) •
            Q sigma tau := by
      exact finThree_sum_sum_mulLeft a
        (fun sigma tau ↦
          (permutationGramDeltaErrorThree D sigma tau : ℂ) • Q sigma tau)

/-- Each diagonal representation matrix fixes the Gram-error sum on the
right. -/
theorem permutationGramWeightedErrorThree_mul_diagonalQ
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (a : Equiv.Perm (Fin 3)) :
    permutationGramWeightedErrorThree D Q * Q a a =
      permutationGramWeightedErrorThree D Q := by
  unfold permutationGramWeightedErrorThree
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_mul, smul_mul_assoc, hmul]
  calc
    (∑ sigma, ∑ tau,
        (permutationGramDeltaErrorThree D sigma tau : ℂ) •
          Q (sigma * a) (tau * a)) =
        ∑ sigma, ∑ tau,
          (permutationGramDeltaErrorThree D (sigma * a) (tau * a) : ℂ) •
            Q (sigma * a) (tau * a) := by
      apply Fintype.sum_congr
      intro sigma
      apply Fintype.sum_congr
      intro tau
      rw [permutationGramDeltaErrorThree_right_mul]
    _ = ∑ sigma, ∑ tau,
          (permutationGramDeltaErrorThree D sigma tau : ℂ) •
            Q sigma tau := by
      exact finThree_sum_sum_mulRight a
        (fun sigma tau ↦
          (permutationGramDeltaErrorThree D sigma tau : ℂ) • Q sigma tau)

/-- The normalized diagonal projector fixes the Gram-error sum on the
left. -/
theorem finiteThreeMomentReferenceProjection_mul_gramError
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau')) :
    finiteThreeMomentReferenceProjection Q *
        permutationGramWeightedErrorThree D Q =
      permutationGramWeightedErrorThree D Q := by
  change (((6 : ℂ)⁻¹ • ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma) *
      permutationGramWeightedErrorThree D Q =
        permutationGramWeightedErrorThree D Q)
  rw [smul_mul_assoc, Finset.sum_mul]
  simp_rw [diagonalQ_mul_permutationGramWeightedErrorThree D Q hmul]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num [Fintype.card_perm, Nat.factorial]

/-- The normalized diagonal projector fixes the Gram-error sum on the
right. -/
theorem permutationGramWeightedErrorThree_mul_referenceProjection
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau')) :
    permutationGramWeightedErrorThree D Q *
        finiteThreeMomentReferenceProjection Q =
      permutationGramWeightedErrorThree D Q := by
  change (permutationGramWeightedErrorThree D Q *
      ((6 : ℂ)⁻¹ • ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma) =
        permutationGramWeightedErrorThree D Q)
  rw [mul_smul_comm, Finset.mul_sum]
  simp_rw [permutationGramWeightedErrorThree_mul_diagonalQ D Q hmul]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  norm_num [Fintype.card_perm, Nat.factorial]

/-- The Gram-error sum is supported on both sides by the normalized
diagonal projector. -/
theorem finiteThreeMomentReferenceProjection_gramError_support
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau')) :
    finiteThreeMomentReferenceProjection Q *
        permutationGramWeightedErrorThree D Q *
        finiteThreeMomentReferenceProjection Q =
      permutationGramWeightedErrorThree D Q := by
  rw [finiteThreeMomentReferenceProjection_mul_gramError D Q hmul,
    permutationGramWeightedErrorThree_mul_referenceProjection D Q hmul]

/-- The Gram-error sum is self-adjoint whenever `Q` intertwines star with
simultaneous inversion. -/
theorem permutationGramWeightedErrorThree_isSelfAdjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹) :
    IsSelfAdjoint (permutationGramWeightedErrorThree D Q) := by
  unfold IsSelfAdjoint permutationGramWeightedErrorThree
  rw [star_sum]
  simp_rw [star_sum, star_smul, hstar]
  simp only [Complex.star_def, Complex.conj_ofReal]
  calc
    (∑ sigma, ∑ tau,
        (permutationGramDeltaErrorThree D sigma tau : ℂ) •
          Q sigma⁻¹ tau⁻¹) =
        ∑ sigma, ∑ tau,
          (permutationGramDeltaErrorThree D sigma⁻¹ tau⁻¹ : ℂ) •
            Q sigma⁻¹ tau⁻¹ := by
      apply Fintype.sum_congr
      intro sigma
      apply Fintype.sum_congr
      intro tau
      rw [permutationGramDeltaErrorThree_inv]
    _ = ∑ sigma, ∑ tau,
          (permutationGramDeltaErrorThree D sigma tau : ℂ) •
            Q sigma tau := by
      exact finThree_sum_sum_inv
        (fun sigma tau ↦
          (permutationGramDeltaErrorThree D sigma tau : ℂ) • Q sigma tau)

/-- Real rescaling preserves self-adjointness of the Gram error. -/
theorem scaledPermutationGramWeightedErrorThree_isSelfAdjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹) :
    IsSelfAdjoint
      ((((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap Q) := by
  unfold IsSelfAdjoint
  rw [star_smul,
    permutationGramWeightedErrorThree_isSelfAdjoint Doverlap Q hstar]
  simp

/-- Real rescaling preserves the two-sided support identity. -/
theorem finiteThreeMomentReferenceProjection_scaledGramError_support
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau')) :
    finiteThreeMomentReferenceProjection Q *
        ((((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
          permutationGramWeightedErrorThree Doverlap Q) *
        finiteThreeMomentReferenceProjection Q =
      (((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap Q := by
  rw [mul_smul_comm, smul_mul_assoc,
    finiteThreeMomentReferenceProjection_gramError_support Doverlap Q hmul]

/-- The exact B.26/B.27 reference-gluing conclusion, with all four former
structural hypotheses discharged from the concrete two-index
representation laws. -/
theorem relativeCPApproximation_threeMoment_referenceComposition_of_B26_representation
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ) (hglobal : 0 < Dglobal)
    (hoverlap : 2 ≤ Doverlap)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹)
    (HAB HBC HABC :
      CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (hcomposedB26 :
      finiteChoiMatrix (CompletelyPositiveMap.comp HAB HBC).toLinearMap =
        finiteThreeMomentComposedReferenceChoi Dglobal Doverlap Q)
    (hglobalB26 : finiteChoiMatrix HABC.toLinearMap =
      finiteThreeMomentGlobalReferenceChoi Dglobal Q) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Doverlap : ℝ))) - 1)
      (CompletelyPositiveMap.comp HAB HBC).toLinearMap
      HABC.toLinearMap := by
  exact relativeCPApproximation_threeMoment_referenceComposition_of_B26
    Dglobal Doverlap hglobal hoverlap Q hQ HAB HBC HABC
    hcomposedB26 hglobalB26
    (finiteThreeMomentReferenceProjection_isSelfAdjoint Q hstar)
    (finiteThreeMomentReferenceProjection_isIdempotent Q hmul)
    (scaledPermutationGramWeightedErrorThree_isSelfAdjoint
      Dglobal Doverlap Q hstar)
    (finiteThreeMomentReferenceProjection_scaledGramError_support
      Dglobal Doverlap Q hmul)

end

end TomographyOracleCore
