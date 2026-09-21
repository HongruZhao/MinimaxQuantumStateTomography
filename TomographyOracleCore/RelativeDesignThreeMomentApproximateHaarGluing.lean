import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaarComposition

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-!
# Unconditional raw-Choi B.26/B.27 reference gluing

The literature writes B.26 using a normalized EPR state, hence the displayed
`D⁻⁶` coefficient.  `finiteChoiMatrix` uses the unnormalized Choi vector,
so its coefficient is `D⁻³`.  This file carries that normalization through
the already-audited permutation-Gram estimate and obtains the relative-CP
comparison for the concrete reference maps.
-/

theorem finiteThreeMomentB26ChoiRegisterPermutation_mul
    (A B C : Type*)
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentB26ChoiRegisterPermutation A B C
        (sigma * sigma') (tau * tau') =
      finiteThreeMomentB26ChoiRegisterPermutation A B C sigma tau *
        finiteThreeMomentB26ChoiRegisterPermutation A B C sigma' tau' := by
  ext x <;> rfl

theorem finiteThreeMomentB26ChoiRegisterPermutation_inv
    (A B C : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    finiteThreeMomentB26ChoiRegisterPermutation A B C sigma⁻¹ tau⁻¹ =
      (finiteThreeMomentB26ChoiRegisterPermutation A B C sigma tau)⁻¹ := by
  ext x <;> rfl

theorem finiteThreeMomentB26ChoiQ_norm_le_one
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖finiteThreeMomentB26ChoiQ A B C sigma tau‖ ≤ 1 := by
  classical
  have hunit : finiteThreeMomentB26ChoiQ A B C sigma tau ∈
      unitary (CStarMatrix
        (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ) := by
    constructor
    · change star (((finiteThreeMomentB26ChoiRegisterPermutation
          A B C sigma tau)⁻¹).permMatrix ℂ) *
          (((finiteThreeMomentB26ChoiRegisterPermutation
            A B C sigma tau)⁻¹).permMatrix ℂ) = 1
      simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
    · change (((finiteThreeMomentB26ChoiRegisterPermutation
          A B C sigma tau)⁻¹).permMatrix ℂ) *
          star (((finiteThreeMomentB26ChoiRegisterPermutation
            A B C sigma tau)⁻¹).permMatrix ℂ) = 1
      simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
  exact le_of_eq (CStarRing.norm_of_mem_unitary hunit)

theorem finiteThreeMomentB26ChoiQ_mul
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentB26ChoiQ A B C sigma tau *
        finiteThreeMomentB26ChoiQ A B C sigma' tau' =
      finiteThreeMomentB26ChoiQ A B C
        (sigma * sigma') (tau * tau') := by
  classical
  apply CStarMatrix.ofMatrix.injective
  change (((finiteThreeMomentB26ChoiRegisterPermutation
        A B C sigma tau)⁻¹).permMatrix ℂ) *
      (((finiteThreeMomentB26ChoiRegisterPermutation
        A B C sigma' tau')⁻¹).permMatrix ℂ) =
    (((finiteThreeMomentB26ChoiRegisterPermutation A B C
      (sigma * sigma') (tau * tau'))⁻¹).permMatrix ℂ)
  rw [← Matrix.permMatrix_mul,
    finiteThreeMomentB26ChoiRegisterPermutation_mul]
  simp

theorem finiteThreeMomentB26ChoiQ_star
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentB26ChoiQ A B C sigma tau) =
      finiteThreeMomentB26ChoiQ A B C sigma⁻¹ tau⁻¹ := by
  classical
  apply CStarMatrix.ofMatrix.injective
  change star (((finiteThreeMomentB26ChoiRegisterPermutation
      A B C sigma tau)⁻¹).permMatrix ℂ) =
    (((finiteThreeMomentB26ChoiRegisterPermutation
      A B C sigma⁻¹ tau⁻¹)⁻¹).permMatrix ℂ)
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
    finiteThreeMomentB26ChoiRegisterPermutation_inv]

/-- Raw unnormalized-Choi form of the global order-three reference. -/
def finiteThreeMomentGlobalReferenceRawChoi
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  (((((Fintype.card A * Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
    ∑ sigma : Equiv.Perm (Fin 3),
      finiteThreeMomentB26ChoiQ A B C sigma sigma

theorem finiteThreeMomentGlobalReferenceRawChoi_eq_flat
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteThreeMomentGlobalReferenceRawChoi A B C =
      ((6 * ((((Fintype.card A * Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹) : ℝ) : ℂ) •
        finiteThreeMomentReferenceProjection
          (finiteThreeMomentB26ChoiQ A B C) := by
  unfold finiteThreeMomentGlobalReferenceRawChoi
    finiteThreeMomentReferenceProjection
  module

theorem finiteThreeMomentGlobalReferenceRawChoi_nonneg
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    0 ≤ finiteThreeMomentGlobalReferenceRawChoi A B C := by
  classical
  rw [finiteThreeMomentGlobalReferenceRawChoi_eq_flat]
  have hD : (0 : ℝ) <
      (Fintype.card A * Fintype.card B * Fintype.card C : ℕ) := by
    exact_mod_cast (mul_pos (mul_pos Fintype.card_pos Fintype.card_pos)
      Fintype.card_pos)
  rw [Complex.coe_smul]
  apply cstarMatrix_real_smul_nonneg (by positivity)
  let P := finiteThreeMomentReferenceProjection
    (finiteThreeMomentB26ChoiQ A B C)
  have hPself : IsSelfAdjoint P :=
    finiteThreeMomentReferenceProjection_isSelfAdjoint _
      (finiteThreeMomentB26ChoiQ_star A B C)
  have hPid : P * P = P :=
    finiteThreeMomentReferenceProjection_isIdempotent _
      (finiteThreeMomentB26ChoiQ_mul A B C)
  calc
    0 ≤ star P * P := star_mul_self_nonneg P
    _ = P * P := by rw [hPself.star_eq]
    _ = P := hPid

/-- Completely positive global reference reconstructed from its concrete
raw Choi matrix. -/
noncomputable def finiteThreeMomentGlobalReferenceCP
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :=
  finiteCPMapOfNonnegativeChoi
    (finiteThreeMomentGlobalReferenceRawChoi A B C)
    (finiteThreeMomentGlobalReferenceRawChoi_nonneg A B C)

@[simp] theorem finiteThreeMomentGlobalReferenceCP_choi
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteChoiMatrix
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap =
      finiteThreeMomentGlobalReferenceRawChoi A B C := by
  apply finiteChoiMatrix_finiteCPMapOfNonnegativeChoi

/-- The raw composition coefficient equals global `D⁻³` times the
normalized overlap Gram entry. -/
theorem finiteThreeMomentComposedReferenceRawChoi_eq_normalized
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteThreeMomentComposedReferenceRawChoi A B C =
      (((((Fintype.card A * Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
        ∑ sigma : Equiv.Perm (Fin 3),
          ∑ tau : Equiv.Perm (Fin 3),
            (normalizedPermutationGramThree (Fintype.card B) sigma tau : ℂ) •
              finiteThreeMomentB26ChoiQ A B C sigma tau := by
  classical
  unfold finiteThreeMomentComposedReferenceRawChoi
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro tau htau
  rw [smul_smul]
  congr 1
  unfold normalizedPermutationGramThree
  have hA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  push_cast
  field_simp

theorem finiteChoiMatrix_referenceComposition_sub_global_eq_rawGramError
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteChoiMatrix
        ((CompletelyPositiveMap.comp
          (finiteThreeMomentABReferenceCP A B C)
          (finiteThreeMomentBCReferenceCP A B C)).toLinearMap -
        (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap) =
      (((((Fintype.card A * Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
        permutationGramWeightedErrorThree (Fintype.card B)
          (finiteThreeMomentB26ChoiQ A B C) := by
  rw [finiteChoiMatrix_sub,
    finiteChoiMatrix_finiteThreeMomentReferenceComposition,
    finiteThreeMomentGlobalReferenceCP_choi,
    finiteThreeMomentComposedReferenceRawChoi_eq_normalized]
  unfold finiteThreeMomentGlobalReferenceRawChoi
    permutationGramWeightedErrorThree
  rw [← smul_sub]
  congr 1
  have hcoeff : ∀ sigma tau : Equiv.Perm (Fin 3),
      (permutationGramDeltaErrorThree (Fintype.card B) sigma tau : ℂ) =
        (normalizedPermutationGramThree (Fintype.card B) sigma tau : ℂ) -
          if sigma = tau then 1 else 0 := by
    intro sigma tau
    unfold permutationGramDeltaErrorThree
    by_cases hst : sigma = tau <;> simp [hst]
  simp_rw [hcoeff]
  simp_rw [sub_smul, Finset.sum_sub_distrib]
  simp

/-- Concrete raw-Choi form of Schuster--Haferkamp--Huang B.26--B.27. -/
theorem relativeCPApproximation_finiteThreeMomentReferenceComposition
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (hoverlap : 2 ≤ Fintype.card B) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1)
      (CompletelyPositiveMap.comp
        (finiteThreeMomentABReferenceCP A B C)
        (finiteThreeMomentBCReferenceCP A B C)).toLinearMap
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap := by
  classical
  let Dglobal := Fintype.card A * Fintype.card B * Fintype.card C
  let epsilon : ℝ := Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1
  let scale : ℝ := ((Dglobal : ℝ) ^ 3)⁻¹
  let c : ℝ := 6 * scale
  let Q := finiteThreeMomentB26ChoiQ A B C
  let P := finiteThreeMomentReferenceProjection Q
  have hDglobal : 0 < Dglobal := by
    dsimp only [Dglobal]
    positivity
  have hepsilon : 0 ≤ epsilon := by
    dsimp only [epsilon]
    apply sub_nonneg.mpr
    apply Real.one_le_exp
    positivity
  have hscale : 0 ≤ scale := by
    dsimp only [scale]
    positivity
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have hPself : IsSelfAdjoint P := by
    dsimp only [P, Q]
    exact finiteThreeMomentReferenceProjection_isSelfAdjoint _
      (finiteThreeMomentB26ChoiQ_star A B C)
  have hPid : P * P = P := by
    dsimp only [P, Q]
    exact finiteThreeMomentReferenceProjection_isIdempotent _
      (finiteThreeMomentB26ChoiQ_mul A B C)
  have hHflat : finiteChoiMatrix
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap =
        (c : ℂ) • P := by
    rw [finiteThreeMomentGlobalReferenceCP_choi,
      finiteThreeMomentGlobalReferenceRawChoi_eq_flat]
  have herror :=
    finiteChoiMatrix_referenceComposition_sub_global_eq_rawGramError
      A B C
  have herrorSelf : IsSelfAdjoint
      (finiteChoiMatrix
        ((CompletelyPositiveMap.comp
          (finiteThreeMomentABReferenceCP A B C)
          (finiteThreeMomentBCReferenceCP A B C)).toLinearMap -
        (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap)) := by
    rw [herror]
    unfold IsSelfAdjoint
    rw [star_smul,
      permutationGramWeightedErrorThree_isSelfAdjoint
        (Fintype.card B) (finiteThreeMomentB26ChoiQ A B C)
        (finiteThreeMomentB26ChoiQ_star A B C)]
    simp
  have herrorSupport :
      P * finiteChoiMatrix
          ((CompletelyPositiveMap.comp
            (finiteThreeMomentABReferenceCP A B C)
            (finiteThreeMomentBCReferenceCP A B C)).toLinearMap -
          (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap) * P =
        finiteChoiMatrix
          ((CompletelyPositiveMap.comp
            (finiteThreeMomentABReferenceCP A B C)
            (finiteThreeMomentBCReferenceCP A B C)).toLinearMap -
          (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap) := by
    dsimp only [P, Q]
    rw [herror, mul_smul_comm, smul_mul_assoc,
      finiteThreeMomentReferenceProjection_gramError_support
        (Fintype.card B) _ (finiteThreeMomentB26ChoiQ_mul A B C)]
  have hrawNorm :
      ‖permutationGramWeightedErrorThree (Fintype.card B) Q‖ ≤
        6 * epsilon := by
    exact (norm_permutationGramWeightedErrorThree_le
      (Fintype.card B) (by omega) Q
      (finiteThreeMomentB26ChoiQ_norm_le_one A B C)).trans
        (permutationGramDeltaErrorThree_le_exp
          (Fintype.card B) hoverlap)
  have herrorNorm :
      ‖finiteChoiMatrix
        ((CompletelyPositiveMap.comp
          (finiteThreeMomentABReferenceCP A B C)
          (finiteThreeMomentBCReferenceCP A B C)).toLinearMap -
        (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap)‖ ≤
          epsilon * c := by
    rw [herror, norm_smul]
    have hnormScale : ‖(scale : ℂ)‖ = scale := by
      simpa using abs_of_nonneg hscale
    rw [hnormScale]
    calc
      scale * ‖permutationGramWeightedErrorThree (Fintype.card B) Q‖ ≤
          scale * (6 * epsilon) :=
        mul_le_mul_of_nonneg_left hrawNorm hscale
      _ = epsilon * c := by
        dsimp only [c]
        ring
  exact relativeCPApproximation_of_finiteChoi_flatSupport_norm
    epsilon c
    (CompletelyPositiveMap.comp
      (finiteThreeMomentABReferenceCP A B C)
      (finiteThreeMomentBCReferenceCP A B C)).toLinearMap
    (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap
    P hepsilon hc hHflat herrorSelf hPself hPid herrorSupport herrorNorm

end

end TomographyOracleCore
