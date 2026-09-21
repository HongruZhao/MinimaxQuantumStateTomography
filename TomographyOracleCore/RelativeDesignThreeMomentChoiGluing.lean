import TomographyOracleCore.RelativeDesignFiniteChoi

namespace TomographyOracleCore

open scoped CStarAlgebra Matrix.Norms.L2Operator

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-!
# The order-three B.26 Choi formulas and reference-gluing conclusion

The two matrices below are the two sides of Schuster--Haferkamp--Huang
Eq. (B.26), after normalizing the overlap Gram matrix by `Doverlap^3`.
The family `Q sigma tau` is the concrete EPR/permutation tensor occurring
there.  No channel comparison is built into either definition.
-/

/-- The composed-subsystem reference Choi matrix in the first line of
Eq. (B.26), specialized to moment order three. -/
def finiteThreeMomentComposedReferenceChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  (((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
    ∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        (normalizedPermutationGramThree Doverlap sigma tau : ℂ) •
          Q sigma tau

/-- The global reference Choi matrix in the second line of Eq. (B.26).
For the actual EPR tensors, `Q sigma sigma` is `sigma tensor sigma`. -/
def finiteThreeMomentGlobalReferenceChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  (((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
    ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma

/-- The normalized symmetric-support operator associated with the diagonal
permutation sum.  For a genuine permutation representation this is the
orthogonal projector onto the invariant subspace. -/
def finiteThreeMomentReferenceProjection
    {I : Type*} [Fintype I] [DecidableEq I]
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  ((6 : ℂ)⁻¹) • ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma

/-- The global B.26 reference is flat on the normalized symmetric support,
with eigenvalue `6 * Dglobal^-6`. -/
theorem finiteThreeMomentGlobalReferenceChoi_eq_flat
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    finiteThreeMomentGlobalReferenceChoi Dglobal Q =
      ((6 * ((Dglobal : ℝ) ^ 6)⁻¹ : ℝ) : ℂ) •
        finiteThreeMomentReferenceProjection Q := by
  unfold finiteThreeMomentGlobalReferenceChoi
    finiteThreeMomentReferenceProjection
  module

/-- Subtracting the two literal B.26 matrices gives exactly the scaled
permutation-Gram defect used in Eq. (B.27). -/
theorem finiteThreeMomentComposedReferenceChoi_sub_global
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    finiteThreeMomentComposedReferenceChoi Dglobal Doverlap Q -
        finiteThreeMomentGlobalReferenceChoi Dglobal Q =
      (((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap Q := by
  unfold finiteThreeMomentComposedReferenceChoi
    finiteThreeMomentGlobalReferenceChoi
  rw [← smul_sub]
  congr 1
  unfold permutationGramWeightedErrorThree
  have hcoeff : ∀ sigma tau : Equiv.Perm (Fin 3),
      (permutationGramDeltaErrorThree Doverlap sigma tau : ℂ) =
        (normalizedPermutationGramThree Doverlap sigma tau : ℂ) -
          if sigma = tau then 1 else 0 := by
    intro sigma tau
    unfold permutationGramDeltaErrorThree
    by_cases hst : sigma = tau <;> simp [hst]
  simp_rw [hcoeff, sub_smul, Finset.sum_sub_distrib]
  simp

/-- The two B.26 Choi identifications reduce the Choi error of the composed
local reference against the global reference to the explicit B.27 matrix. -/
theorem finiteChoiMatrix_referenceComposition_sub_global_eq_gramError
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (Hcomposed Hglobal :
      CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ)
    (hcomposedB26 : finiteChoiMatrix Hcomposed =
      finiteThreeMomentComposedReferenceChoi Dglobal Doverlap Q)
    (hglobalB26 : finiteChoiMatrix Hglobal =
      finiteThreeMomentGlobalReferenceChoi Dglobal Q) :
    finiteChoiMatrix (Hcomposed - Hglobal) =
      (((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap Q := by
  rw [finiteChoiMatrix_sub, hcomposedB26, hglobalB26,
    finiteThreeMomentComposedReferenceChoi_sub_global]

/-- Exact order-three reference-gluing conclusion from the two literal B.26
Choi formulas and the audited B.27 norm estimate.  The remaining structural
hypotheses say only that the concrete normalized permutation sum is a
self-adjoint projection and that the concrete Gram-error matrix is
self-adjoint and supported on it.  No completely-positive comparison is a
premise. -/
theorem relativeCPApproximation_threeMoment_referenceComposition_of_B26
    {I : Type*} [Fintype I] [DecidableEq I]
    (Dglobal Doverlap : ℕ) (hglobal : 0 < Dglobal)
    (hoverlap : 2 ≤ Doverlap)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1)
    (HAB HBC HABC :
      CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (hcomposedB26 :
      finiteChoiMatrix (CompletelyPositiveMap.comp HAB HBC).toLinearMap =
        finiteThreeMomentComposedReferenceChoi Dglobal Doverlap Q)
    (hglobalB26 : finiteChoiMatrix HABC.toLinearMap =
      finiteThreeMomentGlobalReferenceChoi Dglobal Q)
    (hPself : IsSelfAdjoint (finiteThreeMomentReferenceProjection Q))
    (hPid : finiteThreeMomentReferenceProjection Q *
        finiteThreeMomentReferenceProjection Q =
      finiteThreeMomentReferenceProjection Q)
    (herrorSelf : IsSelfAdjoint
      ((((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
        permutationGramWeightedErrorThree Doverlap Q))
    (herrorSupport :
      finiteThreeMomentReferenceProjection Q *
          ((((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
            permutationGramWeightedErrorThree Doverlap Q) *
          finiteThreeMomentReferenceProjection Q =
        (((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
          permutationGramWeightedErrorThree Doverlap Q) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Doverlap : ℝ))) - 1)
      (CompletelyPositiveMap.comp HAB HBC).toLinearMap
      HABC.toLinearMap := by
  let epsilon : ℝ := Real.exp (9 / (2 * (Doverlap : ℝ))) - 1
  let c : ℝ := 6 * ((Dglobal : ℝ) ^ 6)⁻¹
  let P := finiteThreeMomentReferenceProjection Q
  have hepsilon : 0 ≤ epsilon := by
    dsimp only [epsilon]
    apply sub_nonneg.mpr
    apply Real.one_le_exp
    positivity
  have hc : 0 ≤ c := by
    dsimp only [c]
    positivity
  have herror :=
    finiteChoiMatrix_referenceComposition_sub_global_eq_gramError
      Dglobal Doverlap Q
      (CompletelyPositiveMap.comp HAB HBC).toLinearMap HABC.toLinearMap
      hcomposedB26 hglobalB26
  have hHflat : finiteChoiMatrix HABC.toLinearMap = (c : ℂ) • P := by
    rw [hglobalB26, finiteThreeMomentGlobalReferenceChoi_eq_flat]
  have herrorSelf' : IsSelfAdjoint
      (finiteChoiMatrix
        ((CompletelyPositiveMap.comp HAB HBC).toLinearMap -
          HABC.toLinearMap)) := by
    rw [herror]
    exact herrorSelf
  have herrorSupport' :
      P * finiteChoiMatrix
          ((CompletelyPositiveMap.comp HAB HBC).toLinearMap -
            HABC.toLinearMap) * P =
        finiteChoiMatrix
          ((CompletelyPositiveMap.comp HAB HBC).toLinearMap -
            HABC.toLinearMap) := by
    rw [herror]
    exact herrorSupport
  have hB27 := norm_scaled_permutationGramWeightedErrorThree_le_exp
    Dglobal Doverlap hglobal hoverlap Q hQ
  have herrorNorm :
      ‖finiteChoiMatrix
        ((CompletelyPositiveMap.comp HAB HBC).toLinearMap -
          HABC.toLinearMap)‖ ≤ epsilon * c := by
    rw [herror]
    calc
      ‖(((Dglobal : ℝ) ^ 6)⁻¹ : ℂ) •
          permutationGramWeightedErrorThree Doverlap Q‖ ≤
          ((Dglobal : ℝ) ^ 6)⁻¹ *
            (6 * (Real.exp (9 / (2 * (Doverlap : ℝ))) - 1)) := hB27
      _ = epsilon * c := by
        dsimp only [epsilon, c]
        ring
  exact relativeCPApproximation_of_finiteChoi_flatSupport_norm
    epsilon c (CompletelyPositiveMap.comp HAB HBC).toLinearMap
    HABC.toLinearMap P hepsilon hc hHflat herrorSelf' hPself hPid
    herrorSupport' herrorNorm

end

end TomographyOracleCore
