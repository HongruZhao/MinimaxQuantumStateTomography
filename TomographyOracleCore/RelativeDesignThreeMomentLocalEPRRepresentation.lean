import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaar
import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceB23

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance localEPRSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance localEPRStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Normalized untouched-register EPR factor for local third moments

The local Haar/reference maps act on one tensor factor and leave the other
factor unchanged.  In raw finite Choi coordinates the identity factor is the
unnormalized EPR projector.  Dividing it by the untouched dimension gives a
star projection, so tensoring it with the two-index permutation
representation preserves the unit operator-norm bound required in B.23.
-/

/-- The untouched-register EPR projector normalized to be idempotent. -/
def finiteNormalizedEPRProjector
    {T : Type*} [Fintype T] [DecidableEq T] :
    CStarMatrix (T × T) (T × T) ℂ :=
  (((Fintype.card T : ℝ)⁻¹ : ℝ) : ℂ) •
    finiteEPRProjector (I := T)

theorem finiteNormalizedEPRProjector_isSelfAdjoint
    {T : Type*} [Fintype T] [DecidableEq T] :
    IsSelfAdjoint (finiteNormalizedEPRProjector (T := T)) := by
  unfold IsSelfAdjoint finiteNormalizedEPRProjector
  rw [star_smul, (finiteEPRProjector_isSelfAdjoint (T := T)).star_eq]
  simp

theorem finiteNormalizedEPRProjector_sq
    {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] :
    finiteNormalizedEPRProjector (T := T) *
        finiteNormalizedEPRProjector =
      finiteNormalizedEPRProjector := by
  unfold finiteNormalizedEPRProjector
  rw [smul_mul_assoc, mul_smul_comm, finiteEPRProjector_sq]
  simp only [smul_smul]
  congr 1
  have hcard : (Fintype.card T : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem finiteNormalizedEPRProjector_isStarProjection
    {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] :
    IsStarProjection (finiteNormalizedEPRProjector (T := T)) where
  isIdempotentElem := finiteNormalizedEPRProjector_sq (T := T)
  isSelfAdjoint := finiteNormalizedEPRProjector_isSelfAdjoint (T := T)

theorem finiteNormalizedEPRProjector_nonneg
    {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] :
    0 ≤ finiteNormalizedEPRProjector (T := T) :=
  (finiteNormalizedEPRProjector_isStarProjection (T := T)).nonneg

theorem finiteNormalizedEPRProjector_norm_le_one
    {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T] :
    ‖finiteNormalizedEPRProjector (T := T)‖ ≤ 1 := by
  let P := finiteNormalizedEPRProjector (T := T)
  have hself : IsSelfAdjoint P :=
    finiteNormalizedEPRProjector_isSelfAdjoint (T := T)
  have hsq : P * P = P := finiteNormalizedEPRProjector_sq (T := T)
  have hnorm := hself.norm_mul_self
  rw [hsq] at hnorm
  nlinarith [norm_nonneg P]

/-- The acted-on pair-permutation representation tensored with the normalized
EPR projection of the untouched register and transported across a basis
reassociation. -/
def finiteThreeMomentLocalChoiQ
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix (I × I) (I × I) ℂ :=
  finiteChoiKroneckerReindex e
    (finiteThreeMomentPairQ rho sigma tau)
    (finiteNormalizedEPRProjector (T := T))

theorem finiteThreeMomentLocalChoiQ_mul
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau)
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentLocalChoiQ e rho sigma tau *
        finiteThreeMomentLocalChoiQ e rho sigma' tau' =
      finiteThreeMomentLocalChoiQ e rho
        (sigma * sigma') (tau * tau') := by
  unfold finiteThreeMomentLocalChoiQ
  rw [finiteChoiKroneckerReindex_mul,
    finiteThreeMomentPairQ_mul rho hrho,
    finiteNormalizedEPRProjector_sq]

theorem finiteThreeMomentLocalChoiQ_star
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹)
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentLocalChoiQ e rho sigma tau) =
      finiteThreeMomentLocalChoiQ e rho sigma⁻¹ tau⁻¹ := by
  unfold finiteThreeMomentLocalChoiQ
  rw [finiteChoiKroneckerReindex_star,
    finiteThreeMomentPairQ_star rho hrhoInv,
    (finiteNormalizedEPRProjector_isSelfAdjoint (T := T)).star_eq]

theorem finiteThreeMomentLocalChoiQ_one_isStarProjection
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹) :
    IsStarProjection
      (finiteThreeMomentLocalChoiQ e rho 1 1) where
  isIdempotentElem := by
    change finiteThreeMomentLocalChoiQ e rho 1 1 *
        finiteThreeMomentLocalChoiQ e rho 1 1 =
      finiteThreeMomentLocalChoiQ e rho 1 1
    rw [finiteThreeMomentLocalChoiQ_mul e rho hrho]
    simp
  isSelfAdjoint := by
    unfold IsSelfAdjoint
    rw [finiteThreeMomentLocalChoiQ_star e rho hrhoInv]
    simp

theorem finiteThreeMomentLocalChoiQ_one_norm_le_one
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹) :
    ‖finiteThreeMomentLocalChoiQ e rho 1 1‖ ≤ 1 := by
  let P := finiteThreeMomentLocalChoiQ e rho 1 1
  have hproj : IsStarProjection P :=
    finiteThreeMomentLocalChoiQ_one_isStarProjection e rho hrho hrhoInv
  have hnorm := hproj.isSelfAdjoint.norm_mul_self
  rw [hproj.isIdempotentElem] at hnorm
  nlinarith [norm_nonneg P]

theorem finiteThreeMomentLocalChoiQ_norm_le_one
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹)
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖finiteThreeMomentLocalChoiQ e rho sigma tau‖ ≤ 1 := by
  let Q := finiteThreeMomentLocalChoiQ e rho sigma tau
  have hstarMul : star Q * Q =
      finiteThreeMomentLocalChoiQ e rho 1 1 := by
    unfold Q
    rw [finiteThreeMomentLocalChoiQ_star e rho hrhoInv,
      finiteThreeMomentLocalChoiQ_mul e rho hrho]
    simp
  have hnormSq : ‖Q‖ ^ 2 =
      ‖finiteThreeMomentLocalChoiQ e rho 1 1‖ := by
    rw [← hstarMul]
    simpa [pow_two] using
      (CStarRing.norm_star_mul_self (x := Q)).symm
  have hone := finiteThreeMomentLocalChoiQ_one_norm_le_one
    e rho hrho hrhoInv
  nlinarith [norm_nonneg Q]

/-- The transported Choi Kronecker construction is additive in its acted-on
matrix factor. -/
theorem finiteChoiKroneckerReindex_sum_left
    {I S T Α : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Fintype Α]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : Α → CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
  finiteChoiKroneckerReindex e (∑ x, G x) E =
      ∑ x, finiteChoiKroneckerReindex e (G x) E := by
  classical
  have hsum : CStarMatrix.ofMatrix.symm (∑ x, G x) =
      ∑ x, CStarMatrix.ofMatrix.symm (G x) := rfl
  apply CStarMatrix.ofMatrix.injective
  change
    Matrix.reindexAlgEquiv ℂ ℂ (finiteChoiTensorEquiv e).symm
        (Matrix.kronecker
          (CStarMatrix.ofMatrix.symm (∑ x, G x))
          (CStarMatrix.ofMatrix.symm E)) =
      ∑ x, Matrix.reindexAlgEquiv ℂ ℂ
        (finiteChoiTensorEquiv e).symm
          (Matrix.kronecker
            (CStarMatrix.ofMatrix.symm (G x))
            (CStarMatrix.ofMatrix.symm E))
  rw [hsum]
  ext ia jb
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply, Matrix.kronecker,
    Matrix.kroneckerMap, Matrix.of_apply, Matrix.sum_apply,
    CStarMatrix.ofMatrix_symm_apply, Finset.sum_mul]

/-- The raw untouched-register EPR factor is its normalized projection times
the untouched dimension. -/
theorem finiteChoiKroneckerReindex_EPR_eq_card_smul_normalized
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : CStarMatrix (S × S) (S × S) ℂ) :
    finiteChoiKroneckerReindex e G (finiteEPRProjector (I := T)) =
      (Fintype.card T : ℝ) •
        finiteChoiKroneckerReindex e G
          (finiteNormalizedEPRProjector (T := T)) := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  rw [finiteChoiKroneckerReindex_apply]
  rw [CStarMatrix.smul_apply, finiteChoiKroneckerReindex_apply]
  unfold finiteNormalizedEPRProjector
  rw [CStarMatrix.smul_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  have hcard : (Fintype.card T : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- Replacing the untouched raw EPR factor by its normalized projection
extracts exactly one factor of the untouched dimension. -/
theorem finiteThreeMomentLocalReferenceRawChoi_eq_card_smul_approximateHaarRawChoi
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (D : ℕ) :
    (((((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
        finiteChoiKroneckerReindex e
          (finiteThreeMomentPairSum rho)
          (finiteEPRProjector (I := T))) =
      (Fintype.card T : ℝ) •
        finiteThreeMomentApproximateHaarRawChoi D
          (finiteThreeMomentLocalChoiQ e rho) := by
  classical
  unfold finiteThreeMomentApproximateHaarRawChoi
    finiteThreeMomentPairSum finiteThreeMomentLocalChoiQ
  rw [finiteChoiKroneckerReindex_sum_left]
  simp_rw [finiteChoiKroneckerReindex_EPR_eq_card_smul_normalized]
  rw [← Finset.smul_sum]
  apply CStarMatrix.ext
  intro i j
  simp only [CStarMatrix.smul_apply, Complex.real_smul, smul_eq_mul]
  ring

/-! ## Concrete local third-moment factors -/

/-- The normalized Choi representation for an `AB` third moment with the
three-replica `C` register untouched. -/
def finiteThreeMomentABLocalChoiQ
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  finiteThreeMomentLocalChoiQ
    (threeReplicaABCEquivAB_C A B C)
    (threeReplicaABSlotPermutation A B) sigma tau

theorem finiteThreeMomentABLocalChoiQ_mul
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentABLocalChoiQ A B C sigma tau *
        finiteThreeMomentABLocalChoiQ A B C sigma' tau' =
      finiteThreeMomentABLocalChoiQ A B C
        (sigma * sigma') (tau * tau') := by
  exact finiteThreeMomentLocalChoiQ_mul
    (threeReplicaABCEquivAB_C A B C)
    (threeReplicaABSlotPermutation A B)
    (threeReplicaABSlotPermutation_mul A B)
    sigma tau sigma' tau'

theorem finiteThreeMomentABLocalChoiQ_star
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentABLocalChoiQ A B C sigma tau) =
      finiteThreeMomentABLocalChoiQ A B C sigma⁻¹ tau⁻¹ := by
  exact finiteThreeMomentLocalChoiQ_star
    (threeReplicaABCEquivAB_C A B C)
    (threeReplicaABSlotPermutation A B)
    (threeReplicaABSlotPermutation_inv A B) sigma tau

theorem finiteThreeMomentABLocalChoiQ_norm_le_one
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖finiteThreeMomentABLocalChoiQ A B C sigma tau‖ ≤ 1 := by
  exact finiteThreeMomentLocalChoiQ_norm_le_one
    (threeReplicaABCEquivAB_C A B C)
    (threeReplicaABSlotPermutation A B)
    (threeReplicaABSlotPermutation_mul A B)
    (threeReplicaABSlotPermutation_inv A B) sigma tau

theorem finiteThreeMomentABReferenceChoi_eq_card_smul_approximateHaarRawChoi
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteThreeMomentABReferenceChoi A B C =
      (Fintype.card (ThreeReplica C) : ℝ) •
        finiteThreeMomentApproximateHaarRawChoi
          (Fintype.card A * Fintype.card B)
          (finiteThreeMomentABLocalChoiQ A B C) := by
  change (((((Fintype.card A * Fintype.card B : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) •
      finiteChoiKroneckerReindex (threeReplicaABCEquivAB_C A B C)
        (finiteThreeMomentPairSum (threeReplicaABSlotPermutation A B))
        (finiteEPRProjector (I := ThreeReplica C))) =
    (Fintype.card (ThreeReplica C) : ℝ) •
      finiteThreeMomentApproximateHaarRawChoi
        (Fintype.card A * Fintype.card B)
        (finiteThreeMomentLocalChoiQ
          (threeReplicaABCEquivAB_C A B C)
          (threeReplicaABSlotPermutation A B))
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact finiteThreeMomentLocalReferenceRawChoi_eq_card_smul_approximateHaarRawChoi
    (threeReplicaABCEquivAB_C A B C)
    (threeReplicaABSlotPermutation A B)
    (Fintype.card A * Fintype.card B)

/-- The normalized Choi representation for a `BC` third moment with the
three-replica `A` register untouched. -/
def finiteThreeMomentBCLocalChoiQ
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  finiteThreeMomentLocalChoiQ
    (threeReplicaABCEquivBC_A A B C)
    (threeReplicaABSlotPermutation B C) sigma tau

theorem finiteThreeMomentBCLocalChoiQ_mul
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentBCLocalChoiQ A B C sigma tau *
        finiteThreeMomentBCLocalChoiQ A B C sigma' tau' =
      finiteThreeMomentBCLocalChoiQ A B C
        (sigma * sigma') (tau * tau') := by
  exact finiteThreeMomentLocalChoiQ_mul
    (threeReplicaABCEquivBC_A A B C)
    (threeReplicaABSlotPermutation B C)
    (threeReplicaABSlotPermutation_mul B C)
    sigma tau sigma' tau'

theorem finiteThreeMomentBCLocalChoiQ_star
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentBCLocalChoiQ A B C sigma tau) =
      finiteThreeMomentBCLocalChoiQ A B C sigma⁻¹ tau⁻¹ := by
  exact finiteThreeMomentLocalChoiQ_star
    (threeReplicaABCEquivBC_A A B C)
    (threeReplicaABSlotPermutation B C)
    (threeReplicaABSlotPermutation_inv B C) sigma tau

theorem finiteThreeMomentBCLocalChoiQ_norm_le_one
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖finiteThreeMomentBCLocalChoiQ A B C sigma tau‖ ≤ 1 := by
  exact finiteThreeMomentLocalChoiQ_norm_le_one
    (threeReplicaABCEquivBC_A A B C)
    (threeReplicaABSlotPermutation B C)
    (threeReplicaABSlotPermutation_mul B C)
    (threeReplicaABSlotPermutation_inv B C) sigma tau

theorem finiteThreeMomentBCReferenceChoi_eq_card_smul_approximateHaarRawChoi
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteThreeMomentBCReferenceChoi A B C =
      (Fintype.card (ThreeReplica A) : ℝ) •
        finiteThreeMomentApproximateHaarRawChoi
          (Fintype.card B * Fintype.card C)
          (finiteThreeMomentBCLocalChoiQ A B C) := by
  change (((((Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) •
      finiteChoiKroneckerReindex (threeReplicaABCEquivBC_A A B C)
        (finiteThreeMomentPairSum (threeReplicaABSlotPermutation B C))
        (finiteEPRProjector (I := ThreeReplica A))) =
    (Fintype.card (ThreeReplica A) : ℝ) •
      finiteThreeMomentApproximateHaarRawChoi
        (Fintype.card B * Fintype.card C)
        (finiteThreeMomentLocalChoiQ
          (threeReplicaABCEquivBC_A A B C)
          (threeReplicaABSlotPermutation B C))
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  exact finiteThreeMomentLocalReferenceRawChoi_eq_card_smul_approximateHaarRawChoi
    (threeReplicaABCEquivBC_A A B C)
    (threeReplicaABSlotPermutation B C)
    (Fintype.card B * Fintype.card C)

end

end TomographyOracleCore
