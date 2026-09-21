import TomographyOracleCore.RelativeDesignThreeMomentConcretePermutation
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra Matrix.Norms.L2Operator Kronecker BigOperators

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

@[simp] theorem ofMatrix_symm_mul
    {I : Type*} [Fintype I] [DecidableEq I]
    (X Y : CStarMatrix I I ℂ) :
    CStarMatrix.ofMatrix.symm (X * Y) =
      CStarMatrix.ofMatrix.symm X * CStarMatrix.ofMatrix.symm Y := rfl

@[simp] theorem ofMatrix_symm_star
    {I : Type*} [Fintype I]
    (X : CStarMatrix I I ℂ) :
    CStarMatrix.ofMatrix.symm (star X) =
      (CStarMatrix.ofMatrix.symm X).conjTranspose := rfl

@[simp] theorem ofMatrix_symm_complex_smul
    {I : Type*} (c : ℂ) (X : CStarMatrix I I ℂ) :
    CStarMatrix.ofMatrix.symm (c • X) =
      c • CStarMatrix.ofMatrix.symm X := rfl

/-!
# Concrete approximate-Haar reference maps at moment order three

This file uses the unnormalized finite Choi convention from
`RelativeDesignFiniteChoi`.  Consequently the raw Choi coefficient of the
order-three map is `D⁻³`; the `D⁻⁶` coefficient in Eq. (B.26) is the
same Choi matrix evaluated on the normalized EPR state.
-/

/-- Two physical subsystems, each already replicated three times. -/
abbrev ThreeReplicaAB (A B : Type*) := ThreeReplica A × ThreeReplica B

/-- Reassociate the factorized `A,B,C` replica basis as `(A,B),C`. -/
def threeReplicaABCEquivAB_C (A B C : Type*) :
    ThreeReplicaABC A B C ≃ ThreeReplicaAB A B × ThreeReplica C where
  toFun x := ((x.1, x.2.1), x.2.2)
  invFun x := (x.1.1, x.1.2, x.2)
  left_inv x := rfl
  right_inv x := rfl

/-- Reassociate the factorized `A,B,C` replica basis as `A,(B,C)`. -/
def threeReplicaABCEquivA_BC (A B C : Type*) :
    ThreeReplicaABC A B C ≃ ThreeReplica A × ThreeReplicaAB B C where
  toFun x := (x.1, x.2.1, x.2.2)
  invFun x := (x.1, x.2.1, x.2.2)
  left_inv x := rfl
  right_inv x := rfl

/-- Move the Choi pair of a bipartite basis to the product of the two
subsystem Choi pairs. -/
def finiteChoiProductEquiv (S T : Type*) :
    ((S × T) × (S × T)) ≃ (S × S) × (T × T) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  left_inv x := rfl
  right_inv x := rfl

/-- Diagonal two-copy permutation matrix attached to a finite
representation of `S₃`. -/
def finiteThreeMomentPairPermutation
    {S : Type*}
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (sigma tau : Equiv.Perm (Fin 3)) : Equiv.Perm (S × S) :=
  (rho sigma).prodCongr (rho tau)

def finiteThreeMomentPairQ
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (sigma tau : Equiv.Perm (Fin 3)) :
  CStarMatrix (S × S) (S × S) ℂ :=
  CStarMatrix.ofMatrix <|
    Matrix.permMatrixHom (R := ℂ)
      (finiteThreeMomentPairPermutation rho sigma tau)

@[simp] theorem finiteThreeMomentPairQ_apply
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (sigma tau : Equiv.Perm (Fin 3)) (u v : S × S) :
    finiteThreeMomentPairQ rho sigma tau u v =
      if v = (finiteThreeMomentPairPermutation rho sigma tau)⁻¹ u
      then 1 else 0 := by
  change ((finiteThreeMomentPairPermutation rho sigma tau)⁻¹.permMatrix ℂ)
    u v = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

theorem finiteThreeMomentPairQ_mul
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau)
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentPairQ rho sigma tau *
        finiteThreeMomentPairQ rho sigma' tau' =
      finiteThreeMomentPairQ rho (sigma * sigma') (tau * tau') := by
  classical
  apply CStarMatrix.ofMatrix.injective
  change (finiteThreeMomentPairPermutation rho sigma tau)⁻¹.permMatrix ℂ *
      (finiteThreeMomentPairPermutation rho sigma' tau')⁻¹.permMatrix ℂ =
    (finiteThreeMomentPairPermutation rho (sigma * sigma')
      (tau * tau'))⁻¹.permMatrix ℂ
  rw [← Matrix.permMatrix_mul]
  congr 1
  unfold finiteThreeMomentPairPermutation
  rw [hrho sigma sigma', hrho tau tau']
  ext x <;> rfl

theorem finiteThreeMomentPairQ_star
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹)
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentPairQ rho sigma tau) =
      finiteThreeMomentPairQ rho sigma⁻¹ tau⁻¹ := by
  classical
  apply CStarMatrix.ofMatrix.injective
  change star ((finiteThreeMomentPairPermutation rho sigma tau)⁻¹.permMatrix ℂ) =
    (finiteThreeMomentPairPermutation rho sigma⁻¹ tau⁻¹)⁻¹.permMatrix ℂ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  congr 1
  unfold finiteThreeMomentPairPermutation
  rw [hrhoInv sigma, hrhoInv tau]
  ext x <;> rfl

/-- The unnormalized diagonal group sum. -/
def finiteThreeMomentPairSum
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S) :
    CStarMatrix (S × S) (S × S) ℂ :=
  ∑ sigma : Equiv.Perm (Fin 3), finiteThreeMomentPairQ rho sigma sigma

theorem finiteThreeMomentPairSum_isSelfAdjoint
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹) :
    IsSelfAdjoint (finiteThreeMomentPairSum rho) := by
  have h := finiteThreeMomentReferenceProjection_isSelfAdjoint
    (finiteThreeMomentPairQ rho)
    (finiteThreeMomentPairQ_star rho hrhoInv)
  unfold finiteThreeMomentReferenceProjection at h
  unfold IsSelfAdjoint at h ⊢
  have h' := congrArg (fun X ↦ (6 : ℂ) • X) h
  simpa [finiteThreeMomentPairSum] using h'

theorem finiteThreeMomentPairSum_sq
    {S : Type*} [Fintype S] [DecidableEq S]
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau) :
    finiteThreeMomentPairSum rho * finiteThreeMomentPairSum rho =
      (6 : ℂ) • finiteThreeMomentPairSum rho := by
  have h := finiteThreeMomentReferenceProjection_isIdempotent
    (finiteThreeMomentPairQ rho)
    (finiteThreeMomentPairQ_mul rho hrho)
  unfold finiteThreeMomentReferenceProjection at h
  unfold finiteThreeMomentPairSum
  have h' := congrArg (fun X ↦ (36 : ℂ) • X) h
  norm_num [smul_smul] at h'
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul] using h'

/-- The unnormalized EPR projector squares to the subsystem dimension times
itself. -/
theorem finiteEPRProjector_sq
    {T : Type*} [Fintype T] [DecidableEq T] :
    finiteEPRProjector (I := T) * finiteEPRProjector =
      (Fintype.card T : ℂ) • finiteEPRProjector := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp only [CStarMatrix.mul_apply, finiteEPRProjector,
    CStarMatrix.smul_apply]
  by_cases hia : i = a
  · subst a
    by_cases hjb : j = b
    · subst b
      rw [Fintype.sum_prod_type]
      simp
    · simp [hjb]
  · simp [hia]

theorem finiteEPRProjector_isSelfAdjoint
    {T : Type*} [Fintype T] [DecidableEq T] :
    IsSelfAdjoint (finiteEPRProjector (I := T)) := by
  classical
  unfold IsSelfAdjoint
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [CStarMatrix.star_apply, finiteEPRProjector, and_comm]

/-- Choi-coordinate reassociation induced by a bipartite basis
reassociation. -/
def finiteChoiTensorEquiv {I S T : Type*} (e : I ≃ S × T) :
    (I × I) ≃ (S × S) × (T × T) :=
  (e.prodCongr e).trans (finiteChoiProductEquiv S T)

/-- Kronecker product of two Choi matrices, transported back across a
bipartite basis reassociation. -/
def finiteChoiKroneckerReindex
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  CStarMatrix.ofMatrix <|
    Matrix.reindexAlgEquiv ℂ ℂ (finiteChoiTensorEquiv e).symm
      (Matrix.kronecker (CStarMatrix.ofMatrix.symm G)
        (CStarMatrix.ofMatrix.symm E))

@[simp] theorem finiteChoiKroneckerReindex_apply
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ)
    (i a j b : I) :
    finiteChoiKroneckerReindex e G E (i, a) (j, b) =
      G ((e i).1, (e a).1) ((e j).1, (e b).1) *
        E ((e i).2, (e a).2) ((e j).2, (e b).2) := by
  rfl

theorem finiteChoiKroneckerReindex_mul
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G G' : CStarMatrix (S × S) (S × S) ℂ)
    (E E' : CStarMatrix (T × T) (T × T) ℂ) :
    finiteChoiKroneckerReindex e G E *
        finiteChoiKroneckerReindex e G' E' =
      finiteChoiKroneckerReindex e (G * G') (E * E') := by
  apply CStarMatrix.ofMatrix.injective
  change Matrix.reindexAlgEquiv ℂ ℂ (finiteChoiTensorEquiv e).symm
        (Matrix.kronecker (CStarMatrix.ofMatrix.symm G)
          (CStarMatrix.ofMatrix.symm E)) *
      Matrix.reindexAlgEquiv ℂ ℂ (finiteChoiTensorEquiv e).symm
        (Matrix.kronecker (CStarMatrix.ofMatrix.symm G')
          (CStarMatrix.ofMatrix.symm E')) =
    Matrix.reindexAlgEquiv ℂ ℂ (finiteChoiTensorEquiv e).symm
      (Matrix.kronecker (CStarMatrix.ofMatrix.symm (G * G'))
        (CStarMatrix.ofMatrix.symm (E * E')))
  rw [← map_mul]
  congr 1
  simp only [ofMatrix_symm_mul]
  change Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
      (CStarMatrix.ofMatrix.symm G) (CStarMatrix.ofMatrix.symm E) *
    Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
      (CStarMatrix.ofMatrix.symm G') (CStarMatrix.ofMatrix.symm E') =
    Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
      (CStarMatrix.ofMatrix.symm G * CStarMatrix.ofMatrix.symm G')
      (CStarMatrix.ofMatrix.symm E * CStarMatrix.ofMatrix.symm E')
  exact (Matrix.mul_kronecker_mul
    (CStarMatrix.ofMatrix.symm G) (CStarMatrix.ofMatrix.symm G')
    (CStarMatrix.ofMatrix.symm E) (CStarMatrix.ofMatrix.symm E')).symm

theorem finiteChoiKroneckerReindex_star
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
    star (finiteChoiKroneckerReindex e G E) =
      finiteChoiKroneckerReindex e (star G) (star E) := by
  apply CStarMatrix.ofMatrix.injective
  change star (Matrix.reindex (finiteChoiTensorEquiv e).symm
      (finiteChoiTensorEquiv e).symm
        (Matrix.kronecker (CStarMatrix.ofMatrix.symm G)
          (CStarMatrix.ofMatrix.symm E))) =
    Matrix.reindex (finiteChoiTensorEquiv e).symm
      (finiteChoiTensorEquiv e).symm
        (Matrix.kronecker (CStarMatrix.ofMatrix.symm (star G))
          (CStarMatrix.ofMatrix.symm (star E)))
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_reindex]
  congr 1
  simp only [ofMatrix_symm_star]
  change (Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
      (CStarMatrix.ofMatrix.symm G)
      (CStarMatrix.ofMatrix.symm E)).conjTranspose =
    Matrix.kroneckerMap (fun x y : ℂ ↦ x * y)
      (CStarMatrix.ofMatrix.symm G).conjTranspose
      (CStarMatrix.ofMatrix.symm E).conjTranspose
  exact Matrix.conjTranspose_kronecker
    (CStarMatrix.ofMatrix.symm G) (CStarMatrix.ofMatrix.symm E)

/-- Tensoring the order-three diagonal group sum with an untouched-register
EPR projector gives a positive Choi support. -/
theorem finiteChoiKronecker_pairSum_EPR_nonneg
    {I S T : Type*}
    [Fintype I] [Fintype S] [Fintype T]
    [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (rho : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (hrho : ∀ sigma tau, rho (sigma * tau) = rho sigma * rho tau)
    (hrhoInv : ∀ sigma, rho sigma⁻¹ = (rho sigma)⁻¹) :
    0 ≤ finiteChoiKroneckerReindex e
      (finiteThreeMomentPairSum rho) finiteEPRProjector := by
  let R := finiteChoiKroneckerReindex e
    (finiteThreeMomentPairSum rho) (finiteEPRProjector (I := T))
  have hself : IsSelfAdjoint R := by
    unfold IsSelfAdjoint R
    rw [finiteChoiKroneckerReindex_star,
      (finiteThreeMomentPairSum_isSelfAdjoint rho hrhoInv).star_eq,
      (finiteEPRProjector_isSelfAdjoint (T := T)).star_eq]
  have hsq : R * R =
      ((6 * Fintype.card T : ℕ) : ℂ) • R := by
    unfold R
    rw [finiteChoiKroneckerReindex_mul,
      finiteThreeMomentPairSum_sq rho hrho, finiteEPRProjector_sq]
    apply CStarMatrix.ext
    intro i j
    simp only [finiteChoiKroneckerReindex, CStarMatrix.ofMatrix_apply,
      Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
      Matrix.kronecker_apply, Matrix.submatrix_apply,
      Matrix.kronecker, Matrix.kroneckerMap, Matrix.of_apply,
      CStarMatrix.smul_apply, CStarMatrix.ofMatrix_symm_apply,
      ofMatrix_symm_complex_smul]
    push_cast
    ring_nf
  have hstarSq : star R * R =
      ((6 * Fintype.card T : ℕ) : ℂ) • R := by
    rw [hself.star_eq, hsq]
  have hstarSqReal : star R * R =
      (6 * (Fintype.card T : ℝ)) • R := by
    rw [hstarSq]
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.smul_apply, Complex.real_smul, smul_eq_mul]
    push_cast
    rfl
  have hk : (0 : ℝ) < 6 * Fintype.card T := by
    positivity
  have hscaled : 0 ≤ (6 * (Fintype.card T : ℝ))⁻¹ • (star R * R) :=
    smul_nonneg (by positivity) (star_mul_self_nonneg R)
  rw [hstarSqReal] at hscaled
  simpa only [smul_smul, inv_mul_cancel₀ hk.ne', one_smul] using hscaled

/-- Replica-slot representation on two physical subsystems. -/
def threeReplicaABSlotPermutation (A B : Type*)
    (sigma : Equiv.Perm (Fin 3)) : Equiv.Perm (ThreeReplicaAB A B) :=
  (threeReplicaSlotPermutation A sigma).prodCongr
    (threeReplicaSlotPermutation B sigma)

theorem threeReplicaABSlotPermutation_mul (A B : Type*)
    (sigma tau : Equiv.Perm (Fin 3)) :
    threeReplicaABSlotPermutation A B (sigma * tau) =
      threeReplicaABSlotPermutation A B sigma *
        threeReplicaABSlotPermutation A B tau := by
  ext x <;> rfl

theorem threeReplicaABSlotPermutation_inv (A B : Type*)
    (sigma : Equiv.Perm (Fin 3)) :
    threeReplicaABSlotPermutation A B sigma⁻¹ =
      (threeReplicaABSlotPermutation A B sigma)⁻¹ := by
  ext x <;> rfl

/-- Coordinate equivalence for a three-replica register. -/
def threeReplicaEquivTriple (B : Type*) :
    ThreeReplica B ≃ B × B × B where
  toFun x := (x 0, x 1, x 2)
  invFun x i := if i = 0 then x.1 else if i = 1 then x.2.1 else x.2.2
  left_inv x := by
    funext i
    fin_cases i <;> simp
  right_inv x := by
    rcases x with ⟨x0, x1, x2⟩
    simp

theorem finThree_fun_eq_iff {B : Type*} (x y : Fin 3 → B) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨h0, h1, h2⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

@[simp] theorem finThree_eq_chain_forward {B : Type*} (x x1 x2 : B) :
    (x = x2 ∧ x = x1 ∧ x1 = x2) ↔ (x1 = x ∧ x2 = x) := by
  aesop

@[simp] theorem finThree_eq_chain_backward {B : Type*} (x x1 x2 : B) :
    (x = x1 ∧ x1 = x2 ∧ x = x2) ↔ (x1 = x ∧ x2 = x) := by
  aesop

@[simp] theorem card_filter_finThree_eq_chain {B : Type*}
    [Fintype B] [DecidableEq B] (x x1 : B) :
    ((Finset.univ.filter fun x2 : B ↦ x = x1 ∧ x = x2).card) =
      if x = x1 then 1 else 0 := by
  by_cases h : x = x1
  · subst x1
    rw [show (Finset.univ.filter fun x2 : B ↦ x = x ∧ x = x2) = {x} by
      ext y
      simp [eq_comm]]
    simp
  · simp [h]

set_option maxHeartbeats 1200000 in
/-- Exact overlap count: a slot permutation fixes one three-replica basis
vector for each assignment of a basis value to one of its cycles. -/
theorem sum_threeReplicaSlotPermutation_fixed_indicator
    (B : Type*) [Fintype B] [DecidableEq B]
    (pi : Equiv.Perm (Fin 3)) :
    (∑ x : ThreeReplica B,
      if threeReplicaSlotPermutation B pi x = x then (1 : ℂ) else 0) =
      (Fintype.card B : ℂ) ^ finThreeFullCycleCount pi := by
  rcases finThreePerm_eq_six pi with h | h | h | h | h | h <;> subst pi
  all_goals
    calc
      (∑ x : ThreeReplica B,
        if threeReplicaSlotPermutation B _ x = x then (1 : ℂ) else 0) =
          ∑ x : B × B × B,
            if threeReplicaSlotPermutation B _
                ((threeReplicaEquivTriple B).symm x) =
              (threeReplicaEquivTriple B).symm x then (1 : ℂ) else 0 :=
        ((threeReplicaEquivTriple B).symm.sum_comp _).symm
      _ = _ := by
        simp_rw [Fintype.sum_prod_type]
        simp +decide [threeReplicaEquivTriple,
          threeReplicaSlotPermutation, finThreeFullCycleCount,
          finThreeCycleForward, finThreeCycleBackward, finThree_fun_eq_iff,
          eq_comm, pow_succ]
        try ring

/-- Reassociate `A,B,C` as the acted-on subsystem `B,C` followed by the
untouched subsystem `A`. -/
def threeReplicaABCEquivBC_A (A B C : Type*) :
    ThreeReplicaABC A B C ≃ ThreeReplicaAB B C × ThreeReplica A where
  toFun x := ((x.2.1, x.2.2), x.1)
  invFun x := (x.2, x.1.1, x.1.2)
  left_inv x := rfl
  right_inv x := rfl

/-- Literal raw Choi matrix of `(Phi_a)_AB tensor id_C`. -/
def finiteThreeMomentABReferenceChoi
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  (((Fintype.card A * Fintype.card B : ℕ) : ℝ) ^ 3)⁻¹ •
    finiteChoiKroneckerReindex (threeReplicaABCEquivAB_C A B C)
      (finiteThreeMomentPairSum (threeReplicaABSlotPermutation A B))
      finiteEPRProjector

/-- Literal raw Choi matrix of `(Phi_a)_BC tensor id_A`. -/
def finiteThreeMomentBCReferenceChoi
    (A B C : Type*)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  (((Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ •
    finiteChoiKroneckerReindex (threeReplicaABCEquivBC_A A B C)
      (finiteThreeMomentPairSum (threeReplicaABSlotPermutation B C))
      finiteEPRProjector

@[simp] theorem finiteThreeMomentABReferenceChoi_apply
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (i a j b : ThreeReplicaABC A B C) :
    finiteThreeMomentABReferenceChoi A B C (i, a) (j, b) =
      ((((Fintype.card A * Fintype.card B : ℕ) : ℝ) ^ 3)⁻¹ : ℂ) *
        (∑ tau : Equiv.Perm (Fin 3),
          finiteThreeMomentPairQ (threeReplicaABSlotPermutation A B) tau tau
            ((i.1, i.2.1), (a.1, a.2.1))
            ((j.1, j.2.1), (b.1, b.2.1))) *
        (if i.2.2 = a.2.2 ∧ j.2.2 = b.2.2 then 1 else 0) := by
  simp [finiteThreeMomentABReferenceChoi, finiteThreeMomentPairSum,
    finiteEPRProjector, finiteChoiKroneckerReindex,
    finiteChoiTensorEquiv, finiteChoiProductEquiv,
    threeReplicaABCEquivAB_C, Finset.mul_sum]

@[simp] theorem finiteThreeMomentBCReferenceChoi_apply
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (i a j b : ThreeReplicaABC A B C) :
    finiteThreeMomentBCReferenceChoi A B C (i, a) (j, b) =
      ((((Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℂ) *
        (∑ sigma : Equiv.Perm (Fin 3),
          finiteThreeMomentPairQ (threeReplicaABSlotPermutation B C) sigma sigma
            ((i.2.1, i.2.2), (a.2.1, a.2.2))
            ((j.2.1, j.2.2), (b.2.1, b.2.2))) *
        (if i.1 = a.1 ∧ j.1 = b.1 then 1 else 0) := by
  simp [finiteThreeMomentBCReferenceChoi, finiteThreeMomentPairSum,
    finiteEPRProjector, finiteChoiKroneckerReindex,
    finiteChoiTensorEquiv, finiteChoiProductEquiv,
    threeReplicaABCEquivBC_A, Finset.mul_sum]

/-- Positive real scalar multiplication preserves spectral positivity on a
finite complex matrix algebra.  Keeping the carrier abstract avoids a
typeclass elaboration issue for expanded heterogeneous product indices. -/
theorem cstarMatrix_real_smul_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    {r : ℝ} {X : CStarMatrix I I ℂ} (hr : 0 ≤ r) (hX : 0 ≤ X) :
    0 ≤ r • X :=
  smul_nonneg hr hX

theorem finiteThreeMomentABReferenceChoi_nonneg
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    0 ≤ finiteThreeMomentABReferenceChoi A B C := by
  classical
  unfold finiteThreeMomentABReferenceChoi
  apply cstarMatrix_real_smul_nonneg (by positivity)
  exact finiteChoiKronecker_pairSum_EPR_nonneg
    (threeReplicaABCEquivAB_C A B C)
    (threeReplicaABSlotPermutation A B)
    (threeReplicaABSlotPermutation_mul A B)
    (threeReplicaABSlotPermutation_inv A B)

theorem finiteThreeMomentBCReferenceChoi_nonneg
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    0 ≤ finiteThreeMomentBCReferenceChoi A B C := by
  classical
  unfold finiteThreeMomentBCReferenceChoi
  apply cstarMatrix_real_smul_nonneg (by positivity)
  exact finiteChoiKronecker_pairSum_EPR_nonneg
    (threeReplicaABCEquivBC_A A B C)
    (threeReplicaABSlotPermutation B C)
    (threeReplicaABSlotPermutation_mul B C)
    (threeReplicaABSlotPermutation_inv B C)

/-- The linear map whose Choi matrix is a prescribed finite matrix. -/
def finiteLinearMapOfChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ where
  toFun X := fun a b ↦ ∑ i : I, ∑ j : I, X i j * C (i, a) (j, b)
  map_add' X Y := by
    apply CStarMatrix.ext
    intro a b
    change (∑ i : I, ∑ j : I, (X i j + Y i j) * C (i, a) (j, b)) =
      (∑ i : I, ∑ j : I, X i j * C (i, a) (j, b)) +
        ∑ i : I, ∑ j : I, Y i j * C (i, a) (j, b)
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    apply CStarMatrix.ext
    intro a b
    change (∑ i : I, ∑ j : I, (c * X i j) * C (i, a) (j, b)) =
      c * ∑ i : I, ∑ j : I, X i j * C (i, a) (j, b)
    simp only [mul_assoc, Finset.mul_sum]

@[simp] theorem finiteChoiMatrix_finiteLinearMapOfChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : CStarMatrix (I × I) (I × I) ℂ) :
    finiteChoiMatrix (finiteLinearMapOfChoi C) = C := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  change (∑ x : I, ∑ y : I,
    finiteCStarMatrixUnit i j x y * C (x, a) (y, b)) = C (i, a) (j, b)
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [finiteCStarMatrixUnit]
    · intro y hy hyj
      simp [finiteCStarMatrixUnit, hyj]
    · simp
  · intro x hx hxi
    simp [finiteCStarMatrixUnit, hxi]
  · simp

@[simp] theorem finiteLinearMapOfChoi_unit_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : CStarMatrix (I × I) (I × I) ℂ) (i j a b : I) :
    finiteLinearMapOfChoi D (finiteCStarMatrixUnit i j) a b =
      D (i, a) (j, b) := by
  change (∑ x : I, ∑ y : I,
    finiteCStarMatrixUnit i j x y * D (x, a) (y, b)) = D (i, a) (j, b)
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [finiteCStarMatrixUnit]
    · intro y hy hyj
      simp [finiteCStarMatrixUnit, hyj]
    · simp
  · intro x hx hxi
    simp [finiteCStarMatrixUnit, hxi]
  · simp

/-- Canonical completely positive map reconstructed from a concrete
nonnegative finite Choi matrix. -/
noncomputable def finiteCPMapOfNonnegativeChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : CStarMatrix (I × I) (I × I) ℂ) (hC : 0 ≤ C) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  Classical.choose <|
    exists_completelyPositiveMap_of_finiteChoiMatrix_nonneg
      (finiteLinearMapOfChoi C) (by simpa using hC)

theorem finiteCPMapOfNonnegativeChoi_toLinearMap
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : CStarMatrix (I × I) (I × I) ℂ) (hC : 0 ≤ C) :
    (finiteCPMapOfNonnegativeChoi C hC).toLinearMap =
      finiteLinearMapOfChoi C :=
  Classical.choose_spec <|
    exists_completelyPositiveMap_of_finiteChoiMatrix_nonneg
      (finiteLinearMapOfChoi C) (by simpa using hC)

@[simp] theorem finiteChoiMatrix_finiteCPMapOfNonnegativeChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (C : CStarMatrix (I × I) (I × I) ℂ) (hC : 0 ≤ C) :
    finiteChoiMatrix (finiteCPMapOfNonnegativeChoi C hC).toLinearMap = C := by
  rw [finiteCPMapOfNonnegativeChoi_toLinearMap,
    finiteChoiMatrix_finiteLinearMapOfChoi]

/-- Pointwise Choi contraction formula for two maps reconstructed from
concrete nonnegative Choi matrices. -/
theorem finiteChoiMatrix_comp_finiteCPMapOfNonnegativeChoi_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (C D : CStarMatrix (I × I) (I × I) ℂ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) (i a j b : I) :
    finiteChoiMatrix
      (CompletelyPositiveMap.comp
        (finiteCPMapOfNonnegativeChoi C hC)
        (finiteCPMapOfNonnegativeChoi D hD)).toLinearMap
      (i, a) (j, b) =
      ∑ x : I, ∑ y : I, D (i, x) (j, y) * C (x, a) (y, b) := by
  rw [finiteChoiMatrix_apply, CompletelyPositiveMap.comp_toLinearMap,
    LinearMap.comp_apply,
    finiteCPMapOfNonnegativeChoi_toLinearMap,
    finiteCPMapOfNonnegativeChoi_toLinearMap]
  change (∑ x : I, ∑ y : I,
    (finiteLinearMapOfChoi D (finiteCStarMatrixUnit i j)) x y *
      C (x, a) (y, b)) = _
  simp only [finiteLinearMapOfChoi_unit_apply]

/-- Concrete local approximate-Haar reference on `AB`, extended by the
identity on `C`. -/
noncomputable def finiteThreeMomentABReferenceCP
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :=
  finiteCPMapOfNonnegativeChoi (finiteThreeMomentABReferenceChoi A B C)
    (finiteThreeMomentABReferenceChoi_nonneg A B C)

/-- Concrete local approximate-Haar reference on `BC`, extended by the
identity on `A`. -/
noncomputable def finiteThreeMomentBCReferenceCP
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :=
  finiteCPMapOfNonnegativeChoi (finiteThreeMomentBCReferenceChoi A B C)
    (finiteThreeMomentBCReferenceChoi_nonneg A B C)

@[simp] theorem finiteThreeMomentABReferenceCP_choi
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteChoiMatrix (finiteThreeMomentABReferenceCP A B C).toLinearMap =
      finiteThreeMomentABReferenceChoi A B C := by
  apply finiteChoiMatrix_finiteCPMapOfNonnegativeChoi

@[simp] theorem finiteThreeMomentBCReferenceCP_choi
    (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteChoiMatrix (finiteThreeMomentBCReferenceCP A B C).toLinearMap =
      finiteThreeMomentBCReferenceChoi A B C := by
  apply finiteChoiMatrix_finiteCPMapOfNonnegativeChoi

end

end TomographyOracleCore
