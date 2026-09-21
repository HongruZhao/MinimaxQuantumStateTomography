import TomographyOracleCore.RelativeDesignThreeMomentPermutationSupport
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace TomographyOracleCore

open scoped CStarAlgebra Matrix.Norms.L2Operator

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-!
# Concrete order-three register permutations for Eq. (B.26)

The first Choi copy carries `tau` on `A,B` and `sigma` on `C`; the second
copy carries `tau` on `A` and `sigma` on `B,C`.  These are exactly the two
permutation tensors

`tau_AB sigma_C tensor tau_A sigma_BC`

in Schuster--Haferkamp--Huang Eq. (B.26), written on a factorized finite
computational basis.
-/

/-- Three replica slots of a finite basis. -/
abbrev ThreeReplica (X : Type*) := Fin 3 → X

/-- Factorized basis for three replicas of `A tensor B tensor C`. -/
abbrev ThreeReplicaABC (A B C : Type*) :=
  ThreeReplica A × ThreeReplica B × ThreeReplica C

/-- The usual permutation of three replica slots. -/
def threeReplicaSlotPermutation (X : Type*)
    (sigma : Equiv.Perm (Fin 3)) : Equiv.Perm (ThreeReplica X) :=
  Equiv.arrowCongr sigma (Equiv.refl X)

@[simp]
theorem threeReplicaSlotPermutation_apply
    (X : Type*) (sigma : Equiv.Perm (Fin 3)) (x : ThreeReplica X)
    (i : Fin 3) :
    threeReplicaSlotPermutation X sigma x i = x (sigma⁻¹ i) := rfl

/-- Replica-slot permutations multiply as the original permutations do. -/
theorem threeReplicaSlotPermutation_mul
    (X : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    threeReplicaSlotPermutation X (sigma * tau) =
      threeReplicaSlotPermutation X sigma *
        threeReplicaSlotPermutation X tau := by
  rfl

/-- Replica-slot permutations commute with inversion. -/
theorem threeReplicaSlotPermutation_inv
    (X : Type*) (sigma : Equiv.Perm (Fin 3)) :
    threeReplicaSlotPermutation X sigma⁻¹ =
      (threeReplicaSlotPermutation X sigma)⁻¹ := by
  rfl

/-- The literal two-copy register permutation in B.26. -/
def finiteThreeMomentB26RegisterPermutation
    (A B C : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    Equiv.Perm (ThreeReplicaABC A B C × ThreeReplicaABC A B C) :=
  ((threeReplicaSlotPermutation A tau).prodCongr
      ((threeReplicaSlotPermutation B tau).prodCongr
        (threeReplicaSlotPermutation C sigma))).prodCongr
    ((threeReplicaSlotPermutation A tau).prodCongr
      ((threeReplicaSlotPermutation B sigma).prodCongr
        (threeReplicaSlotPermutation C sigma)))

/-- The B.26 register permutations form a two-index representation. -/
theorem finiteThreeMomentB26RegisterPermutation_mul
    (A B C : Type*)
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentB26RegisterPermutation A B C (sigma * sigma') (tau * tau') =
      finiteThreeMomentB26RegisterPermutation A B C sigma tau *
        finiteThreeMomentB26RegisterPermutation A B C sigma' tau' := by
  ext x <;> rfl

/-- Simultaneous inversion is the inverse register permutation. -/
theorem finiteThreeMomentB26RegisterPermutation_inv
    (A B C : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    finiteThreeMomentB26RegisterPermutation A B C sigma⁻¹ tau⁻¹ =
      (finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹ := by
  ext x <;> rfl

/-- Concrete B.26 permutation tensor as a finite C-star matrix.  Mathlib's
`permMatrixHom` inserts the inverse required to turn the contravariant
`permMatrix` convention into a genuine representation. -/
def finiteThreeMomentB26Q
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  by
    classical
    exact CStarMatrix.ofMatrix <|
      Matrix.permMatrixHom (R := ℂ)
        (finiteThreeMomentB26RegisterPermutation A B C sigma tau)

/-- The concrete B.26 tensors have operator norm at most one. -/
theorem finiteThreeMomentB26Q_norm_le_one
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖finiteThreeMomentB26Q A B C sigma tau‖ ≤ 1 := by
  classical
  have hunit : finiteThreeMomentB26Q A B C sigma tau ∈
      unitary (CStarMatrix
        (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ) := by
    constructor
    · change star (((finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹
          ).permMatrix ℂ) *
          ((finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹
            ).permMatrix ℂ =
        (1 : Matrix
          (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
          (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ)
      simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
    · change ((finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹
          ).permMatrix ℂ *
          star (((finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹
            ).permMatrix ℂ) =
        (1 : Matrix
          (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
          (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ)
      simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
  exact le_of_eq (CStarRing.norm_of_mem_unitary hunit)

/-- Concrete multiplication law for the B.26 permutation tensors. -/
theorem finiteThreeMomentB26Q_mul
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentB26Q A B C sigma tau *
        finiteThreeMomentB26Q A B C sigma' tau' =
      finiteThreeMomentB26Q A B C (sigma * sigma') (tau * tau') := by
  classical
  apply CStarMatrix.ofMatrix.injective
  change ((finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹
        ).permMatrix ℂ *
      ((finiteThreeMomentB26RegisterPermutation A B C sigma' tau')⁻¹
        ).permMatrix ℂ =
    ((finiteThreeMomentB26RegisterPermutation A B C
        (sigma * sigma') (tau * tau'))⁻¹).permMatrix ℂ
  rw [← Matrix.permMatrix_mul,
    finiteThreeMomentB26RegisterPermutation_mul]
  simp

/-- Concrete adjoint law for the B.26 permutation tensors. -/
theorem finiteThreeMomentB26Q_star
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentB26Q A B C sigma tau) =
      finiteThreeMomentB26Q A B C sigma⁻¹ tau⁻¹ := by
  classical
  apply CStarMatrix.ofMatrix.injective
  change star (((finiteThreeMomentB26RegisterPermutation A B C sigma tau)⁻¹
      ).permMatrix ℂ) =
    ((finiteThreeMomentB26RegisterPermutation A B C sigma⁻¹ tau⁻¹)⁻¹
      ).permMatrix ℂ
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix]
  rw [finiteThreeMomentB26RegisterPermutation_inv]

/-- B.26/B.27 reference gluing for the literal finite register-permutation
tensors.  Only the two Choi identities from B.26 remain as premises; all
norm and representation structure is now proved. -/
theorem relativeCPApproximation_threeMoment_referenceComposition_of_concreteB26
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (Dglobal Doverlap : ℕ) (hglobal : 0 < Dglobal)
    (hoverlap : 2 ≤ Doverlap)
    (HAB HBC HABC :
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
        CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ)
    (hcomposedB26 :
      finiteChoiMatrix (CompletelyPositiveMap.comp HAB HBC).toLinearMap =
        finiteThreeMomentComposedReferenceChoi Dglobal Doverlap
          (finiteThreeMomentB26Q A B C))
    (hglobalB26 : finiteChoiMatrix HABC.toLinearMap =
      finiteThreeMomentGlobalReferenceChoi Dglobal
        (finiteThreeMomentB26Q A B C)) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Doverlap : ℝ))) - 1)
      (CompletelyPositiveMap.comp HAB HBC).toLinearMap
      HABC.toLinearMap := by
  exact
    relativeCPApproximation_threeMoment_referenceComposition_of_B26_representation
      Dglobal Doverlap hglobal hoverlap
      (finiteThreeMomentB26Q A B C)
      (finiteThreeMomentB26Q_norm_le_one A B C)
      (finiteThreeMomentB26Q_mul A B C)
      (finiteThreeMomentB26Q_star A B C)
      HAB HBC HABC hcomposedB26 hglobalB26

end

end TomographyOracleCore
