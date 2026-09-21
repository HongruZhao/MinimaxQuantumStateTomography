import TomographyOracleCore.FiniteUnitaryThirdTwirlCPBridge
import TomographyOracleCore.RelativeDesignThreeMomentConcretePermutation

namespace TomographyOracleCore

universe u v w z

open scoped CStarAlgebra

noncomputable section

local instance finiteUnitaryThirdTwirlFactorCPSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance finiteUnitaryThirdTwirlFactorCPStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Factor-basis CP representatives of finite third twirls

The finite-unitary construction uses the replica-major basis
`TripleIndex ((A × B) × C)`, whereas the three-moment gluing calculation
uses the subsystem-major basis `ThreeReplicaABC A B C`.  This file gives the
literal coordinate equivalence and transports completely positive maps across
it.  The local `AB`, local `BC`, and global `ABC` twirls consequently live on
one common matrix algebra.
-/

/-- Three copies of a product split into the product of the two three-copy
registers. -/
def tripleIndexProdEquiv (X : Type u) (Y : Type v) :
    TripleIndex (X × Y) ≃ TripleIndex X × TripleIndex Y where
  toFun x := ((x.1.1, x.2.1.1, x.2.2.1),
    (x.1.2, x.2.1.2, x.2.2.2))
  invFun x := ((x.1.1, x.2.1),
    ((x.1.2.1, x.2.2.1), (x.1.2.2, x.2.2.2)))
  left_inv x := rfl
  right_inv x := rfl

/-- A three-entry tuple and a function on `Fin 3` carry the same data. -/
def tripleIndexEquivThreeReplica (X : Type u) :
    TripleIndex X ≃ ThreeReplica X where
  toFun x := ![x.1, x.2.1, x.2.2]
  invFun f := (f 0, f 1, f 2)
  left_inv x := by
    rcases x with ⟨x₀, x₁, x₂⟩
    rfl
  right_inv f := by
    funext i
    fin_cases i <;> rfl

/-- Replica-major coordinates on `((A × B) × C)³` are equivalent to
the subsystem-major `A³ × B³ × C³` coordinates used in B.26. -/
def tripleIndexABCEquiv
    (A : Type u) (B : Type v) (C : Type w) :
    TripleIndex ((A × B) × C) ≃ ThreeReplicaABC A B C :=
  (tripleIndexProdEquiv (A × B) C).trans <|
    ((tripleIndexProdEquiv A B).prodCongr
      (Equiv.refl (TripleIndex C))).trans <|
    (Equiv.prodAssoc (TripleIndex A) (TripleIndex B)
      (TripleIndex C)).trans <|
    (tripleIndexEquivThreeReplica A).prodCongr
      ((tripleIndexEquivThreeReplica B).prodCongr
        (tripleIndexEquivThreeReplica C))

/-- The analogous register reorder for a `BC` operation tensored with an
identity on `A`. -/
def threeReplicaBCAEquivABC
    (A : Type u) (B : Type v) (C : Type w) :
    ThreeReplicaABC B C A ≃ ThreeReplicaABC A B C where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv x := rfl
  right_inv x := rfl

/-- Replica-major coordinates for `(B × C) × A`, reordered onto the same
subsystem-major `A,B,C` basis. -/
def tripleIndexBCAEquivABC
    (A : Type u) (B : Type v) (C : Type w) :
    TripleIndex ((B × C) × A) ≃ ThreeReplicaABC A B C :=
  (tripleIndexABCEquiv B C A).trans (threeReplicaBCAEquivABC A B C)

/-- Coordinate reindexing of a finite matrix algebra as a completely
positive map.  This is the CP coercion of the corresponding star-algebra
equivalence. -/
def cstarMatrixReindexCP
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J) :
    CStarMatrix I I ℂ →CP CStarMatrix J J ℂ :=
  CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (CStarMatrix.reindexₐ ℂ ℂ e)

@[simp] theorem cstarMatrixReindexCP_apply
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J) (X : CStarMatrix I I ℂ) :
    (cstarMatrixReindexCP e).toLinearMap X =
      CStarMatrix.reindexₐ ℂ ℂ e X := rfl

/-- Conjugate a CP map by a coordinate equivalence. -/
def CompletelyPositiveMap.reindexEquiv
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J)
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CStarMatrix J J ℂ →CP CStarMatrix J J ℂ :=
  CompletelyPositiveMap.comp (cstarMatrixReindexCP e) <|
    CompletelyPositiveMap.comp Phi (cstarMatrixReindexCP e.symm)

@[simp] theorem CompletelyPositiveMap.reindexEquiv_apply
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J)
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (X : CStarMatrix J J ℂ) :
    (CompletelyPositiveMap.reindexEquiv e Phi).toLinearMap X =
      CStarMatrix.reindexₐ ℂ ℂ e
        (Phi.toLinearMap (CStarMatrix.reindexₐ ℂ ℂ e.symm X)) := rfl

/-- Coordinate transport preserves composition of CP maps. -/
theorem CompletelyPositiveMap.reindexEquiv_comp
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    (e : I ≃ J)
    (Phi Psi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CompletelyPositiveMap.reindexEquiv e
        (CompletelyPositiveMap.comp Phi Psi) =
      CompletelyPositiveMap.comp
        (CompletelyPositiveMap.reindexEquiv e Phi)
        (CompletelyPositiveMap.reindexEquiv e Psi) := by
  apply DFunLike.coe_injective
  funext X
  change CStarMatrix.reindexₐ ℂ ℂ e
      (Phi.toLinearMap
        (Psi.toLinearMap (CStarMatrix.reindexₐ ℂ ℂ e.symm X))) =
    CStarMatrix.reindexₐ ℂ ℂ e
      (Phi.toLinearMap
        (CStarMatrix.reindexₐ ℂ ℂ e.symm
          (CStarMatrix.reindexₐ ℂ ℂ e
            (Psi.toLinearMap
              (CStarMatrix.reindexₐ ℂ ℂ e.symm X)))))
  rw [CStarMatrix.reindexₐ_symm,
    (CStarMatrix.reindexₐ ℂ ℂ e).symm_apply_apply]

/-- The local finite `AB` twirl, tensored with identity on `C` and transported
to the common subsystem-major three-replica basis. -/
def finiteUnitaryThirdTwirlABTensorIdC_CP
    (A : Type u) (B : Type v) (C : Type w) {E : Type z}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype E] [Nonempty E]
    (UAB : E → Matrix.unitaryGroup (A × B) ℂ) :
    CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ :=
  CompletelyPositiveMap.reindexEquiv (tripleIndexABCEquiv A B C)
    (finiteUnitaryThirdTwirlTensorIdCP (J := C) UAB)

@[simp] theorem finiteUnitaryThirdTwirlABTensorIdC_CP_apply
    (A : Type u) (B : Type v) (C : Type w) {E : Type z}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype E] [Nonempty E]
    (UAB : E → Matrix.unitaryGroup (A × B) ℂ)
    (X : CStarMatrix (ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C) ℂ) :
    (finiteUnitaryThirdTwirlABTensorIdC_CP A B C UAB).toLinearMap X =
      CStarMatrix.reindexₐ ℂ ℂ (tripleIndexABCEquiv A B C)
        ((finiteUnitaryThirdTwirlTensorIdCP (J := C) UAB).toLinearMap
          (CStarMatrix.reindexₐ ℂ ℂ
            (tripleIndexABCEquiv A B C).symm X)) := rfl

/-- The local finite `BC` twirl, tensored with identity on `A` and transported
with the cyclic register reorder to the common basis. -/
def finiteUnitaryThirdTwirlBCTensorIdA_CP
    (A : Type u) (B : Type v) (C : Type w) {E : Type z}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype E] [Nonempty E]
    (UBC : E → Matrix.unitaryGroup (B × C) ℂ) :
    CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ :=
  CompletelyPositiveMap.reindexEquiv (tripleIndexBCAEquivABC A B C)
    (finiteUnitaryThirdTwirlTensorIdCP (J := A) UBC)

@[simp] theorem finiteUnitaryThirdTwirlBCTensorIdA_CP_apply
    (A : Type u) (B : Type v) (C : Type w) {E : Type z}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype E] [Nonempty E]
    (UBC : E → Matrix.unitaryGroup (B × C) ℂ)
    (X : CStarMatrix (ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C) ℂ) :
    (finiteUnitaryThirdTwirlBCTensorIdA_CP A B C UBC).toLinearMap X =
      CStarMatrix.reindexₐ ℂ ℂ (tripleIndexBCAEquivABC A B C)
        ((finiteUnitaryThirdTwirlTensorIdCP (J := A) UBC).toLinearMap
          (CStarMatrix.reindexₐ ℂ ℂ
            (tripleIndexBCAEquivABC A B C).symm X)) := rfl

/-- A global finite `ABC` third twirl transported to the common
subsystem-major basis. -/
def finiteUnitaryThirdTwirlABC_CP
    (A : Type u) (B : Type v) (C : Type w) {E : Type z}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype E] [Nonempty E]
    (UABC : E → Matrix.unitaryGroup ((A × B) × C) ℂ) :
    CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ :=
  CompletelyPositiveMap.reindexEquiv (tripleIndexABCEquiv A B C)
    (finiteUnitaryThirdTwirlCP UABC)

@[simp] theorem finiteUnitaryThirdTwirlABC_CP_apply
    (A : Type u) (B : Type v) (C : Type w) {E : Type z}
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [Fintype E] [Nonempty E]
    (UABC : E → Matrix.unitaryGroup ((A × B) × C) ℂ)
    (X : CStarMatrix (ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C) ℂ) :
    (finiteUnitaryThirdTwirlABC_CP A B C UABC).toLinearMap X =
      CStarMatrix.reindexₐ ℂ ℂ (tripleIndexABCEquiv A B C)
        ((finiteUnitaryThirdTwirlCP UABC).toLinearMap
          (CStarMatrix.reindexₐ ℂ ℂ
            (tripleIndexABCEquiv A B C).symm X)) := rfl

end


end TomographyOracleCore
