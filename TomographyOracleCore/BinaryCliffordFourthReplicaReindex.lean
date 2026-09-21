import Mathlib.Logic.Equiv.Fin.Basic
import TomographyOracleCore.BinaryCliffordFiniteFourthRepresentation
import TomographyOracleCore.PeriodicCliffordFourthSectorOperatorCoordinates

namespace TomographyOracleCore

/-!
# Reindexing four binary-word replicas by qubit

The literal fourth tensor power is indexed by four binary words, whereas
the certified sector matrices are indexed by one four-bit vector at each
qubit.  This file gives the explicit finite equivalence between those two
coordinate conventions and transports arbitrary matrices and simple
four-fold tensors across it.

This is only a coordinate bridge.  It makes no assertion that a sector
matrix is a stochastic-Lagrangian operator and proves no Clifford
invariance statement.
-/

/-- The canonical representative identifies `ZMod 2` with `Fin 2`. -/
def zmodTwoEquivFinTwo : ZMod 2 ≃ Fin 2 where
  toFun x := ⟨x.val, x.val_lt⟩
  invFun i := (i.val : ZMod 2)
  left_inv x := ZMod.natCast_zmod_val x
  right_inv i := by
    apply Fin.ext
    exact ZMod.val_natCast_of_lt i.isLt

/-- Reversal of four right-associated coordinates. -/
def reverseFourthIndexEquiv (α : Type*) :
    FourthIndex α ≃ FourthIndex α where
  toFun x := (x.2.2.2, x.2.2.1, x.2.1, x.1)
  invFun x := (x.2.2.2, x.2.2.1, x.2.1, x.1)
  left_inv x := by
    rcases x with ⟨x₁, x₂, x₃, x₄⟩
    rfl
  right_inv x := by
    rcases x with ⟨x₁, x₂, x₃, x₄⟩
    rfl

/-- Two binary digits in little-endian product order. -/
def finTwoPairEquivFinFour :
    Fin 2 × Fin 2 ≃ Fin 4 :=
  finProdFinEquiv

/-- Three binary digits in little-endian product order. -/
def finTwoTripleEquivFinEight :
    Fin 2 × Fin 2 × Fin 2 ≃ Fin 8 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finTwoPairEquivFinFour).trans
    finProdFinEquiv

/-- Four binary digits in little-endian product order. -/
def finTwoFourthEquivFinSixteen :
    FourthIndex (Fin 2) ≃ Fin 16 :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finTwoTripleEquivFinEight).trans
    finProdFinEquiv

/-- Four `ZMod 2` coordinates as a four-bit vector.  The reversal before
`finProdFinEquiv` makes the first tensor-replica coordinate the least
significant bit, the second coordinate bit one, and so on. -/
def zmodTwoFourthEquivBitVecFour :
    FourthIndex (ZMod 2) ≃ QubitFourthReplicaIndex :=
  (Equiv.prodCongr zmodTwoEquivFinTwo
      (Equiv.prodCongr zmodTwoEquivFinTwo
        (Equiv.prodCongr zmodTwoEquivFinTwo zmodTwoEquivFinTwo))).trans
    ((reverseFourthIndexEquiv (Fin 2)).trans
      (finTwoFourthEquivFinSixteen.trans
        (BitVec.equivFin (m := 4)).toEquiv.symm))

/-- Transpose four length-`K` binary words into one four-bit replica index
at each qubit. -/
def fourthIndexPauliBinaryWordEquiv (K : ℕ) :
    FourthIndex (PauliBinaryWord K) ≃
      QubitFourthBlockReplicaIndex K where
  toFun x a := zmodTwoFourthEquivBitVecFour
    (x.1 a, x.2.1 a, x.2.2.1 a, x.2.2.2 a)
  invFun v :=
    (fun a ↦ (zmodTwoFourthEquivBitVecFour.symm (v a)).1,
      fun a ↦ (zmodTwoFourthEquivBitVecFour.symm (v a)).2.1,
      fun a ↦ (zmodTwoFourthEquivBitVecFour.symm (v a)).2.2.1,
      fun a ↦ (zmodTwoFourthEquivBitVecFour.symm (v a)).2.2.2)
  left_inv x := by
    apply Prod.ext
    · funext a
      simp
    · apply Prod.ext
      · funext a
        simp
      · apply Prod.ext
        · funext a
          simp
        · funext a
          simp
  right_inv v := by
    funext a
    exact zmodTwoFourthEquivBitVecFour.apply_symm_apply (v a)

@[simp]
theorem fourthIndexPauliBinaryWordEquiv_apply
    (K : ℕ) (x : FourthIndex (PauliBinaryWord K)) (a : Fin K) :
    fourthIndexPauliBinaryWordEquiv K x a =
      zmodTwoFourthEquivBitVecFour
        (x.1 a, x.2.1 a, x.2.2.1 a, x.2.2.2 a) :=
  rfl

/-- Reindex square matrices from four-word coordinates to the block-replica
coordinates used by the fourth-sector matrices. -/
def fourthCopyBlockReplicaMatrixEquiv
    (K : ℕ) (R : Type*) :
    Matrix (FourthIndex (PauliBinaryWord K))
        (FourthIndex (PauliBinaryWord K)) R ≃
      Matrix (QubitFourthBlockReplicaIndex K)
        (QubitFourthBlockReplicaIndex K) R :=
  Matrix.reindex (fourthIndexPauliBinaryWordEquiv K)
    (fourthIndexPauliBinaryWordEquiv K)

@[simp]
theorem fourthCopyBlockReplicaMatrixEquiv_apply
    (K : ℕ) {R : Type*}
    (A : Matrix (FourthIndex (PauliBinaryWord K))
      (FourthIndex (PauliBinaryWord K)) R)
    (row column : QubitFourthBlockReplicaIndex K) :
    fourthCopyBlockReplicaMatrixEquiv K R A row column =
      A ((fourthIndexPauliBinaryWordEquiv K).symm row)
        ((fourthIndexPauliBinaryWordEquiv K).symm column) :=
  rfl

@[simp]
theorem fourthCopyBlockReplicaMatrixEquiv_symm_apply
    (K : ℕ) {R : Type*}
    (A : Matrix (QubitFourthBlockReplicaIndex K)
      (QubitFourthBlockReplicaIndex K) R)
    (row column : FourthIndex (PauliBinaryWord K)) :
    (fourthCopyBlockReplicaMatrixEquiv K R).symm A row column =
      A (fourthIndexPauliBinaryWordEquiv K row)
        (fourthIndexPauliBinaryWordEquiv K column) :=
  rfl

/-- A simple fourth tensor written in the block-replica coordinates used by
the sector matrices. -/
def matrixTensorFourInBlockReplicaCoordinates
    (K : ℕ)
    (A B C D : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (QubitFourthBlockReplicaIndex K)
      (QubitFourthBlockReplicaIndex K) ℂ :=
  fourthCopyBlockReplicaMatrixEquiv K ℂ
    (matrixTensorFour A B C D)

/-- Transported entry formula for the literal fourth tensor at arbitrary
block-replica row and column indices. -/
theorem matrixTensorFourInBlockReplicaCoordinates_apply
    (K : ℕ)
    (A B C D : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (row column : QubitFourthBlockReplicaIndex K) :
    matrixTensorFourInBlockReplicaCoordinates K A B C D row column =
      A ((fourthIndexPauliBinaryWordEquiv K).symm row).1
          ((fourthIndexPauliBinaryWordEquiv K).symm column).1 *
        B ((fourthIndexPauliBinaryWordEquiv K).symm row).2.1
          ((fourthIndexPauliBinaryWordEquiv K).symm column).2.1 *
        C ((fourthIndexPauliBinaryWordEquiv K).symm row).2.2.1
          ((fourthIndexPauliBinaryWordEquiv K).symm column).2.2.1 *
        D ((fourthIndexPauliBinaryWordEquiv K).symm row).2.2.2
          ((fourthIndexPauliBinaryWordEquiv K).symm column).2.2.2 := by
  rw [matrixTensorFourInBlockReplicaCoordinates,
    fourthCopyBlockReplicaMatrixEquiv_apply,
    matrixTensorFour_apply]

/-- The transported entry formula evaluated at the image of two literal
four-word indices. -/
@[simp]
theorem matrixTensorFourInBlockReplicaCoordinates_apply_equiv
    (K : ℕ)
    (A B C D : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (x y : FourthIndex (PauliBinaryWord K)) :
    matrixTensorFourInBlockReplicaCoordinates K A B C D
        (fourthIndexPauliBinaryWordEquiv K x)
        (fourthIndexPauliBinaryWordEquiv K y) =
      A x.1 y.1 * B x.2.1 y.2.1 *
        C x.2.2.1 y.2.2.1 * D x.2.2.2 y.2.2.2 := by
  rw [matrixTensorFourInBlockReplicaCoordinates_apply]
  simp

end TomographyOracleCore
