import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.BitVec
import Mathlib.Data.Finset.Card
import TomographyOracleCore.PeriodicCliffordFourthGramRowSum

namespace TomographyOracleCore

noncomputable section

set_option maxHeartbeats 5000000

local instance : Finite QubitFourthBinaryVector :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthBinaryVector :=
  Fintype.ofFinite _

/-!
# Explicit coordinate operators for the fourth-copy qubit sectors

An element of `BitVec 8` is the flattened pair of four-bit row and column
indices of a one-qubit, four-replica operator.  Thus a real-valued function
on `QubitFourthBinaryVector` is a concrete coordinate array for such an
operator.  The sector operator below is the `0`--`1` indicator of the
explicit sixteen-vector carrier already certified in
`PeriodicCliffordFourthSectors`.

This module proves, rather than assumes, that the Hilbert--Schmidt coordinate
Gram matrix of these operators is the certified matrix `G_2`.  It also forms
literal tensor-product coordinates on `r` qubits and proves their Gram
matrix is `G_(2^r)`.

The result is deliberately narrower than the physical Clifford-twirl bridge:
it does not yet identify this coordinate realization with the `R_r(T)`
operators in the stochastic-Lagrangian commutant theorem, nor does it prove
that the finite Clifford average is the projector onto their span.
-/

/-- The finite real coordinate space of a one-qubit, four-replica operator,
with its row and column indices flattened into `BitVec 8`. -/
abbrev QubitFourthOneQubitOperatorCoordinates :=
  QubitFourthBinaryVector → ℝ

/-- The explicit `0`--`1` coordinate array associated with sector `i`. -/
def qubitFourthOneQubitSectorOperator
    (i : Fin 30) : QubitFourthOneQubitOperatorCoordinates :=
  fun v ↦ if v ∈ qubitFourthSector i then 1 else 0

/-- The real Hilbert--Schmidt coordinate form on flattened operator arrays. -/
def qubitFourthOneQubitHilbertSchmidt
    (A B : QubitFourthOneQubitOperatorCoordinates) : ℝ :=
  ∑ v, A v * B v

/-- The Hilbert--Schmidt Gram entry of two explicit one-qubit sector
operators. -/
def qubitFourthOneQubitSectorGram (i j : Fin 30) : ℝ :=
  qubitFourthOneQubitHilbertSchmidt
    (qubitFourthOneQubitSectorOperator i)
    (qubitFourthOneQubitSectorOperator j)

/-- The Hilbert--Schmidt dot product of two sector indicators counts their
set-theoretic intersection. -/
theorem qubitFourthOneQubitSectorGram_eq_inter_card
    (i j : Fin 30) :
    qubitFourthOneQubitSectorGram i j =
      (((qubitFourthSector i).toFinset ∩
        (qubitFourthSector j).toFinset).card : ℝ) := by
  classical
  unfold qubitFourthOneQubitSectorGram
    qubitFourthOneQubitHilbertSchmidt
    qubitFourthOneQubitSectorOperator
  calc
    (∑ v : QubitFourthBinaryVector,
        (if v ∈ qubitFourthSector i then (1 : ℝ) else 0) *
          (if v ∈ qubitFourthSector j then (1 : ℝ) else 0)) =
        ∑ v : QubitFourthBinaryVector,
          if v ∈ (qubitFourthSector i).toFinset ∩
              (qubitFourthSector j).toFinset
            then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hi : v ∈ qubitFourthSector i <;>
        by_cases hj : v ∈ qubitFourthSector j <;>
          simp [hi, hj]
    _ = (((qubitFourthSector i).toFinset ∩
          (qubitFourthSector j).toFinset).card : ℝ) := by
      rw [Finset.sum_boole, Finset.filter_univ_mem]

/-- The list definition of `qubitFourthIntersectionCard` agrees with the
ordinary intersection cardinality.  Distinctness of the left carrier is the
only non-computational ingredient. -/
theorem qubitFourthSector_inter_toFinset_card
    (i j : Fin 30) :
    ((qubitFourthSector i).toFinset ∩
      (qubitFourthSector j).toFinset).card =
        qubitFourthIntersectionCard i j := by
  classical
  have h := (qubitFourthSector_valid i).1.card_eq_countP
    (P := fun v : QubitFourthBinaryVector ↦
      v ∈ (qubitFourthSector j).toFinset)
  rw [← Finset.filter_mem_eq_inter]
  rw [h]
  unfold qubitFourthIntersectionCard
  apply List.countP_congr
  intro v _hv
  simp

/-- Exact power-of-two cardinality of every one-qubit sector intersection.
This is a finite kernel certificate over the displayed thirty carriers. -/
theorem qubitFourthIntersectionCard_eq_two_pow_entry
    (i j : Fin 30) :
    qubitFourthIntersectionCard i j =
      2 ^ qubitFourthIntersectionEntry i j := by
  fin_cases i <;> fin_cases j <;> rfl

/-- The literal one-qubit operator-coordinate Hilbert--Schmidt Gram matrix
is exactly the certified scalar Gram matrix at local dimension `2`. -/
theorem qubitFourthOneQubitSectorGram_eq_gramMatrix
    (i j : Fin 30) :
    qubitFourthOneQubitSectorGram i j =
      qubitFourthGramMatrix 2 i j := by
  rw [qubitFourthOneQubitSectorGram_eq_inter_card,
    qubitFourthSector_inter_toFinset_card,
    qubitFourthIntersectionCard_eq_two_pow_entry]
  simp [qubitFourthGramMatrix]

/-! ## Literal matrix realization -/

/-- Four replica bits form the computational basis index of the four-copy
one-qubit Hilbert space. -/
abbrev QubitFourthReplicaIndex := BitVec 4

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-- Splitting a flattened eight-bit operator coordinate into its four-bit
row and four-bit column indices. -/
def qubitFourthRowColumnEquiv :
    (QubitFourthReplicaIndex × QubitFourthReplicaIndex) ≃
      QubitFourthBinaryVector where
  toFun p := p.1 ++ p.2
  invFun v := (v.extractLsb' 4 4, v.extractLsb' 0 4)
  left_inv p := by
    rcases p with ⟨row, column⟩
    apply Prod.ext
    · exact BitVec.extractLsb'_append_eq_left
    · exact BitVec.extractLsb'_append_eq_right
  right_inv v := BitVec.extractLsb'_append_extractLsb'

/-- The explicit one-qubit sector operator as a literal real `16 × 16`
matrix on the four-replica computational basis. -/
def qubitFourthOneQubitSectorMatrix
    (i : Fin 30) :
    Matrix QubitFourthReplicaIndex QubitFourthReplicaIndex ℝ :=
  fun row column ↦
    qubitFourthOneQubitSectorOperator i
      (qubitFourthRowColumnEquiv (row, column))

/-- Real Hilbert--Schmidt form for the literal one-qubit matrices.  The
sector matrices have real `0`--`1` entries, so this is the restriction of the
usual complex conjugate Hilbert--Schmidt form. -/
def qubitFourthOneQubitMatrixHilbertSchmidt
    (A B : Matrix QubitFourthReplicaIndex QubitFourthReplicaIndex ℝ) : ℝ :=
  ∑ row, ∑ column, A row column * B row column

/-- Unflattening the coordinates preserves the Hilbert--Schmidt form. -/
theorem qubitFourthOneQubitSectorMatrix_hilbertSchmidt_eq_coordinate
    (i j : Fin 30) :
    qubitFourthOneQubitMatrixHilbertSchmidt
        (qubitFourthOneQubitSectorMatrix i)
        (qubitFourthOneQubitSectorMatrix j) =
      qubitFourthOneQubitSectorGram i j := by
  classical
  unfold qubitFourthOneQubitMatrixHilbertSchmidt
    qubitFourthOneQubitSectorMatrix
    qubitFourthOneQubitSectorGram
    qubitFourthOneQubitHilbertSchmidt
  calc
    (∑ row : QubitFourthReplicaIndex,
        ∑ column : QubitFourthReplicaIndex,
          qubitFourthOneQubitSectorOperator i
              (qubitFourthRowColumnEquiv (row, column)) *
            qubitFourthOneQubitSectorOperator j
              (qubitFourthRowColumnEquiv (row, column))) =
        ∑ p : QubitFourthReplicaIndex × QubitFourthReplicaIndex,
          qubitFourthOneQubitSectorOperator i
              (qubitFourthRowColumnEquiv p) *
            qubitFourthOneQubitSectorOperator j
              (qubitFourthRowColumnEquiv p) := by
      symm
      exact Fintype.sum_prod_type _
    _ = ∑ v : QubitFourthBinaryVector,
          qubitFourthOneQubitSectorOperator i v *
            qubitFourthOneQubitSectorOperator j v := by
      apply Fintype.sum_equiv qubitFourthRowColumnEquiv
      intro p
      rfl

/-- Exact literal-matrix Hilbert--Schmidt Gram identity at one qubit. -/
theorem qubitFourthOneQubitSectorMatrix_hilbertSchmidt_eq_gramMatrix
    (i j : Fin 30) :
    qubitFourthOneQubitMatrixHilbertSchmidt
        (qubitFourthOneQubitSectorMatrix i)
        (qubitFourthOneQubitSectorMatrix j) =
      qubitFourthGramMatrix 2 i j := by
  rw [qubitFourthOneQubitSectorMatrix_hilbertSchmidt_eq_coordinate,
    qubitFourthOneQubitSectorGram_eq_gramMatrix]

/-! ## Literal tensor-product coordinates -/

/-- The flattened coordinate index for an `r`-qubit tensor product of
four-replica one-qubit operator arrays. -/
abbrev QubitFourthTensorOperatorIndex (r : ℕ) :=
  Fin r → QubitFourthBinaryVector

/-- The coordinate array of the `r`-fold tensor power of sector operator
`i`. -/
def qubitFourthTensorSectorOperator
    (r : ℕ) (i : Fin 30) (v : QubitFourthTensorOperatorIndex r) : ℝ :=
  ∏ a, qubitFourthOneQubitSectorOperator i (v a)

/-- Hilbert--Schmidt coordinate Gram entry of two literal `r`-fold tensor
sector operators. -/
def qubitFourthTensorSectorGram
    (r : ℕ) (i j : Fin 30) : ℝ :=
  ∑ v : QubitFourthTensorOperatorIndex r,
    qubitFourthTensorSectorOperator r i v *
      qubitFourthTensorSectorOperator r j v

/-- Hilbert--Schmidt tensorization: the tensor-coordinate Gram entry is the
`r`-th power of the one-qubit entry. -/
theorem qubitFourthTensorSectorGram_eq_pow
    (r : ℕ) (i j : Fin 30) :
    qubitFourthTensorSectorGram r i j =
      qubitFourthOneQubitSectorGram i j ^ r := by
  classical
  unfold qubitFourthTensorSectorGram qubitFourthTensorSectorOperator
    qubitFourthOneQubitSectorGram qubitFourthOneQubitHilbertSchmidt
  calc
    (∑ v : Fin r → QubitFourthBinaryVector,
        (∏ a, qubitFourthOneQubitSectorOperator i (v a)) *
          ∏ a, qubitFourthOneQubitSectorOperator j (v a)) =
        ∑ v : Fin r → QubitFourthBinaryVector,
          ∏ a, (qubitFourthOneQubitSectorOperator i (v a) *
            qubitFourthOneQubitSectorOperator j (v a)) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [← Finset.prod_mul_distrib]
    _ = (∑ v : QubitFourthBinaryVector,
          qubitFourthOneQubitSectorOperator i v *
            qubitFourthOneQubitSectorOperator j v) ^ r := by
      exact (Fintype.sum_pow
        (fun v : QubitFourthBinaryVector ↦
          qubitFourthOneQubitSectorOperator i v *
            qubitFourthOneQubitSectorOperator j v) r).symm

/-- Exact operator-coordinate Gram identity for every block dimension
`x = 2^r`: `tr(R_r(T)^* R_r(S)) = x^dim(T cap S)` at the coordinate level. -/
theorem qubitFourthTensorSectorGram_eq_gramMatrix
    (r : ℕ) (i j : Fin 30) :
    qubitFourthTensorSectorGram r i j =
      qubitFourthGramMatrix ((2 : ℝ) ^ r) i j := by
  rw [qubitFourthTensorSectorGram_eq_pow,
    qubitFourthOneQubitSectorGram_eq_gramMatrix]
  simp only [qubitFourthGramMatrix_apply]
  calc
    (((2 : ℝ) ^ qubitFourthIntersectionEntry i j) ^ r) =
        (2 : ℝ) ^ (qubitFourthIntersectionEntry i j * r) :=
      (pow_mul (2 : ℝ) (qubitFourthIntersectionEntry i j) r).symm
    _ = (2 : ℝ) ^ (r * qubitFourthIntersectionEntry i j) := by
      rw [Nat.mul_comm]
    _ = (((2 : ℝ) ^ r) ^ qubitFourthIntersectionEntry i j) :=
      pow_mul (2 : ℝ) r (qubitFourthIntersectionEntry i j)

/-! ## Literal block matrices -/

/-- Computational basis index for the four replicas of an `r`-qubit
block. -/
abbrev QubitFourthBlockReplicaIndex (r : ℕ) :=
  Fin r → QubitFourthReplicaIndex

/-- A pair of block row/column indices is equivalent to the flattened
tensor-operator coordinate used above. -/
def qubitFourthBlockRowColumnEquiv (r : ℕ) :
    (QubitFourthBlockReplicaIndex r × QubitFourthBlockReplicaIndex r) ≃
      QubitFourthTensorOperatorIndex r where
  toFun p a := qubitFourthRowColumnEquiv (p.1 a, p.2 a)
  invFun v :=
    (fun a ↦ (qubitFourthRowColumnEquiv.symm (v a)).1,
      fun a ↦ (qubitFourthRowColumnEquiv.symm (v a)).2)
  left_inv p := by
    rcases p with ⟨row, column⟩
    apply Prod.ext <;> funext a <;> simp
  right_inv v := by
    funext a
    simp

/-- The `r`-qubit sector operator as a literal matrix, entrywise equal to
the tensor product of its one-qubit sector matrices. -/
def qubitFourthBlockSectorMatrix
    (r : ℕ) (i : Fin 30) :
    Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℝ :=
  fun row column ↦
    ∏ a, qubitFourthOneQubitSectorMatrix i (row a) (column a)

/-- Real Hilbert--Schmidt form for literal `r`-qubit block matrices. -/
def qubitFourthBlockMatrixHilbertSchmidt
    (r : ℕ)
    (A B : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℝ) : ℝ :=
  ∑ row, ∑ column, A row column * B row column

/-- The literal block-matrix Hilbert--Schmidt form equals the previously
tensorized flattened-coordinate form. -/
theorem qubitFourthBlockSectorMatrix_hilbertSchmidt_eq_coordinate
    (r : ℕ) (i j : Fin 30) :
    qubitFourthBlockMatrixHilbertSchmidt r
        (qubitFourthBlockSectorMatrix r i)
        (qubitFourthBlockSectorMatrix r j) =
      qubitFourthTensorSectorGram r i j := by
  classical
  unfold qubitFourthBlockMatrixHilbertSchmidt
    qubitFourthBlockSectorMatrix
    qubitFourthOneQubitSectorMatrix
    qubitFourthTensorSectorGram
    qubitFourthTensorSectorOperator
  calc
    (∑ row : QubitFourthBlockReplicaIndex r,
        ∑ column : QubitFourthBlockReplicaIndex r,
          (∏ a, qubitFourthOneQubitSectorOperator i
              (qubitFourthRowColumnEquiv (row a, column a))) *
            ∏ a, qubitFourthOneQubitSectorOperator j
              (qubitFourthRowColumnEquiv (row a, column a))) =
        ∑ p : QubitFourthBlockReplicaIndex r ×
            QubitFourthBlockReplicaIndex r,
          (∏ a, qubitFourthOneQubitSectorOperator i
              (qubitFourthBlockRowColumnEquiv r p a)) *
            ∏ a, qubitFourthOneQubitSectorOperator j
              (qubitFourthBlockRowColumnEquiv r p a) := by
      symm
      exact Fintype.sum_prod_type _
    _ = ∑ v : QubitFourthTensorOperatorIndex r,
          (∏ a, qubitFourthOneQubitSectorOperator i (v a)) *
            ∏ a, qubitFourthOneQubitSectorOperator j (v a) := by
      apply Fintype.sum_equiv (qubitFourthBlockRowColumnEquiv r)
      intro p
      rfl

/-- Exact literal block-matrix Hilbert--Schmidt Gram identity for every
block dimension `2^r`. -/
theorem qubitFourthBlockSectorMatrix_hilbertSchmidt_eq_gramMatrix
    (r : ℕ) (i j : Fin 30) :
    qubitFourthBlockMatrixHilbertSchmidt r
        (qubitFourthBlockSectorMatrix r i)
        (qubitFourthBlockSectorMatrix r j) =
      qubitFourthGramMatrix ((2 : ℝ) ^ r) i j := by
  rw [qubitFourthBlockSectorMatrix_hilbertSchmidt_eq_coordinate,
    qubitFourthTensorSectorGram_eq_gramMatrix]

/-- The literal matrix whose entries are tensor-coordinate
Hilbert--Schmidt products. -/
def qubitFourthTensorSectorGramMatrix
    (r : ℕ) : Matrix (Fin 30) (Fin 30) ℝ :=
  fun i j ↦ qubitFourthTensorSectorGram r i j

/-- Matrix-level form of the exact tensor-coordinate Gram identity. -/
theorem qubitFourthTensorSectorGramMatrix_eq
    (r : ℕ) :
    qubitFourthTensorSectorGramMatrix r =
      qubitFourthGramMatrix ((2 : ℝ) ^ r) := by
  ext i j
  exact qubitFourthTensorSectorGram_eq_gramMatrix r i j

/-- Entrywise nonnegativity of the concrete tensor-coordinate Gram matrix,
in the form required by the trace-cycle endpoint. -/
theorem qubitFourthTensorSectorGramMatrix_nonneg
    (r : ℕ) :
    ∀ i j, 0 ≤ qubitFourthTensorSectorGramMatrix r i j := by
  intro i j
  rw [qubitFourthTensorSectorGramMatrix,
    qubitFourthTensorSectorGram_eq_gramMatrix]
  exact qubitFourthGramMatrix_nonneg (pow_nonneg (by norm_num) r) i j

/-- Consequently every row of the concrete tensor-coordinate
Hilbert--Schmidt Gram matrix has the exact row sum used in the periodic cycle
bound. -/
theorem qubitFourthTensorSectorGram_rowSum
    (r : ℕ) (i : Fin 30) :
    ∑ j, qubitFourthTensorSectorGram r i j =
      cliffordFourthGramRowSum ((2 : ℝ) ^ r) := by
  simp_rw [qubitFourthTensorSectorGram_eq_gramMatrix]
  exact qubitFourthGramMatrix_rowSum i ((2 : ℝ) ^ r)

/-- Quantified constant-row-sum form for the concrete tensor-coordinate
Gram matrix. -/
theorem qubitFourthTensorSectorGramMatrix_all_rowSums
    (r : ℕ) :
    ∀ i, ∑ j, qubitFourthTensorSectorGramMatrix r i j =
      cliffordFourthGramRowSum ((2 : ℝ) ^ r) := by
  intro i
  simpa [qubitFourthTensorSectorGramMatrix] using
    qubitFourthTensorSectorGram_rowSum r i

end

end TomographyOracleCore
