import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.Trace
import TomographyOracleCore.PeriodicCliffordFourthSectorOperatorCoordinates

namespace TomographyOracleCore

noncomputable section

-- The coordinate module deliberately keeps these finite enumerations local;
-- restate them here for the intrinsic matrix traces below.
local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-!
# Complex fourth-sector operators and their Hilbert--Schmidt Gram matrix

This module moves the explicit real `0`--`1` sector matrices into the
complex matrix space used by the physical quantum model.  The
Hilbert--Schmidt form is now defined intrinsically as
`trace(Aᴴ * B)`, and its exact reduction to the previously certified real
Gram matrix is proved.

`qubitFourthSectorR` is the explicit stochastic-Lagrangian `R(T)`-style
coordinate formula: on an `r`-qubit block its matrix entry is the product of
the one-site membership indicators.  The name records the coordinate model,
not a use of the external commutant theorem.  What remains separate is the
representation-theoretic assertion that the fourth Clifford average is the
orthogonal projector onto the span of precisely these matrices.
-/

/-- Entrywise embedding of a real matrix into a complex matrix. -/
def qubitFourthComplexOfRealMatrix
    {m n : Type*} (A : Matrix m n ℝ) : Matrix m n ℂ :=
  fun i j ↦ (A i j : ℂ)

@[simp] theorem qubitFourthComplexOfRealMatrix_apply
    {m n : Type*} (A : Matrix m n ℝ) (i : m) (j : n) :
    qubitFourthComplexOfRealMatrix A i j = (A i j : ℂ) := rfl

/-- The physical complex Hilbert--Schmidt pairing. -/
def qubitFourthComplexHilbertSchmidt
    {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) : ℂ :=
  (A.conjTranspose * B).trace

/-- Expansion of `trace(Aᴴ * B)` as the entrywise conjugate dot product. -/
theorem qubitFourthComplexHilbertSchmidt_eq_entrywise
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A B =
      ∑ row, ∑ column, star (A row column) * B row column := by
  change (∑ column, ∑ row, star (A row column) * B row column) =
    ∑ row, ∑ column, star (A row column) * B row column
  exact Finset.sum_comm

/-- Complex embedding preserves the real entrywise Hilbert--Schmidt
pairing. -/
theorem qubitFourthComplexHilbertSchmidt_ofRealMatrix
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) :
    qubitFourthComplexHilbertSchmidt
        (qubitFourthComplexOfRealMatrix A)
        (qubitFourthComplexOfRealMatrix B) =
      ((∑ row, ∑ column, A row column * B row column : ℝ) : ℂ) := by
  rw [qubitFourthComplexHilbertSchmidt_eq_entrywise]
  calc
    (∑ row : ι, ∑ column : ι,
        star (qubitFourthComplexOfRealMatrix A row column) *
          qubitFourthComplexOfRealMatrix B row column) =
        ∑ row : ι,
          ((∑ column : ι, A row column * B row column : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro row _hrow
      calc
        (∑ column : ι,
            star (qubitFourthComplexOfRealMatrix A row column) *
              qubitFourthComplexOfRealMatrix B row column) =
            ∑ column : ι,
              ((A row column * B row column : ℝ) : ℂ) := by
          apply Finset.sum_congr rfl
          intro column _hcolumn
          simp [qubitFourthComplexOfRealMatrix]
        _ = ((∑ column : ι,
              A row column * B row column : ℝ) : ℂ) :=
          (Complex.ofReal_sum (Finset.univ : Finset ι)
            (fun column ↦ A row column * B row column)).symm
    _ = ((∑ row : ι, ∑ column : ι,
          A row column * B row column : ℝ) : ℂ) :=
      (Complex.ofReal_sum (Finset.univ : Finset ι)
        (fun row ↦ ∑ column : ι,
          A row column * B row column)).symm

/-- Explicit complex `R_r(T)`-style sector matrix.  Its normalization is
fixed by the literal `0`--`1` coordinate formula, with no scalar factor. -/
def qubitFourthSectorR
    (r : ℕ) (i : Fin 30) :
    Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ :=
  qubitFourthComplexOfRealMatrix (qubitFourthBlockSectorMatrix r i)

/-- Exact tensor-product entry formula for the complex sector operator. -/
theorem qubitFourthSectorR_apply_tensor
    (r : ℕ) (i : Fin 30)
    (row column : QubitFourthBlockReplicaIndex r) :
    qubitFourthSectorR r i row column =
      ∏ a, (qubitFourthOneQubitSectorMatrix i
        (row a) (column a) : ℂ) := by
  simp [qubitFourthSectorR, qubitFourthComplexOfRealMatrix,
    qubitFourthBlockSectorMatrix, Complex.ofReal_prod]

/-- Fully expanded membership-indicator normalization of `R_r(T)`. -/
theorem qubitFourthSectorR_apply_indicator
    (r : ℕ) (i : Fin 30)
    (row column : QubitFourthBlockReplicaIndex r) :
    qubitFourthSectorR r i row column =
      ∏ a, if row a ++ column a ∈ qubitFourthSector i
        then (1 : ℂ) else 0 := by
  rw [qubitFourthSectorR_apply_tensor]
  apply Finset.prod_congr rfl
  intro a _ha
  by_cases hmem : row a ++ column a ∈ qubitFourthSector i
  · simp [qubitFourthOneQubitSectorMatrix,
      qubitFourthOneQubitSectorOperator, qubitFourthRowColumnEquiv, hmem]
  · simp [qubitFourthOneQubitSectorMatrix,
      qubitFourthOneQubitSectorOperator, qubitFourthRowColumnEquiv, hmem]

/-- The adjoint has the expected conjugate-transposed real coordinate
array; the entries are real, so conjugation contributes no additional
phase. -/
theorem qubitFourthSectorR_conjTranspose_apply
    (r : ℕ) (i : Fin 30)
    (row column : QubitFourthBlockReplicaIndex r) :
    (qubitFourthSectorR r i).conjTranspose row column =
      (qubitFourthBlockSectorMatrix r i column row : ℂ) := by
  simp [qubitFourthSectorR, qubitFourthComplexOfRealMatrix]

/-- The intrinsic complex Hilbert--Schmidt pairing is the complex embedding
of the already literal real block-matrix pairing. -/
theorem qubitFourthSectorR_hilbertSchmidt_eq_real
    (r : ℕ) (i j : Fin 30) :
    qubitFourthComplexHilbertSchmidt
        (qubitFourthSectorR r i) (qubitFourthSectorR r j) =
      (qubitFourthBlockMatrixHilbertSchmidt r
        (qubitFourthBlockSectorMatrix r i)
        (qubitFourthBlockSectorMatrix r j) : ℂ) := by
  simpa [qubitFourthSectorR,
    qubitFourthBlockMatrixHilbertSchmidt] using
    qubitFourthComplexHilbertSchmidt_ofRealMatrix
      (qubitFourthBlockSectorMatrix r i)
      (qubitFourthBlockSectorMatrix r j)

/-- Exact complex Hilbert--Schmidt Gram identity for all thirty sector
operators and every block dimension `2^r`. -/
theorem qubitFourthSectorR_hilbertSchmidt_eq_gramMatrix
    (r : ℕ) (i j : Fin 30) :
    qubitFourthComplexHilbertSchmidt
        (qubitFourthSectorR r i) (qubitFourthSectorR r j) =
      (qubitFourthGramMatrix ((2 : ℝ) ^ r) i j : ℂ) := by
  rw [qubitFourthSectorR_hilbertSchmidt_eq_real,
    qubitFourthBlockSectorMatrix_hilbertSchmidt_eq_gramMatrix]

/-- The complex Gram matrix formed intrinsically from the thirty literal
sector operators. -/
def qubitFourthSectorRGramMatrix
    (r : ℕ) : Matrix (Fin 30) (Fin 30) ℂ :=
  fun i j ↦ qubitFourthComplexHilbertSchmidt
    (qubitFourthSectorR r i) (qubitFourthSectorR r j)

/-- Matrix-level complex Gram identification. -/
theorem qubitFourthSectorRGramMatrix_eq
    (r : ℕ) :
    qubitFourthSectorRGramMatrix r =
      fun i j ↦ (qubitFourthGramMatrix ((2 : ℝ) ^ r) i j : ℂ) := by
  ext i j
  exact qubitFourthSectorR_hilbertSchmidt_eq_gramMatrix r i j

end

end TomographyOracleCore
