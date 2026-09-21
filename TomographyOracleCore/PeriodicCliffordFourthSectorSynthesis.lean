import Mathlib.Tactic.Ring
import TomographyOracleCore.PeriodicCliffordFourthSectorOperatorComplex

namespace TomographyOracleCore

noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-!
# Finite-family synthesis for the thirty fourth-copy sectors

This module packages the literal complex sector matrices into a linear
finite-family synthesis operator.  All results below are elementary linear
algebra consequences of the already explicit Hilbert--Schmidt Gram matrix.

In particular, this file does **not** identify a physical Clifford average
with the synthesis operator, and it does not assume that the displayed
Weingarten matrix is the inverse of the Gram matrix.  The two missing
representation-theoretic statements are recorded at the end as definitions
of propositions, not as axioms or theorem hypotheses.
-/

/-- For fixed left argument, the complex Hilbert--Schmidt pairing is a
complex-linear functional of its right argument. -/
def qubitFourthComplexHilbertSchmidtRightLinear
    {ι : Type*} [Fintype ι] (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] ℂ where
  toFun := qubitFourthComplexHilbertSchmidt A
  map_add' X Y := by
    unfold qubitFourthComplexHilbertSchmidt
    rw [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    unfold qubitFourthComplexHilbertSchmidt
    rw [Matrix.mul_smul, Matrix.trace_smul]
    simp

@[simp] theorem qubitFourthComplexHilbertSchmidtRightLinear_apply
    {ι : Type*} [Fintype ι]
    (A X : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidtRightLinear A X =
      qubitFourthComplexHilbertSchmidt A X := rfl

@[simp] theorem qubitFourthComplexHilbertSchmidt_add_right
    {ι : Type*} [Fintype ι]
    (A X Y : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A (X + Y) =
      qubitFourthComplexHilbertSchmidt A X +
        qubitFourthComplexHilbertSchmidt A Y :=
  map_add (qubitFourthComplexHilbertSchmidtRightLinear A) X Y

@[simp] theorem qubitFourthComplexHilbertSchmidt_smul_right
    {ι : Type*} [Fintype ι]
    (A X : Matrix ι ι ℂ) (c : ℂ) :
    qubitFourthComplexHilbertSchmidt A (c • X) =
      c * qubitFourthComplexHilbertSchmidt A X :=
  map_smul (qubitFourthComplexHilbertSchmidtRightLinear A) c X

@[simp] theorem qubitFourthComplexHilbertSchmidt_sub_right
    {ι : Type*} [Fintype ι]
    (A X Y : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A (X - Y) =
      qubitFourthComplexHilbertSchmidt A X -
        qubitFourthComplexHilbertSchmidt A Y :=
  map_sub (qubitFourthComplexHilbertSchmidtRightLinear A) X Y

/-- Finite sums can be pulled through the right argument of the
Hilbert--Schmidt pairing. -/
theorem qubitFourthComplexHilbertSchmidt_sum_right
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι ι ℂ) (f : κ → Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A (∑ k, f k) =
      ∑ k, qubitFourthComplexHilbertSchmidt A (f k) := by
  change (qubitFourthComplexHilbertSchmidtRightLinear A) (∑ k, f k) = _
  rw [map_sum]
  rfl

/-- Analysis coefficient of an operator against the `j`th explicit sector
matrix. -/
def qubitFourthSectorAnalysis
    (r : ℕ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (j : Fin 30) : ℂ :=
  qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r j) X

/-- Finite-family synthesis with an arbitrary coefficient matrix `W`.

For input `X`, its literal value is
`∑ i,j (W i j * ⟪R_j,X⟫) • R_i`. -/
def qubitFourthSectorSynthesisLinearMap
    (r : ℕ) (W : Matrix (Fin 30) (Fin 30) ℂ) :
    Matrix (QubitFourthBlockReplicaIndex r)
        (QubitFourthBlockReplicaIndex r) ℂ →ₗ[ℂ]
      Matrix (QubitFourthBlockReplicaIndex r)
        (QubitFourthBlockReplicaIndex r) ℂ :=
  ∑ i : Fin 30, ∑ j : Fin 30, (W i j) •
    (qubitFourthComplexHilbertSchmidtRightLinear
      (qubitFourthSectorR r j)).smulRight (qubitFourthSectorR r i)

/-- Pointwise formula for the finite-family synthesis map. -/
@[simp] theorem qubitFourthSectorSynthesisLinearMap_apply
    (r : ℕ) (W : Matrix (Fin 30) (Fin 30) ℂ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ) :
    qubitFourthSectorSynthesisLinearMap r W X =
      ∑ i : Fin 30, ∑ j : Fin 30,
        (W i j * qubitFourthSectorAnalysis r X j) •
          qubitFourthSectorR r i := by
  simp [qubitFourthSectorSynthesisLinearMap,
    LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, qubitFourthSectorAnalysis, smul_smul]

/-- On a sector vector, synthesis acts by the literal matrix product `W G`.
No inverse relation between these matrices is used. -/
theorem qubitFourthSectorSynthesisLinearMap_on_sector
    (r : ℕ) (W : Matrix (Fin 30) (Fin 30) ℂ) (k : Fin 30) :
    qubitFourthSectorSynthesisLinearMap r W
        (qubitFourthSectorR r k) =
      ∑ i : Fin 30,
        ((W * qubitFourthSectorRGramMatrix r) i k) •
          qubitFourthSectorR r i := by
  rw [qubitFourthSectorSynthesisLinearMap_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold qubitFourthSectorAnalysis qubitFourthSectorRGramMatrix
  change
    (∑ j : Fin 30,
      (W i j * qubitFourthComplexHilbertSchmidt
        (qubitFourthSectorR r j) (qubitFourthSectorR r k)) •
        qubitFourthSectorR r i) =
      (∑ j : Fin 30,
        W i j * qubitFourthComplexHilbertSchmidt
          (qubitFourthSectorR r j) (qubitFourthSectorR r k)) •
        qubitFourthSectorR r i
  rw [Finset.sum_smul]

/-- Pairing a synthesized operator with `R_l` gives the corresponding
double Gram contraction. -/
theorem qubitFourthSector_hilbertSchmidt_synthesis
    (r : ℕ) (W : Matrix (Fin 30) (Fin 30) ℂ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (l : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (qubitFourthSectorSynthesisLinearMap r W X) =
      ∑ i : Fin 30, ∑ j : Fin 30,
        (W i j * qubitFourthSectorAnalysis r X j) *
          qubitFourthSectorRGramMatrix r l i := by
  rw [qubitFourthSectorSynthesisLinearMap_apply,
    qubitFourthComplexHilbertSchmidt_sum_right]
  simp_rw [qubitFourthComplexHilbertSchmidt_sum_right,
    qubitFourthComplexHilbertSchmidt_smul_right]
  rfl

/-- Matrix form of the preceding contraction: the residual obstruction to
sector orthogonality is exactly `G W`. -/
theorem qubitFourthSector_hilbertSchmidt_synthesis_matrix
    (r : ℕ) (W : Matrix (Fin 30) (Fin 30) ℂ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (l : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (qubitFourthSectorSynthesisLinearMap r W X) =
      ∑ j : Fin 30,
        ((qubitFourthSectorRGramMatrix r * W) l j) *
          qubitFourthSectorAnalysis r X j := by
  rw [qubitFourthSector_hilbertSchmidt_synthesis]
  calc
    (∑ i : Fin 30, ∑ j : Fin 30,
        (W i j * qubitFourthSectorAnalysis r X j) *
          qubitFourthSectorRGramMatrix r l i) =
        ∑ j : Fin 30, ∑ i : Fin 30,
          (W i j * qubitFourthSectorAnalysis r X j) *
            qubitFourthSectorRGramMatrix r l i := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin 30,
        ((qubitFourthSectorRGramMatrix r * W) l j) *
          qubitFourthSectorAnalysis r X j := by
      apply Finset.sum_congr rfl
      intro j _hj
      rw [Matrix.mul_apply, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _hi
      ring

/-- Exact residual formula.  Thus an actual proof that `G W = 1` would make
the synthesis residual orthogonal to all thirty sector matrices. -/
theorem qubitFourthSectorSynthesis_residual_pairing
    (r : ℕ) (W : Matrix (Fin 30) (Fin 30) ℂ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (l : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (X - qubitFourthSectorSynthesisLinearMap r W X) =
      qubitFourthSectorAnalysis r X l -
        ∑ j : Fin 30,
          ((qubitFourthSectorRGramMatrix r * W) l j) *
            qubitFourthSectorAnalysis r X j := by
  rw [qubitFourthComplexHilbertSchmidt_sub_right,
    qubitFourthSector_hilbertSchmidt_synthesis_matrix]
  rfl

/-! ## The explicit Weingarten candidate and the remaining semantic gap -/

/-- The certified intersection entry, viewed as an element of `Fin 5`.
Only classes `1,2,3,4` occur. -/
def qubitFourthIntersectionClass (i j : Fin 30) : Fin 5 :=
  ⟨qubitFourthIntersectionEntry i j,
    Nat.lt_succ_of_le (qubitFourthIntersectionEntry_bounds i j).2⟩

@[simp] theorem qubitFourthIntersectionClass_val
    (i j : Fin 30) :
    (qubitFourthIntersectionClass i j).val =
      qubitFourthIntersectionEntry i j := rfl

/-- The finite intersection class is symmetric in the two sectors. -/
theorem qubitFourthIntersectionClass_comm (i j : Fin 30) :
    qubitFourthIntersectionClass i j =
      qubitFourthIntersectionClass j i := by
  apply Fin.ext
  exact qubitFourthIntersectionEntry_comm i j

/-- The literal complex matrix formed from the four scalar Weingarten
coefficients and the certified intersection table. -/
def qubitFourthComplexWgMatrix
    (x : ℝ) : Matrix (Fin 30) (Fin 30) ℂ :=
  fun i j ↦
    (qubitFourthWgCoefficient (qubitFourthIntersectionClass i j) x : ℂ)

@[simp] theorem qubitFourthComplexWgMatrix_apply
    (x : ℝ) (i j : Fin 30) :
    qubitFourthComplexWgMatrix x i j =
      (qubitFourthWgCoefficient
        (qubitFourthIntersectionClass i j) x : ℂ) := rfl

/-- The explicit Weingarten candidate matrix is symmetric. -/
theorem qubitFourthComplexWgMatrix_comm
    (x : ℝ) (i j : Fin 30) :
    qubitFourthComplexWgMatrix x i j =
      qubitFourthComplexWgMatrix x j i := by
  rw [qubitFourthComplexWgMatrix_apply,
    qubitFourthComplexWgMatrix_apply,
    qubitFourthIntersectionClass_comm i j]

/-- The explicit thirty-sector synthesis candidate at local dimension
`2^r`.  The name `candidate` is intentional: projector status is not asserted
until the inverse and physical-average identifications are proved. -/
def qubitFourthSectorSynthesisCandidate
    (r : ℕ) :
    Matrix (QubitFourthBlockReplicaIndex r)
        (QubitFourthBlockReplicaIndex r) ℂ →ₗ[ℂ]
      Matrix (QubitFourthBlockReplicaIndex r)
        (QubitFourthBlockReplicaIndex r) ℂ :=
  qubitFourthSectorSynthesisLinearMap r
    (qubitFourthComplexWgMatrix ((2 : ℝ) ^ r))

/-- Exact matrix-inverse statement still to be derived from the already
certified association tables.  This is a proposition definition, not an
available theorem. -/
def QubitFourthComplexWgInverseStatement (r : ℕ) : Prop :=
  qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) *
        qubitFourthSectorRGramMatrix r = 1 ∧
    qubitFourthSectorRGramMatrix r *
        qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) = 1

/-- Type of complex operator superoperators on an `r`-qubit fourth-copy
block. -/
abbrev QubitFourthComplexSuperoperator (r : ℕ) :=
  Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ →ₗ[ℂ]
    Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ

/-- The remaining physical representation-theoretic identification, stated
as a proposition about a separately constructed physical Clifford-average
map.  No such equality is assumed or proved in this module. -/
def PhysicalCliffordFourthAverageEqualsSectorSynthesis
    (r : ℕ) (physicalAverage : QubitFourthComplexSuperoperator r) : Prop :=
  physicalAverage = qubitFourthSectorSynthesisCandidate r

end

end TomographyOracleCore
