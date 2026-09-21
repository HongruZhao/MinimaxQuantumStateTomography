import Mathlib.LinearAlgebra.UnitaryGroup
import TomographyOracleCore.BinaryCliffordPauliCosetEnsemble
import TomographyOracleCore.FiniteGroupHilbertSchmidtTwirl

namespace TomographyOracleCore

open scoped Kronecker

noncomputable section

/-!
# Literal fourth-copy unitary representations

This file constructs the physical four-fold tensor power of a unitary and
the resulting conjugation representation.  It also specializes the
construction pointwise to the existing finite Pauli-coset Clifford ensemble.

The existing `PauliCosetCliffordEnsemble` is an indexing type, not a group,
and `binaryTransvectionUnitaryLift` is a chosen lift rather than a monoid
homomorphism.  Consequently its pointwise action is defined here without
pretending that the ensemble itself supplies a `Representation`.  The final
group-valued construction takes the missing mathematical datum explicitly:
a monoid homomorphism into the unitary group.
-/

/-- Index set for a four-fold tensor product. -/
abbrev FourthIndex (ι : Type*) := ι × ι × ι × ι

/-- Literal four-fold Kronecker product, with right-associated replica
indices. -/
def matrixTensorFour {ι : Type*}
    (A B C D : Matrix ι ι ℂ) :
    Matrix (FourthIndex ι) (FourthIndex ι) ℂ :=
  A ⊗ₖ (B ⊗ₖ (C ⊗ₖ D))

@[simp]
theorem matrixTensorFour_apply {ι : Type*}
    (A B C D : Matrix ι ι ℂ) (x y : FourthIndex ι) :
    matrixTensorFour A B C D x y =
      A x.1 y.1 * B x.2.1 y.2.1 *
        C x.2.2.1 y.2.2.1 * D x.2.2.2 y.2.2.2 := by
  simp [matrixTensorFour, Matrix.kronecker_apply, mul_assoc]

/-- Four-fold tensor products preserve matrix multiplication. -/
theorem matrixTensorFour_mul {ι : Type*} [Fintype ι]
    (A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ : Matrix ι ι ℂ) :
    matrixTensorFour (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) (A₄ * B₄) =
      matrixTensorFour A₁ A₂ A₃ A₄ *
        matrixTensorFour B₁ B₂ B₃ B₄ := by
  simp only [matrixTensorFour, Matrix.mul_kronecker_mul]

/-- Four-fold tensor products commute with conjugate transpose. -/
theorem matrixTensorFour_conjTranspose {ι : Type*}
    (A B C D : Matrix ι ι ℂ) :
    matrixTensorFour A.conjTranspose B.conjTranspose
        C.conjTranspose D.conjTranspose =
      (matrixTensorFour A B C D).conjTranspose := by
  simp [matrixTensorFour, Matrix.conjTranspose_kronecker]

/-- The tensor fourth power of the identity is the identity. -/
@[simp]
theorem matrixTensorFour_one {ι : Type*} [DecidableEq ι] :
    matrixTensorFour (1 : Matrix ι ι ℂ) 1 1 1 = 1 := by
  simp [matrixTensorFour, Matrix.one_kronecker_one]

/-- Four identical copies of a unitary form a unitary on the four-replica
space. -/
noncomputable def unitaryTensorFourth
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup (FourthIndex ι) ℂ :=
  ⟨matrixTensorFour U.1 U.1 U.1 U.1,
    Matrix.kronecker_mem_unitary U.2
      (Matrix.kronecker_mem_unitary U.2
        (Matrix.kronecker_mem_unitary U.2 U.2))⟩

@[simp]
theorem unitaryTensorFourth_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    unitaryTensorFourth (1 : Matrix.unitaryGroup ι ℂ) = 1 := by
  apply Subtype.ext
  exact matrixTensorFour_one

@[simp]
theorem unitaryTensorFourth_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) :
    unitaryTensorFourth (U * V) =
      unitaryTensorFourth U * unitaryTensorFourth V := by
  apply Subtype.ext
  exact matrixTensorFour_mul U.1 U.1 U.1 U.1 V.1 V.1 V.1 V.1

/-- Tensor fourth power as a monoid homomorphism on unitary groups. -/
noncomputable def unitaryTensorFourthMonoidHom
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    Matrix.unitaryGroup ι ℂ →*
      Matrix.unitaryGroup (FourthIndex ι) ℂ where
  toFun := unitaryTensorFourth
  map_one' := unitaryTensorFourth_one
  map_mul' := unitaryTensorFourth_mul

@[simp]
theorem unitaryTensorFourth_inv
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    unitaryTensorFourth U⁻¹ = (unitaryTensorFourth U)⁻¹ :=
  unitaryTensorFourthMonoidHom.map_inv U

/-- Conjugation by one unitary, as a complex-linear map on matrices. -/
def unitaryMatrixConjugationLinearMap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ where
  toFun X := (U.1 * X) * U.1.conjTranspose
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    simp only [RingHom.id_apply]

@[simp]
theorem unitaryMatrixConjugationLinearMap_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    unitaryMatrixConjugationLinearMap U X =
      (U.1 * X) * U.1.conjTranspose :=
  rfl

@[simp]
theorem unitaryMatrixConjugationLinearMap_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    unitaryMatrixConjugationLinearMap
        (1 : Matrix.unitaryGroup ι ℂ) = 1 := by
  apply LinearMap.ext
  intro X
  simp [unitaryMatrixConjugationLinearMap]

@[simp]
theorem unitaryMatrixConjugationLinearMap_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) :
    unitaryMatrixConjugationLinearMap (U * V) =
      unitaryMatrixConjugationLinearMap U *
        unitaryMatrixConjugationLinearMap V := by
  apply LinearMap.ext
  intro X
  change (((U.1 * V.1) * X) *
      (U.1 * V.1).conjTranspose) =
    (U.1 * ((V.1 * X) * V.1.conjTranspose)) *
      U.1.conjTranspose
  rw [Matrix.conjTranspose_mul]
  simp only [mul_assoc]

/-- Conjugation representation supplied by a genuine unitary-group
homomorphism. -/
noncomputable def unitaryConjugationRepresentation
    {G ι : Type*} [Monoid G] [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix.unitaryGroup ι ℂ) :
    Representation ℂ G (Matrix ι ι ℂ) where
  toFun g := unitaryMatrixConjugationLinearMap (U g)
  map_one' := by rw [U.map_one, unitaryMatrixConjugationLinearMap_one]
  map_mul' g h := by
    rw [U.map_mul, unitaryMatrixConjugationLinearMap_mul]

/-- The literal fourth-copy conjugation representation associated with a
unitary representation of a group on the one-copy Hilbert space. -/
noncomputable def unitaryFourthCopyRepresentation
    {G ι : Type*} [Monoid G] [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix.unitaryGroup ι ℂ) :
    Representation ℂ G
      (Matrix (FourthIndex ι) (FourthIndex ι) ℂ) :=
  unitaryConjugationRepresentation
    (unitaryTensorFourthMonoidHom.comp U)

@[simp]
theorem unitaryFourthCopyRepresentation_apply
    {G ι : Type*} [Monoid G] [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix.unitaryGroup ι ℂ) (g : G)
    (X : Matrix (FourthIndex ι) (FourthIndex ι) ℂ) :
    unitaryFourthCopyRepresentation U g X =
      ((unitaryTensorFourth (U g)).1 * X) *
        (unitaryTensorFourth (U g)).1.conjTranspose :=
  rfl

/-- Exact inverse-adjoint identity for conjugation by one unitary. -/
theorem unitaryMatrixConjugationLinearMap_inverse_adjoint
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A
        (unitaryMatrixConjugationLinearMap U B) =
      qubitFourthComplexHilbertSchmidt
        (unitaryMatrixConjugationLinearMap U⁻¹ A) B := by
  rw [unitaryMatrixConjugationLinearMap_apply,
    qubitFourthComplexHilbertSchmidt_conjugation_adjoint,
    unitaryMatrixConjugationLinearMap_apply]
  simp [Matrix.star_eq_conjTranspose]

/-- Exact inverse-adjoint identity for the literal fourth-copy group
representation. -/
theorem unitaryFourthCopyRepresentation_inverse_adjoint
    {G ι : Type*} [Group G] [Fintype ι] [DecidableEq ι]
    (U : G →* Matrix.unitaryGroup ι ℂ) (g : G)
    (A B : Matrix (FourthIndex ι) (FourthIndex ι) ℂ) :
    qubitFourthComplexHilbertSchmidt A
        (unitaryFourthCopyRepresentation U g B) =
      qubitFourthComplexHilbertSchmidt
        (unitaryFourthCopyRepresentation U (g⁻¹) A) B := by
  change qubitFourthComplexHilbertSchmidt A
      (unitaryMatrixConjugationLinearMap
        (unitaryTensorFourth (U g)) B) =
    qubitFourthComplexHilbertSchmidt
      (unitaryMatrixConjugationLinearMap
        (unitaryTensorFourth (U (g⁻¹))) A) B
  rw [unitaryMatrixConjugationLinearMap_inverse_adjoint,
    map_inv, unitaryTensorFourth_inv]

/-! ## Finite binary-Clifford group interface -/

/-- The missing realization datum for a finite binary Clifford group (or a
finite central extension of the symplectic group): an exact homomorphism to
physical unitaries on the binary-word Hilbert space.  This type is an
interface, not an assertion that the currently chosen symplectic lifts form
such a homomorphism. -/
abbrev BinaryCliffordUnitaryRealization
    (K : ℕ) (G : Type*) [Monoid G] :=
  G →* Matrix.unitaryGroup (PauliBinaryWord K) ℂ

/-- Physical fourth-copy representation supplied by an exact finite binary
Clifford unitary realization. -/
noncomputable def binaryCliffordFiniteFourthRepresentation
    (K : ℕ) {G : Type*} [Group G] [Fintype G]
    (U : BinaryCliffordUnitaryRealization K G) :
    Representation ℂ G
      (Matrix (FourthIndex (PauliBinaryWord K))
        (FourthIndex (PauliBinaryWord K)) ℂ) :=
  unitaryFourthCopyRepresentation U

/-- The finite binary-Clifford fourth-copy representation has the exact
inverse-adjoint identity required by the finite-group twirl. -/
theorem binaryCliffordFiniteFourthRepresentation_inverse_adjoint
    (K : ℕ) {G : Type*} [Group G] [Fintype G]
    (U : BinaryCliffordUnitaryRealization K G) (g : G)
    (A B : Matrix (FourthIndex (PauliBinaryWord K))
      (FourthIndex (PauliBinaryWord K)) ℂ) :
    qubitFourthComplexHilbertSchmidt A
        (binaryCliffordFiniteFourthRepresentation K U g B) =
      qubitFourthComplexHilbertSchmidt
        (binaryCliffordFiniteFourthRepresentation K U (g⁻¹) A) B :=
  unitaryFourthCopyRepresentation_inverse_adjoint U g A B

/-! ## Pointwise specialization to the existing finite Clifford ensemble -/

/-- The literal four-copy unitary attached to one member of the finite
Pauli-coset Clifford ensemble. -/
noncomputable def pauliCosetCliffordTensorFourth
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup
      (FourthIndex (PauliBinaryWord K)) ℂ :=
  unitaryTensorFourth (pauliCosetCliffordUnitary K e)

/-- Pointwise physical four-copy action of one Pauli-coset Clifford
ensemble member. -/
noncomputable def pauliCosetCliffordFourthAction
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix (FourthIndex (PauliBinaryWord K))
        (FourthIndex (PauliBinaryWord K)) ℂ →ₗ[ℂ]
      Matrix (FourthIndex (PauliBinaryWord K))
        (FourthIndex (PauliBinaryWord K)) ℂ :=
  unitaryMatrixConjugationLinearMap
    (pauliCosetCliffordTensorFourth K e)

@[simp]
theorem pauliCosetCliffordFourthAction_apply
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (X : Matrix (FourthIndex (PauliBinaryWord K))
      (FourthIndex (PauliBinaryWord K)) ℂ) :
    pauliCosetCliffordFourthAction K e X =
      ((pauliCosetCliffordTensorFourth K e).1 * X) *
        (pauliCosetCliffordTensorFourth K e).1.conjTranspose :=
  rfl

/-- Exact pointwise inverse-adjoint identity for every unitary in the
existing finite Pauli-coset Clifford ensemble. -/
theorem pauliCosetCliffordFourthAction_inverse_adjoint
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A B : Matrix (FourthIndex (PauliBinaryWord K))
      (FourthIndex (PauliBinaryWord K)) ℂ) :
    qubitFourthComplexHilbertSchmidt A
        (pauliCosetCliffordFourthAction K e B) =
      qubitFourthComplexHilbertSchmidt
        (unitaryMatrixConjugationLinearMap
          (pauliCosetCliffordTensorFourth K e)⁻¹ A) B :=
  unitaryMatrixConjugationLinearMap_inverse_adjoint
    (pauliCosetCliffordTensorFourth K e) A B

end

end TomographyOracleCore
