import TomographyOracleCore.BinaryCliffordExactThirdDesign
import TomographyOracleCore.FiniteUnitaryProjectiveRelativeThirdMoment
import TomographyOracleCore.RelativeDesignFiniteChoi

namespace TomographyOracleCore

universe u v

open scoped CStarAlgebra BigOperators Kronecker

noncomputable section

local instance finiteTwirlCPSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance finiteTwirlCPStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Completely positive finite-unitary third twirls

These maps package literal finite averages of tensor-cube unitary
conjugations as completely positive maps.  The Pauli-coset specialization
is therefore a concrete CP representative of the Haar third twirl, by the
audited exact Clifford third-design identity.
-/

/-- Transport a matrix linear map across the definitional matrix/C-star
matrix equivalence. -/
def cstarLinearMapOfMatrixLinearMap
    {I : Type u} [Fintype I]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ) :
    CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ where
  toFun X := CStarMatrix.ofMatrix <| Phi (CStarMatrix.ofMatrix.symm X)
  map_add' X Y := by
    change Phi (X + Y) = Phi X + Phi Y
    exact map_add Phi X Y
  map_smul' c X := by
    change Phi (c • X) = c • Phi X
    exact map_smul Phi c X

@[simp] theorem cstarLinearMapOfMatrixLinearMap_apply
    {I : Type u} [Fintype I]
    (Phi : Matrix I I ℂ →ₗ[ℂ] Matrix I I ℂ)
    (X : CStarMatrix I I ℂ) :
    cstarLinearMapOfMatrixLinearMap Phi X =
      CStarMatrix.ofMatrix (Phi (CStarMatrix.ofMatrix.symm X)) := rfl

/-- Tensor cube of a finite-dimensional unitary, viewed as a C-star
matrix. -/
def finiteUnitaryTensorCube
    {I : Type u} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) :
    CStarMatrix (TripleIndex I) (TripleIndex I) ℂ :=
  CStarMatrix.ofMatrix (matrixTensorThree U.1 U.1 U.1)

/-- One tensor-cube conjugation as a completely positive map. -/
def finiteUnitaryThirdConjugationCP
    {I : Type u} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ) :
    CStarMatrix (TripleIndex I) (TripleIndex I) ℂ →CP
      CStarMatrix (TripleIndex I) (TripleIndex I) ℂ :=
  finiteKrausConjugation (star (finiteUnitaryTensorCube U))

@[simp] theorem finiteUnitaryThirdConjugationCP_apply
    {I : Type u} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ)
    (X : CStarMatrix (TripleIndex I) (TripleIndex I) ℂ) :
    (finiteUnitaryThirdConjugationCP U).toLinearMap X =
      finiteUnitaryTensorCube U * X * star (finiteUnitaryTensorCube U) := by
  change star (star (finiteUnitaryTensorCube U)) * X *
      star (finiteUnitaryTensorCube U) = _
  rw [star_star]

/-- Normalized finite average of literal tensor-cube conjugation CP maps. -/
def finiteUnitaryThirdTwirlCP
    {I : Type u} {E : Type v}
    [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    CStarMatrix (TripleIndex I) (TripleIndex I) ℂ →CP
      CStarMatrix (TripleIndex I) (TripleIndex I) ℂ :=
  CompletelyPositiveMap.nonnegRealSMul
    ((Fintype.card E : ℝ)⁻¹) (by positivity)
    (CompletelyPositiveMap.fintypeSum fun e : E ↦
      finiteUnitaryThirdConjugationCP (U e))

@[simp] theorem finiteUnitaryThirdTwirlCP_apply
    {I : Type u} {E : Type v}
    [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ)
    (X : CStarMatrix (TripleIndex I) (TripleIndex I) ℂ) :
    (finiteUnitaryThirdTwirlCP U).toLinearMap X =
      (((Fintype.card E : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ e : E,
            finiteUnitaryTensorCube (U e) * X *
            star (finiteUnitaryTensorCube (U e)) := by
  rw [finiteUnitaryThirdTwirlCP,
    CompletelyPositiveMap.nonnegRealSMul_toLinearMap,
    LinearMap.smul_apply,
    CompletelyPositiveMap.fintypeSum_toLinearMap,
    LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  exact finiteUnitaryThirdConjugationCP_apply (U e) X

/-- Matrix-space form of the same generic finite third twirl. -/
def finiteUnitaryThirdTwirlMatrixLinearMap
    {I : Type u} {E : Type v}
    [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    Matrix (TripleIndex I) (TripleIndex I) ℂ →ₗ[ℂ]
      Matrix (TripleIndex I) (TripleIndex I) ℂ where
  toFun X := ((Fintype.card E : ℂ)⁻¹) •
    ∑ e : E,
      (matrixTensorThree (U e).1 (U e).1 (U e).1 * X) *
        (matrixTensorThree (U e).1 (U e).1 (U e).1).conjTranspose
  map_add' X Y := by
    simp_rw [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
    module
  map_smul' c X := by
    simp_rw [Matrix.mul_smul, Matrix.smul_mul, ← Finset.smul_sum]
    simp [smul_smul, mul_comm]

@[simp] theorem finiteUnitaryThirdTwirlMatrixLinearMap_apply
    {I : Type u} {E : Type v}
    [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ)
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    finiteUnitaryThirdTwirlMatrixLinearMap U X =
      ((Fintype.card E : ℂ)⁻¹) •
        ∑ e : E,
          (matrixTensorThree (U e).1 (U e).1 (U e).1 * X) *
            (matrixTensorThree (U e).1 (U e).1 (U e).1).conjTranspose := by
  rfl

theorem finiteUnitaryThirdTwirlCP_toLinearMap
    {I : Type u} {E : Type v}
    [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    (finiteUnitaryThirdTwirlCP U).toLinearMap =
      cstarLinearMapOfMatrixLinearMap
        (finiteUnitaryThirdTwirlMatrixLinearMap U) := by
  apply LinearMap.ext
  intro X
  rw [finiteUnitaryThirdTwirlCP_apply]
  rw [cstarLinearMapOfMatrixLinearMap_apply,
    finiteUnitaryThirdTwirlMatrixLinearMap_apply]
  apply CStarMatrix.ext
  intro x y
  simp only [finiteUnitaryTensorCube, CStarMatrix.ofMatrix_apply,
    CStarMatrix.ofMatrix_symm_apply,
    CStarMatrix.smul_apply, CStarMatrix.mul_apply, CStarMatrix.star_apply,
    cstarMatrix_fintypeSum_apply, Matrix.smul_apply, Matrix.sum_apply,
    Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1
  simpa using Complex.ofReal_inv (Fintype.card E : ℝ)

/-- Tensor a unitary with an identity register. -/
def finiteUnitaryTensorId
    {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix.unitaryGroup I ℂ) :
    Matrix.unitaryGroup (I × J) ℂ :=
  ⟨U.1 ⊗ₖ (1 : Matrix J J ℂ),
    Matrix.kronecker_mem_unitary U.2 (by simpa using (1 : unitary (Matrix J J ℂ)).property)⟩

@[simp] theorem finiteUnitaryTensorId_coe
    {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix.unitaryGroup I ℂ) :
    (finiteUnitaryTensorId (J := J) U).1 =
      U.1 ⊗ₖ (1 : Matrix J J ℂ) := rfl

/-- Local finite third twirl on `I`, extended by identity on `J`. -/
def finiteUnitaryThirdTwirlTensorIdCP
    {I : Type u} {J : Type v} {E : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    CStarMatrix (TripleIndex (I × J)) (TripleIndex (I × J)) ℂ →CP
      CStarMatrix (TripleIndex (I × J)) (TripleIndex (I × J)) ℂ :=
  finiteUnitaryThirdTwirlCP (fun e ↦ finiteUnitaryTensorId (J := J) (U e))

theorem finiteUnitaryThirdTwirlTensorIdCP_toLinearMap
    {I : Type u} {J : Type v} {E : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    (finiteUnitaryThirdTwirlTensorIdCP (J := J) U).toLinearMap =
      cstarLinearMapOfMatrixLinearMap
        (finiteUnitaryThirdTwirlMatrixLinearMap
          (fun e ↦ finiteUnitaryTensorId (J := J) (U e))) := by
  exact finiteUnitaryThirdTwirlCP_toLinearMap _

/-- Concrete CP representative of the exact local Pauli-coset Clifford
third twirl. -/
def finitePauliCosetThirdTwirlCP (K : ℕ) :
    CStarMatrix (TripleIndex (PauliBinaryWord K))
        (TripleIndex (PauliBinaryWord K)) ℂ →CP
      CStarMatrix (TripleIndex (PauliBinaryWord K))
        (TripleIndex (PauliBinaryWord K)) ℂ :=
  finiteUnitaryThirdTwirlCP (pauliCosetCliffordUnitary K)

theorem finitePauliCosetThirdTwirlMatrixLinearMap_eq
    (K : ℕ) :
    finiteUnitaryThirdTwirlMatrixLinearMap
        (pauliCosetCliffordUnitary K) =
      finitePauliCosetThirdTwirlLinearMap K := by
  rfl

theorem finitePauliCosetThirdTwirlCP_toLinearMap
    (K : ℕ) :
    (finitePauliCosetThirdTwirlCP K).toLinearMap =
      cstarLinearMapOfMatrixLinearMap
        (finitePauliCosetThirdTwirlLinearMap K) := by
  rw [finitePauliCosetThirdTwirlCP,
    finiteUnitaryThirdTwirlCP_toLinearMap,
    finitePauliCosetThirdTwirlMatrixLinearMap_eq]

/-- A concrete completely positive representative of the Haar third twirl
on `K` qubits.  It is implemented by the finite Pauli-coset Clifford
ensemble, whose exact third-design identity is already proved. -/
def pauliHaarThirdTwirlCP (K : ℕ) := finitePauliCosetThirdTwirlCP K

/-- The concrete CP representative has exactly the literal Haar integral as
its transported linear map. -/
theorem pauliHaarThirdTwirlCP_toLinearMap
    (K : ℕ) :
    (pauliHaarThirdTwirlCP K).toLinearMap =
      cstarLinearMapOfMatrixLinearMap
        (pauliHaarThirdTwirlLinearMap K) := by
  rw [pauliHaarThirdTwirlCP,
    finitePauliCosetThirdTwirlCP_toLinearMap,
    finitePauliCosetThirdTwirlLinearMap_eq_pauliHaarThirdTwirlLinearMap]

/-- Local Haar third twirl on `K` qubits, extended by identity on an
arbitrary finite register.  The implementation is again the exact finite
Clifford third design. -/
def pauliHaarThirdTwirlTensorIdCP
    (K : ℕ) (J : Type v) [Fintype J] [DecidableEq J] :
    CStarMatrix (TripleIndex (PauliBinaryWord K × J))
        (TripleIndex (PauliBinaryWord K × J)) ℂ →CP
      CStarMatrix (TripleIndex (PauliBinaryWord K × J))
        (TripleIndex (PauliBinaryWord K × J)) ℂ :=
  finiteUnitaryThirdTwirlTensorIdCP
    (J := J) (pauliCosetCliffordUnitary K)

theorem pauliHaarThirdTwirlTensorIdCP_toLinearMap
    (K : ℕ) (J : Type v) [Fintype J] [DecidableEq J] :
    (pauliHaarThirdTwirlTensorIdCP K J).toLinearMap =
      cstarLinearMapOfMatrixLinearMap
        (finiteUnitaryThirdTwirlMatrixLinearMap
          (fun e : PauliCosetCliffordEnsemble K ↦
            finiteUnitaryTensorId (J := J)
              (pauliCosetCliffordUnitary K e))) := by
  exact finiteUnitaryThirdTwirlTensorIdCP_toLinearMap _

end

end TomographyOracleCore
