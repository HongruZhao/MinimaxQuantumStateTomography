import TomographyOracleCore.Revision.MatrixTensorPiSpan
import TomographyOracleCore.Revision.PhysicalCliffordFourthTwirl

namespace TomographyOracleCore.Revision.FourthTwirlTensorization

open MatrixTensorPi MatrixTensorPiSpan BinaryCliffordNeutralFourth
open PhysicalCliffordFourthTwirl FourthSectorDecomposition
open scoped BigOperators
noncomputable section

variable {J α E : Type*} [Fintype J] [DecidableEq J]
  [Fintype α] [DecidableEq α] [Fintype E]

def fourthAverage (U : E → Matrix.unitaryGroup α ℂ) :
    Matrix (FourthIndex α) (FourthIndex α) ℂ →ₗ[ℂ]
      Matrix (FourthIndex α) (FourthIndex α) ℂ :=
  (Fintype.card E : ℂ)⁻¹ •
    ∑ e, unitaryMatrixConjugationLinearMap (unitaryTensorFourth (U e))

def tensorPiUnitary (U : J → Matrix.unitaryGroup α ℂ) : Matrix.unitaryGroup (J → α) ℂ :=
  ⟨tensorPi (fun j => (U j).val), tensorPi_unitary U⟩

theorem fourthTensorPi_conjTranspose
    (A : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthTensorPi (fun j => (A j).conjTranspose) = (fourthTensorPi A).conjTranspose := by
  simp only [fourthTensorPi, tensorPi_conjTranspose, Matrix.conjTranspose_submatrix]

theorem fourthConjugation_tensorPi
    (U : J → Matrix.unitaryGroup α ℂ)
    (A : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth (tensorPiUnitary U))
      (fourthTensorPi A) =
        fourthTensorPi (fun j => unitaryMatrixConjugationLinearMap
          (unitaryTensorFourth (U j)) (A j)) := by
  change (matrixTensorFour (tensorPi (fun j => (U j).val))
      (tensorPi (fun j => (U j).val)) (tensorPi (fun j => (U j).val))
      (tensorPi (fun j => (U j).val)) * fourthTensorPi A) *
    (matrixTensorFour (tensorPi (fun j => (U j).val))
      (tensorPi (fun j => (U j).val)) (tensorPi (fun j => (U j).val))
      (tensorPi (fun j => (U j).val))).conjTranspose = _
  rw [← fourthTensorPi_fourth, ← fourthTensorPi_conjTranspose,
    ← fourthTensorPi_mul, ← fourthTensorPi_mul]
  rfl

/-- Independence of the literal finite gate indices tensorizes the fourth
average, with its exact normalization. -/
theorem fourthAverage_tensorPi
    (U : J → E → Matrix.unitaryGroup α ℂ)
    (A : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthAverage (fun e : J → E => tensorPiUnitary (fun j => U j (e j)))
      (fourthTensorPi A) = fourthTensorPi (fun j => fourthAverage (U j) (A j)) := by
  classical
  unfold fourthAverage
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  simp_rw [fourthConjugation_tensorPi]
  rw [fourthTensorPi_smul, fourthTensorPi_sum]
  congr 1
  simp only [Fintype.card_fun, Nat.cast_pow, Finset.prod_const, Finset.card_univ, inv_pow]

theorem tensorPi_hilbertSchmidt (A B : J → Matrix α α ℂ) :
    qubitFourthComplexHilbertSchmidt (tensorPi A) (tensorPi B) =
      ∏ j, qubitFourthComplexHilbertSchmidt (A j) (B j) := by
  classical
  simp only [qubitFourthComplexHilbertSchmidt_eq_entrywise, tensorPi, star_prod,
    ← Finset.prod_mul_distrib]
  have hy (x : J → α) :
      (∑ y : J → α, ∏ j, star (A j (x j) (y j)) * B j (x j) (y j)) =
        ∏ j, ∑ y : α, star (A j (x j) y) * B j (x j) y :=
    (Fintype.prod_sum (fun j y => star (A j (x j) y) * B j (x j) y)).symm
  simp_rw [hy]
  exact (Fintype.prod_sum (fun j x => ∑ y : α, star (A j x y) * B j x y)).symm

theorem submatrix_hilbertSchmidt
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ≃ ι) (A B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt (A.submatrix e e) (B.submatrix e e) =
      qubitFourthComplexHilbertSchmidt A B := by
  simp only [qubitFourthComplexHilbertSchmidt_eq_entrywise, Matrix.submatrix_apply]
  have hy (x : κ) : (∑ y : κ, star (A (e x) (e y)) * B (e x) (e y)) =
      ∑ y : ι, star (A (e x) y) * B (e x) y :=
    Equiv.sum_comp e (fun y : ι => star (A (e x) y) * B (e x) y)
  simp_rw [hy]
  exact Equiv.sum_comp e (fun x : ι => ∑ y : ι, star (A x y) * B x y)

theorem fourthTensorPi_hilbertSchmidt
    (A B : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    qubitFourthComplexHilbertSchmidt (fourthTensorPi A) (fourthTensorPi B) =
      ∏ j, qubitFourthComplexHilbertSchmidt (A j) (B j) := by
  rw [fourthTensorPi, fourthTensorPi, submatrix_hilbertSchmidt]
  exact tensorPi_hilbertSchmidt A B

end
end TomographyOracleCore.Revision.FourthTwirlTensorization
