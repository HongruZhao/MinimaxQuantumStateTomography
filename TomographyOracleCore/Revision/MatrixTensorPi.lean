import TomographyOracleCore.Revision.FourthSectorDecomposition
import TomographyOracleCore.BinaryCliffordPeriodicCircuit

namespace TomographyOracleCore.Revision.MatrixTensorPi

open FourthSectorDecomposition FourthReplicaPermutations
open scoped BigOperators
noncomputable section

variable {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α]

def tensorPi (A : J → Matrix α α ℂ) : Matrix (J → α) (J → α) ℂ :=
  fun x y => ∏ j, A j (x j) (y j)

theorem tensorPi_mul (A B : J → Matrix α α ℂ) :
    tensorPi (fun j => A j * B j) = tensorPi A * tensorPi B := by
  classical
  ext x y
  simp only [tensorPi, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun j z => A j (x j) z * B j z (y j))

theorem tensorPi_conjTranspose (A : J → Matrix α α ℂ) :
    tensorPi (fun j => (A j).conjTranspose) = (tensorPi A).conjTranspose := by
  ext x y
  simp only [tensorPi, Matrix.conjTranspose_apply, star_prod]

theorem tensorPi_one [DecidableEq α] :
    tensorPi (J := J) (fun _ => (1 : Matrix α α ℂ)) = 1 := by
  classical
  ext x y
  simp only [tensorPi, Matrix.one_apply, prod_indicator_eq_ite_forall, funext_iff]

theorem tensorPi_smul (c : J → ℂ) (A : J → Matrix α α ℂ) :
    tensorPi (fun j => c j • A j) = (∏ j, c j) • tensorPi A := by
  ext x y
  simp only [tensorPi, Matrix.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]

theorem tensorPi_sum {L : Type*} [Fintype L] (A : J → L → Matrix α α ℂ) :
    tensorPi (fun j => ∑ l, A j l) = ∑ f : J → L, tensorPi (fun j => A j (f j)) := by
  ext x y
  simp only [tensorPi, Matrix.sum_apply]
  exact Fintype.prod_sum _

theorem tensorPi_combination {L : Type*} [Fintype L]
    (c : J → L → ℂ) (A : J → L → Matrix α α ℂ) :
    tensorPi (fun j => ∑ l, c j l • A j l) =
      ∑ f : J → L, (∏ j, c j (f j)) • tensorPi (fun j => A j (f j)) := by
  rw [tensorPi_sum]
  simp_rw [tensorPi_smul]

theorem tensorPi_unitary [DecidableEq α]
    (U : J → Matrix.unitaryGroup α ℂ) :
    tensorPi (fun j => (U j).val) ∈ Matrix.unitaryGroup (J → α) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    ← tensorPi_conjTranspose, ← tensorPi_mul]
  have h (j : J) : (U j).val * (U j).val.conjTranspose = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp (U j).property
  simp_rw [h]
  exact tensorPi_one

def fourthPiEquiv (J α : Type*) : FourthIndex (J → α) ≃ (J → FourthIndex α) where
  toFun x j := (x.1 j, x.2.1 j, x.2.2.1 j, x.2.2.2 j)
  invFun x := (fun j => (x j).1, fun j => (x j).2.1,
    fun j => (x j).2.2.1, fun j => (x j).2.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def fourthTensorPi (A : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    Matrix (FourthIndex (J → α)) (FourthIndex (J → α)) ℂ :=
  (tensorPi A).submatrix (fourthPiEquiv J α) (fourthPiEquiv J α)

theorem fourthTensorPi_mul (A B : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthTensorPi (fun j => A j * B j) = fourthTensorPi A * fourthTensorPi B := by
  classical
  simp only [fourthTensorPi, tensorPi_mul, Matrix.submatrix_mul_equiv]

theorem fourthTensorPi_fourth (A : J → Matrix α α ℂ) :
    fourthTensorPi (fun j => matrixTensorFour (A j) (A j) (A j) (A j)) =
      matrixTensorFour (tensorPi A) (tensorPi A) (tensorPi A) (tensorPi A) := by
  ext x y
  simp only [fourthTensorPi, Matrix.submatrix_apply, tensorPi, fourthPiEquiv,
    Equiv.coe_fn_mk, matrixTensorFour_apply, Finset.prod_mul_distrib]

theorem fourthTensorPi_smul (c : J → ℂ)
    (A : J → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthTensorPi (fun j => c j • A j) = (∏ j, c j) • fourthTensorPi A := by
  rw [fourthTensorPi, tensorPi_smul]
  rfl

theorem fourthTensorPi_sum {L : Type*} [Fintype L]
    (A : J → L → Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthTensorPi (fun j => ∑ l, A j l) =
      ∑ f : J → L, fourthTensorPi (fun j => A j (f j)) := by
  classical
  ext x y
  simp only [fourthTensorPi, tensorPi_sum, Matrix.submatrix_apply, Matrix.sum_apply]

theorem fourthTensorPi_unitary [DecidableEq α]
    (U : J → Matrix.unitaryGroup (FourthIndex α) ℂ) :
    fourthTensorPi (fun j => (U j).val) ∈ Matrix.unitaryGroup (FourthIndex (J → α)) ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  simp only [fourthTensorPi, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv _ _ _ (fourthPiEquiv J α)]
  have h := Matrix.mem_unitaryGroup_iff.mp (tensorPi_unitary U)
  rw [Matrix.star_eq_conjTranspose] at h
  rw [h]
  exact Matrix.submatrix_one_equiv _

end
end TomographyOracleCore.Revision.MatrixTensorPi
