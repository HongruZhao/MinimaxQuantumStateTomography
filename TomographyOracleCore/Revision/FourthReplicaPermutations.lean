import TomographyOracleCore.Revision.BinaryCliffordNeutralFourth

namespace TomographyOracleCore.Revision.FourthReplicaPermutations

open BinaryCliffordNeutralFourth
open scoped BigOperators

noncomputable section

def fourthTupleCoordinatesEquiv (ι : Type*) : FourthIndex ι ≃ (Fin 4 → ι) where
  toFun x := ![x.1, x.2.1, x.2.2.1, x.2.2.2]
  invFun f := (f 0, f 1, f 2, f 3)
  left_inv x := rfl
  right_inv f := by funext i; fin_cases i <;> rfl

def permuteFourthTuple {ι : Type*} (pi : Equiv.Perm (Fin 4)) (x : FourthIndex ι) :
    FourthIndex ι :=
  (fourthTupleCoordinatesEquiv ι).symm
    (fun i => fourthTupleCoordinatesEquiv ι x (pi i))

@[simp]
theorem coordinates_permuteFourthTuple
    {ι : Type*} (pi : Equiv.Perm (Fin 4)) (x : FourthIndex ι) (i : Fin 4) :
    fourthTupleCoordinatesEquiv ι (permuteFourthTuple pi x) i =
      fourthTupleCoordinatesEquiv ι x (pi i) := by
  exact congrFun ((fourthTupleCoordinatesEquiv ι).apply_symm_apply _) i

def permuteFourthTupleEquiv (ι : Type*) (pi : Equiv.Perm (Fin 4)) :
    Equiv.Perm (FourthIndex ι) where
  toFun := permuteFourthTuple pi
  invFun := permuteFourthTuple pi.symm
  left_inv x := by
    apply (fourthTupleCoordinatesEquiv ι).injective
    funext i
    simp
  right_inv x := by
    apply (fourthTupleCoordinatesEquiv ι).injective
    funext i
    simp

def fourthReplicaPermutationMatrix {ι : Type*} [DecidableEq ι]
    (pi : Equiv.Perm (Fin 4)) : Matrix (FourthIndex ι) (FourthIndex ι) ℂ :=
  fun x y => if y = permuteFourthTuple pi x then 1 else 0

theorem fourthReplicaPermutationMatrix_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pi : Equiv.Perm (Fin 4)) (A : Matrix (FourthIndex ι) (FourthIndex ι) ℂ)
    (x y : FourthIndex ι) :
    (fourthReplicaPermutationMatrix (ι := ι) pi * A) x y = A (permuteFourthTuple pi x) y := by
  simp [fourthReplicaPermutationMatrix, Matrix.mul_apply]

theorem mul_fourthReplicaPermutationMatrix
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pi : Equiv.Perm (Fin 4)) (A : Matrix (FourthIndex ι) (FourthIndex ι) ℂ)
    (x y : FourthIndex ι) :
    (A * fourthReplicaPermutationMatrix (ι := ι) pi) x y = A x (permuteFourthTuple pi.symm y) := by
  have heq (z : FourthIndex ι) :
      y = permuteFourthTuple pi z ↔ z = permuteFourthTuple pi.symm y := by
    change y = permuteFourthTupleEquiv ι pi z ↔
      z = (permuteFourthTupleEquiv ι pi).symm y
    rw [eq_comm (a := y)]
    exact (Equiv.eq_symm_apply (permuteFourthTupleEquiv ι pi)).symm
  simp only [Matrix.mul_apply, fourthReplicaPermutationMatrix, heq]
  simp

theorem matrixTensorFourth_apply_product {ι : Type*}
    (A : Matrix ι ι ℂ) (x y : FourthIndex ι) :
    matrixTensorFour A A A A x y =
      ∏ i : Fin 4, A (fourthTupleCoordinatesEquiv ι x i)
        (fourthTupleCoordinatesEquiv ι y i) := by
  rw [Fin.prod_univ_four, matrixTensorFour_apply]
  rfl

/-- A simultaneous fourth tensor power commutes with every permutation of
its replica slots. This is an entrywise finite-product identity. -/
theorem fourthReplicaPermutationMatrix_commute_tensorFourth
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (pi : Equiv.Perm (Fin 4)) (A : Matrix ι ι ℂ) :
    fourthReplicaPermutationMatrix (ι := ι) pi * matrixTensorFour A A A A =
      matrixTensorFour A A A A * fourthReplicaPermutationMatrix (ι := ι) pi := by
  ext x y
  rw [fourthReplicaPermutationMatrix_mul, mul_fourthReplicaPermutationMatrix,
    matrixTensorFourth_apply_product, matrixTensorFourth_apply_product]
  simp only [coordinates_permuteFourthTuple]
  have h := Equiv.prod_comp pi (fun i =>
    A (fourthTupleCoordinatesEquiv ι x i) (fourthTupleCoordinatesEquiv ι y (pi.symm i)))
  simpa only [Equiv.symm_apply_apply] using h

/-- Physical fourth-copy conjugation fixes every replica permutation. -/
theorem unitaryFourthConjugation_fixes_permutation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (pi : Equiv.Perm (Fin 4)) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
        (fourthReplicaPermutationMatrix pi) = fourthReplicaPermutationMatrix pi := by
  change (matrixTensorFour U.val U.val U.val U.val * fourthReplicaPermutationMatrix pi) *
    (matrixTensorFour U.val U.val U.val U.val).conjTranspose = _
  rw [← fourthReplicaPermutationMatrix_commute_tensorFourth, mul_assoc]
  have hU : (unitaryTensorFourth U).val * (unitaryTensorFourth U).val.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      Matrix.mem_unitaryGroup_iff.mp (unitaryTensorFourth U).property
  change fourthReplicaPermutationMatrix pi *
    ((unitaryTensorFourth U).val * (unitaryTensorFourth U).val.conjTranspose) = _
  rw [hU, mul_one]

end

end TomographyOracleCore.Revision.FourthReplicaPermutations
