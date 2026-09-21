import TomographyOracleCore.BinaryCliffordFiniteSecondMoment

namespace TomographyOracleCore
open scoped BigOperators

def liftDoubleToTriple12 {ι : Type*} [DecidableEq ι]
    (X : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ :=
  fun x y ↦ X (x.1, x.2.1) (y.1, y.2.1) *
    (1 : Matrix ι ι ℂ) x.2.2 y.2.2

def liftDoubleToTriple13 {ι : Type*} [DecidableEq ι]
    (X : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ :=
  fun x y ↦ X (x.1, x.2.2) (y.1, y.2.2) *
    (1 : Matrix ι ι ℂ) x.2.1 y.2.1

def liftDoubleToTriple23 {ι : Type*} [DecidableEq ι]
    (X : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ :=
  fun x y ↦ X (x.2.1, x.2.2) (y.2.1, y.2.2) *
    (1 : Matrix ι ι ℂ) x.1 y.1

theorem matrixTensorThree_one_right_eq_lift12
    {ι : Type*} [DecidableEq ι]
    (A B : Matrix ι ι ℂ) :
    matrixTensorThree A B 1 =
      liftDoubleToTriple12 (matrixTensorTwo A B) := by
  ext x y
  rfl

theorem matrixTensorThree_one_middle_eq_lift13
    {ι : Type*} [DecidableEq ι]
    (A C : Matrix ι ι ℂ) :
    matrixTensorThree A 1 C =
      liftDoubleToTriple13 (matrixTensorTwo A C) := by
  ext x y
  simp [matrixTensorThree, liftDoubleToTriple13, matrixTensorTwo,
    Matrix.one_apply]

theorem matrixTensorThree_one_left_eq_lift23
    {ι : Type*} [DecidableEq ι]
    (B C : Matrix ι ι ℂ) :
    matrixTensorThree 1 B C =
      liftDoubleToTriple23 (matrixTensorTwo B C) := by
  ext x y
  simp [matrixTensorThree, liftDoubleToTriple23, matrixTensorTwo,
    Matrix.one_apply]

theorem liftDoubleToTriple12_smul {ι : Type*}
    [DecidableEq ι] (c : ℂ)
    (X : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple12 (c • X) = c • liftDoubleToTriple12 X := by
  ext x y
  simp [liftDoubleToTriple12]
  ring

theorem liftDoubleToTriple13_smul {ι : Type*}
    [DecidableEq ι] (c : ℂ)
    (X : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple13 (c • X) = c • liftDoubleToTriple13 X := by
  ext x y
  simp [liftDoubleToTriple13]
  ring

theorem liftDoubleToTriple23_smul {ι : Type*}
    [DecidableEq ι] (c : ℂ)
    (X : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple23 (c • X) = c • liftDoubleToTriple23 X := by
  ext x y
  simp [liftDoubleToTriple23]
  ring

theorem liftDoubleToTriple12_sum
    {ι β : Type*} [DecidableEq ι] [Fintype β]
    (X : β → Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple12 (∑ b : β, X b) =
      ∑ b : β, liftDoubleToTriple12 (X b) := by
  ext x y
  have hleft :
      ((∑ b : β, X b) (x.1, x.2.1) (y.1, y.2.1)) =
        ∑ b : β, X b (x.1, x.2.1) (y.1, y.2.1) := by
    exact Matrix.sum_apply (x.1, x.2.1) (y.1, y.2.1)
      Finset.univ X
  have hright :
      ((∑ b : β, liftDoubleToTriple12 (X b)) x y) =
        ∑ b : β, liftDoubleToTriple12 (X b) x y := by
    exact Matrix.sum_apply x y Finset.univ
      (fun b : β ↦ liftDoubleToTriple12 (X b))
  rw [hright]
  simp [liftDoubleToTriple12, hleft, Finset.sum_mul]

theorem liftDoubleToTriple13_sum
    {ι β : Type*} [DecidableEq ι] [Fintype β]
    (X : β → Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple13 (∑ b : β, X b) =
      ∑ b : β, liftDoubleToTriple13 (X b) := by
  ext x y
  have hleft :
      ((∑ b : β, X b) (x.1, x.2.2) (y.1, y.2.2)) =
        ∑ b : β, X b (x.1, x.2.2) (y.1, y.2.2) := by
    exact Matrix.sum_apply (x.1, x.2.2) (y.1, y.2.2)
      Finset.univ X
  have hright :
      ((∑ b : β, liftDoubleToTriple13 (X b)) x y) =
        ∑ b : β, liftDoubleToTriple13 (X b) x y := by
    exact Matrix.sum_apply x y Finset.univ
      (fun b : β ↦ liftDoubleToTriple13 (X b))
  rw [hright]
  simp [liftDoubleToTriple13, hleft, Finset.sum_mul]

theorem liftDoubleToTriple23_sum
    {ι β : Type*} [DecidableEq ι] [Fintype β]
    (X : β → Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple23 (∑ b : β, X b) =
      ∑ b : β, liftDoubleToTriple23 (X b) := by
  ext x y
  have hleft :
      ((∑ b : β, X b) (x.2.1, x.2.2) (y.2.1, y.2.2)) =
        ∑ b : β, X b (x.2.1, x.2.2) (y.2.1, y.2.2) := by
    exact Matrix.sum_apply (x.2.1, x.2.2) (y.2.1, y.2.2)
      Finset.univ X
  have hright :
      ((∑ b : β, liftDoubleToTriple23 (X b)) x y) =
        ∑ b : β, liftDoubleToTriple23 (X b) x y := by
    exact Matrix.sum_apply x y Finset.univ
      (fun b : β ↦ liftDoubleToTriple23 (X b))
  rw [hright]
  simp [liftDoubleToTriple23, hleft, Finset.sum_mul]

@[simp] theorem liftDoubleToTriple12_zero {ι : Type*} [DecidableEq ι] :
    liftDoubleToTriple12 (0 : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) = 0 := by
  ext x y
  simp [liftDoubleToTriple12]

@[simp] theorem liftDoubleToTriple13_zero {ι : Type*} [DecidableEq ι] :
    liftDoubleToTriple13 (0 : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) = 0 := by
  ext x y
  simp [liftDoubleToTriple13]

@[simp] theorem liftDoubleToTriple23_zero {ι : Type*} [DecidableEq ι] :
    liftDoubleToTriple23 (0 : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) = 0 := by
  ext x y
  simp [liftDoubleToTriple23]

@[simp] theorem liftDoubleToTriple12_one {ι : Type*} [DecidableEq ι] :
    liftDoubleToTriple12 (1 : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) = 1 := by
  ext x y
  simp [liftDoubleToTriple12, Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;>
    by_cases h2 : x.2.1 = y.2.1 <;>
      by_cases h3 : x.2.2 = y.2.2 <;>
        simp [h1, h2, h3] <;> aesop

@[simp] theorem liftDoubleToTriple13_one {ι : Type*} [DecidableEq ι] :
    liftDoubleToTriple13 (1 : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) = 1 := by
  ext x y
  simp [liftDoubleToTriple13, Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;>
    by_cases h2 : x.2.1 = y.2.1 <;>
      by_cases h3 : x.2.2 = y.2.2 <;>
        simp [h1, h2, h3] <;> aesop

@[simp] theorem liftDoubleToTriple23_one {ι : Type*} [DecidableEq ι] :
    liftDoubleToTriple23 (1 : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) = 1 := by
  ext x y
  simp [liftDoubleToTriple23, Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;>
    by_cases h2 : x.2.1 = y.2.1 <;>
      by_cases h3 : x.2.2 = y.2.2 <;>
        simp [h1, h2, h3] <;> aesop

theorem liftDoubleToTriple12_sub {ι : Type*} [DecidableEq ι]
    (X Y : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple12 (X - Y) =
      liftDoubleToTriple12 X - liftDoubleToTriple12 Y := by
  ext x y
  simp [liftDoubleToTriple12]
  ring

theorem liftDoubleToTriple13_sub {ι : Type*} [DecidableEq ι]
    (X Y : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple13 (X - Y) =
      liftDoubleToTriple13 X - liftDoubleToTriple13 Y := by
  ext x y
  simp [liftDoubleToTriple13]
  ring

theorem liftDoubleToTriple23_sub {ι : Type*} [DecidableEq ι]
    (X Y : Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ) :
    liftDoubleToTriple23 (X - Y) =
      liftDoubleToTriple23 X - liftDoubleToTriple23 Y := by
  ext x y
  simp [liftDoubleToTriple23]
  ring

theorem liftDoubleToTriple12_registerSwapTwo (K : ℕ) :
    liftDoubleToTriple12 (registerSwapTwo K) = registerSwap12 K := by
  classical
  ext x y
  simp [liftDoubleToTriple12, registerSwapTwo, registerSwap12,
    Matrix.one_apply]
  by_cases h1 : x.1 = y.2.1 <;>
    by_cases h2 : x.2.1 = y.1 <;>
      by_cases h3 : x.2.2 = y.2.2 <;>
        simp [h1, h2, h3]

theorem liftDoubleToTriple13_registerSwapTwo (K : ℕ) :
    liftDoubleToTriple13 (registerSwapTwo K) = registerSwap13 K := by
  classical
  ext x y
  simp [liftDoubleToTriple13, registerSwapTwo, registerSwap13,
    Matrix.one_apply]
  by_cases h1 : x.1 = y.2.2 <;>
    by_cases h2 : x.2.2 = y.1 <;>
      by_cases h3 : x.2.1 = y.2.1 <;>
        simp [h1, h2, h3]

theorem liftDoubleToTriple23_registerSwapTwo (K : ℕ) :
    liftDoubleToTriple23 (registerSwapTwo K) = registerSwap23 K := by
  classical
  ext x y
  simp [liftDoubleToTriple23, registerSwapTwo, registerSwap23,
    Matrix.one_apply]
  by_cases h1 : x.2.1 = y.2.2 <;>
    by_cases h2 : x.2.2 = y.2.1 <;>
      by_cases h3 : x.1 = y.1 <;>
        simp [h1, h2, h3]

theorem unitaryConjugation_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) :
    (U.1 * (1 : Matrix ι ι ℂ)) * U.1.conjTranspose = 1 := by
  simpa [mul_one, Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff.mp U.2)

theorem conjugatedMatrixTensorThree_one_right_eq_lift12
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A B : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorThree K e A B 1 =
      liftDoubleToTriple12 (conjugatedMatrixTensorTwo K e A B) := by
  rw [conjugatedMatrixTensorThree_eq, conjugatedMatrixTensorTwo_eq,
    unitaryConjugation_one, matrixTensorThree_one_right_eq_lift12]

theorem conjugatedMatrixTensorThree_one_middle_eq_lift13
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A C : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorThree K e A 1 C =
      liftDoubleToTriple13 (conjugatedMatrixTensorTwo K e A C) := by
  rw [conjugatedMatrixTensorThree_eq, conjugatedMatrixTensorTwo_eq,
    unitaryConjugation_one, matrixTensorThree_one_middle_eq_lift13]

theorem conjugatedMatrixTensorThree_one_left_eq_lift23
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (B C : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorThree K e 1 B C =
      liftDoubleToTriple23 (conjugatedMatrixTensorTwo K e B C) := by
  rw [conjugatedMatrixTensorThree_eq, conjugatedMatrixTensorTwo_eq,
    unitaryConjugation_one, matrixTensorThree_one_left_eq_lift23]

noncomputable def averagedHermitianPauliThirdMoment
    (K : ℕ) (p q r : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
    ∑ e : PauliCosetCliffordEnsemble K,
      conjugatedMatrixTensorThree K e
        (hermitianBinaryPauliMatrix K p)
        (hermitianBinaryPauliMatrix K q)
        (hermitianBinaryPauliMatrix K r)

theorem averagedHermitianPauliThirdMoment_zero_right_eq_lift12
    (K : ℕ) (p q : PauliLabel K) :
    averagedHermitianPauliThirdMoment K p q 0 =
      liftDoubleToTriple12
        (averagedHermitianPauliSecondMoment K p q) := by
  unfold averagedHermitianPauliThirdMoment
    averagedHermitianPauliSecondMoment
  rw [hermitianBinaryPauliMatrix_zero]
  simp_rw [conjugatedMatrixTensorThree_one_right_eq_lift12]
  rw [liftDoubleToTriple12_smul, liftDoubleToTriple12_sum]
  rfl

theorem averagedHermitianPauliThirdMoment_zero_middle_eq_lift13
    (K : ℕ) (p r : PauliLabel K) :
    averagedHermitianPauliThirdMoment K p 0 r =
      liftDoubleToTriple13
        (averagedHermitianPauliSecondMoment K p r) := by
  unfold averagedHermitianPauliThirdMoment
    averagedHermitianPauliSecondMoment
  rw [hermitianBinaryPauliMatrix_zero]
  simp_rw [conjugatedMatrixTensorThree_one_middle_eq_lift13]
  rw [liftDoubleToTriple13_smul, liftDoubleToTriple13_sum]
  rfl

theorem averagedHermitianPauliThirdMoment_zero_left_eq_lift23
    (K : ℕ) (q r : PauliLabel K) :
    averagedHermitianPauliThirdMoment K 0 q r =
      liftDoubleToTriple23
        (averagedHermitianPauliSecondMoment K q r) := by
  unfold averagedHermitianPauliThirdMoment
    averagedHermitianPauliSecondMoment
  rw [hermitianBinaryPauliMatrix_zero]
  simp_rw [conjugatedMatrixTensorThree_one_left_eq_lift23]
  rw [liftDoubleToTriple23_smul, liftDoubleToTriple23_sum]
  rfl

theorem averagedHermitianPauliThirdMoment_zero_right_eq_zero_of_ne
    (K : ℕ) (p q : PauliLabel K) (hpq : p ≠ q) :
    averagedHermitianPauliThirdMoment K p q 0 = 0 := by
  rw [averagedHermitianPauliThirdMoment_zero_right_eq_lift12,
    averagedHermitianPauliSecondMoment_eq_zero_of_ne K p q hpq]
  simp

theorem averagedHermitianPauliThirdMoment_zero_middle_eq_zero_of_ne
    (K : ℕ) (p r : PauliLabel K) (hpr : p ≠ r) :
    averagedHermitianPauliThirdMoment K p 0 r = 0 := by
  rw [averagedHermitianPauliThirdMoment_zero_middle_eq_lift13,
    averagedHermitianPauliSecondMoment_eq_zero_of_ne K p r hpr]
  simp

theorem averagedHermitianPauliThirdMoment_zero_left_eq_zero_of_ne
    (K : ℕ) (q r : PauliLabel K) (hqr : q ≠ r) :
    averagedHermitianPauliThirdMoment K 0 q r = 0 := by
  rw [averagedHermitianPauliThirdMoment_zero_left_eq_lift23,
    averagedHermitianPauliSecondMoment_eq_zero_of_ne K q r hqr]
  simp

theorem averagedHermitianPauliThirdMoment_same_zero_eq_swap12
    (K : ℕ) (Q : NonidentityPauliLabel K) :
    averagedHermitianPauliThirdMoment K Q.1 Q.1 0 =
      ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
        (((2 : ℂ) ^ K) • registerSwap12 K - 1) := by
  rw [averagedHermitianPauliThirdMoment_zero_right_eq_lift12,
    averagedHermitianPauliSecondMoment_same_eq_swap]
  rw [liftDoubleToTriple12_smul, liftDoubleToTriple12_sub,
    liftDoubleToTriple12_smul,
    liftDoubleToTriple12_registerSwapTwo, liftDoubleToTriple12_one]

theorem averagedHermitianPauliThirdMoment_same_zero_eq_swap13
    (K : ℕ) (Q : NonidentityPauliLabel K) :
    averagedHermitianPauliThirdMoment K Q.1 0 Q.1 =
      ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
        (((2 : ℂ) ^ K) • registerSwap13 K - 1) := by
  rw [averagedHermitianPauliThirdMoment_zero_middle_eq_lift13,
    averagedHermitianPauliSecondMoment_same_eq_swap]
  rw [liftDoubleToTriple13_smul, liftDoubleToTriple13_sub,
    liftDoubleToTriple13_smul,
    liftDoubleToTriple13_registerSwapTwo, liftDoubleToTriple13_one]

theorem averagedHermitianPauliThirdMoment_zero_same_eq_swap23
    (K : ℕ) (Q : NonidentityPauliLabel K) :
    averagedHermitianPauliThirdMoment K 0 Q.1 Q.1 =
      ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
        (((2 : ℂ) ^ K) • registerSwap23 K - 1) := by
  rw [averagedHermitianPauliThirdMoment_zero_left_eq_lift23,
    averagedHermitianPauliSecondMoment_same_eq_swap]
  rw [liftDoubleToTriple23_smul, liftDoubleToTriple23_sub,
    liftDoubleToTriple23_smul,
    liftDoubleToTriple23_registerSwapTwo, liftDoubleToTriple23_one]

theorem averagedHermitianPauliThirdMoment_zero_zero_zero (K : ℕ) :
    averagedHermitianPauliThirdMoment K 0 0 0 = 1 := by
  rw [averagedHermitianPauliThirdMoment_zero_right_eq_lift12,
    averagedHermitianPauliSecondMoment_zero_zero,
    liftDoubleToTriple12_one]

end TomographyOracleCore
