import TomographyOracleCore.BinaryPauliDephasing
import Mathlib.LinearAlgebra.UnitaryGroup

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Matrix algebra for binary Paulis

The unphased monomial matrices from `BinaryPauliDephasing` multiply with the
usual binary-character cocycle.  A label-dependent fourth-root phase then
makes every Pauli Hermitian and involutive.  These identities are the matrix
input for a constructive Clifford lift of binary symplectic transvections.
-/

/-- Multiplication law for the concrete unphased binary Pauli matrices. -/
theorem binaryPauliMatrix_mul (K : ℕ) (p q : PauliLabel K) :
    binaryPauliMatrix K p * binaryPauliMatrix K q =
      (binaryWordCharacter K p.2 q.1 : ℂ) •
        binaryPauliMatrix K (p + q) := by
  classical
  ext a b
  rw [Matrix.smul_apply]
  change (binaryPauliMatrix K p * binaryPauliMatrix K q) a b =
    (binaryWordCharacter K p.2 q.1 : ℂ) *
      binaryPauliMatrix K (p + q) a b
  rw [Matrix.mul_apply]
  rw [Fintype.sum_eq_single (b + q.1)]
  · by_cases hab : a = b + (p.1 + q.1)
    · subst a
      simp only [binaryPauliMatrix]
      simp only [Prod.fst_add, Prod.snd_add]
      rw [if_pos (by abel)]
      simp only [if_true]
      rw [binaryWordCharacter_add_right,
        binaryWordCharacter_add_left]
      push_cast
      ring
    · have hne : a ≠ (b + q.1) + p.1 := by
        intro h
        apply hab
        rw [h]
        abel
      simp [binaryPauliMatrix, hab, hne]
  · intro k hk
    have hk' : k ≠ b + q.1 := by
      intro h
      exact hk h
    simp [binaryPauliMatrix, hk']

/-- Squaring an unphased binary Pauli produces its cocycle sign. -/
theorem binaryPauliMatrix_sq (K : ℕ) (p : PauliLabel K) :
    binaryPauliMatrix K p * binaryPauliMatrix K p =
      (binaryWordCharacter K p.2 p.1 : ℂ) • 1 := by
  rw [binaryPauliMatrix_mul, pauliLabel_add_self,
    binaryPauliMatrix_zero]

/-- The adjoint of an unphased binary Pauli differs by the same cocycle
sign that occurs in its square. -/
theorem binaryPauliMatrix_conjTranspose (K : ℕ) (p : PauliLabel K) :
    (binaryPauliMatrix K p).conjTranspose =
      (binaryWordCharacter K p.2 p.1 : ℂ) •
        binaryPauliMatrix K p := by
  classical
  ext a b
  rw [Matrix.conjTranspose_apply, Matrix.smul_apply]
  by_cases hab : a = b + p.1
  · have hba : b = a + p.1 := by
      rw [hab]
      calc
        b = b + 0 := by simp
        _ = b + (p.1 + p.1) := by
          rw [binaryWord_add_self]
        _ = (b + p.1) + p.1 := by abel
    simp only [binaryPauliMatrix]
    rw [if_pos hba, if_pos hab,
      hab, binaryWordCharacter_add_right]
    push_cast
    simp [smul_eq_mul]
    ring
  · have hba : ¬b = a + p.1 := by
      intro h
      apply hab
      rw [h]
      calc
        a = a + 0 := by simp
        _ = a + (p.1 + p.1) := by
          rw [binaryWord_add_self]
        _ = (a + p.1) + p.1 := by abel
    simp [binaryPauliMatrix, hab, hba]

/-- Every binary word character is a sign. -/
theorem binaryWordCharacter_eq_one_or_neg_one (K : ℕ)
    (x y : PauliBinaryWord K) :
    binaryWordCharacter K x y = 1 ∨
      binaryWordCharacter K x y = -1 := by
  unfold binaryWordCharacter
  rcases zmodTwo_eq_zero_or_one (binaryDotProduct K x y) with h | h
  · left
    simp [h]
  · right
    simp [h]

/-- Phase that turns the unphased monomial `X^x Z^z` into the Hermitian
Pauli with the same binary label. -/
noncomputable def hermitianPauliPhase (K : ℕ) (p : PauliLabel K) : ℂ :=
  if binaryWordCharacter K p.2 p.1 = 1 then 1 else Complex.I

theorem hermitianPauliPhase_ne_zero (K : ℕ) (p : PauliLabel K) :
    hermitianPauliPhase K p ≠ 0 := by
  unfold hermitianPauliPhase
  split_ifs <;> simp

/-- The Hermitian phase cancels the square cocycle. -/
theorem hermitianPauliPhase_sq_mul_character (K : ℕ)
    (p : PauliLabel K) :
    hermitianPauliPhase K p * hermitianPauliPhase K p *
        (binaryWordCharacter K p.2 p.1 : ℂ) = 1 := by
  rcases binaryWordCharacter_eq_one_or_neg_one K p.2 p.1 with h | h
  · simp [hermitianPauliPhase, h]
  · norm_num [hermitianPauliPhase, h, Complex.I_mul_I]

/-- The adjoint phase identity. -/
theorem star_hermitianPauliPhase_mul_character (K : ℕ)
    (p : PauliLabel K) :
    star (hermitianPauliPhase K p) *
        (binaryWordCharacter K p.2 p.1 : ℂ) =
      hermitianPauliPhase K p := by
  rcases binaryWordCharacter_eq_one_or_neg_one K p.2 p.1 with h | h
  · simp [hermitianPauliPhase, h]
  · norm_num [hermitianPauliPhase, h]

/-- Hermitian, involutive binary Pauli matrix. -/
noncomputable def hermitianBinaryPauliMatrix (K : ℕ) (p : PauliLabel K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  hermitianPauliPhase K p • binaryPauliMatrix K p

/-- The phase-corrected binary Pauli is Hermitian. -/
theorem hermitianBinaryPauliMatrix_conjTranspose (K : ℕ)
    (p : PauliLabel K) :
    (hermitianBinaryPauliMatrix K p).conjTranspose =
      hermitianBinaryPauliMatrix K p := by
  rw [hermitianBinaryPauliMatrix, Matrix.conjTranspose_smul,
    binaryPauliMatrix_conjTranspose, smul_smul,
    star_hermitianPauliPhase_mul_character]

/-- Every phase-corrected binary Pauli squares to the identity. -/
theorem hermitianBinaryPauliMatrix_sq (K : ℕ) (p : PauliLabel K) :
    hermitianBinaryPauliMatrix K p * hermitianBinaryPauliMatrix K p = 1 := by
  rw [hermitianBinaryPauliMatrix, Matrix.smul_mul, Matrix.mul_smul,
    binaryPauliMatrix_sq, smul_smul, smul_smul]
  rw [hermitianPauliPhase_sq_mul_character]
  simp

/-- The identity label gives the identity Hermitian Pauli. -/
theorem hermitianBinaryPauliMatrix_zero (K : ℕ) :
    hermitianBinaryPauliMatrix K 0 = 1 := by
  simp [hermitianBinaryPauliMatrix, hermitianPauliPhase,
    binaryPauliMatrix_zero]

/-- The binary dot product is symmetric. -/
theorem binaryDotProduct_comm (K : ℕ) (x y : PauliBinaryWord K) :
    binaryDotProduct K x y = binaryDotProduct K y x := by
  unfold binaryDotProduct
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Word characters are symmetric in their two binary arguments. -/
theorem binaryWordCharacter_comm (K : ℕ) (x y : PauliBinaryWord K) :
    binaryWordCharacter K x y = binaryWordCharacter K y x := by
  unfold binaryWordCharacter
  rw [binaryDotProduct_comm]

/-- A binary character squares to one. -/
theorem binaryWordCharacter_sq (K : ℕ) (x y : PauliBinaryWord K) :
    binaryWordCharacter K x y * binaryWordCharacter K x y = 1 := by
  exact binarySign_sq _

/-- Split the canonical symplectic form into its two binary dot products. -/
theorem pauliSymplecticForm_eq_dot_add_dot (K : ℕ)
    (p q : PauliLabel K) :
    pauliSymplecticForm K p q =
      binaryDotProduct K p.1 q.2 + binaryDotProduct K p.2 q.1 := by
  rw [pauliSymplecticForm_apply]
  unfold binaryDotProduct
  exact Finset.sum_add_distrib

/-- The Pauli commutation character is the product of the two cross-word
characters. -/
theorem pauliCharacter_eq_mul_wordCharacters (K : ℕ)
    (p q : PauliLabel K) :
    pauliCharacter K p q =
      binaryWordCharacter K p.1 q.2 *
        binaryWordCharacter K p.2 q.1 := by
  unfold pauliCharacter binaryWordCharacter
  rw [pauliSymplecticForm_eq_dot_add_dot, binarySign_add]

/-- Concrete Pauli matrices commute or anticommute according to the
canonical symplectic character. -/
theorem binaryPauliMatrix_mul_swap (K : ℕ) (p q : PauliLabel K) :
    binaryPauliMatrix K p * binaryPauliMatrix K q =
      (pauliCharacter K p q : ℂ) •
        (binaryPauliMatrix K q * binaryPauliMatrix K p) := by
  rw [binaryPauliMatrix_mul, binaryPauliMatrix_mul, add_comm q p,
    pauliCharacter_eq_mul_wordCharacters,
    binaryWordCharacter_comm K p.1 q.2, smul_smul]
  apply congrArg (fun c : ℂ ↦ c • binaryPauliMatrix K (p + q))
  have hsq := binaryWordCharacter_sq K q.2 p.1
  have hreal :
      binaryWordCharacter K p.2 q.1 =
        (binaryWordCharacter K q.2 p.1 *
          binaryWordCharacter K p.2 q.1) *
            binaryWordCharacter K q.2 p.1 := by
    calc
      binaryWordCharacter K p.2 q.1 =
          1 * binaryWordCharacter K p.2 q.1 := by ring
      _ = (binaryWordCharacter K q.2 p.1 *
            binaryWordCharacter K q.2 p.1) *
              binaryWordCharacter K p.2 q.1 := by rw [hsq]
      _ = (binaryWordCharacter K q.2 p.1 *
            binaryWordCharacter K p.2 q.1) *
              binaryWordCharacter K q.2 p.1 := by ring
  exact_mod_cast hreal

end TomographyOracleCore
