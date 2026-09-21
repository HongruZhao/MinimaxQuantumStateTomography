import TomographyOracleCore.BinaryPauliAlgebra
import Mathlib.LinearAlgebra.UnitaryGroup

namespace TomographyOracleCore

/-!
# Constructive Clifford lifts of binary symplectic transvections

For a Hermitian involutive Pauli `H_a`, the matrix
`((1 - i) / 2) (I + i H_a)` is unitary.  The prefactor differs from the
usual `1 / sqrt 2` only by a global phase and avoids analytic square roots.
Its conjugation action is the binary symplectic transvection along `a`, up
to an irrelevant nonzero Pauli phase.
-/

/-- A convenient unit-modulus normalization divided by `sqrt 2`. -/
noncomputable def cliffordTransvectionScalar : ℂ :=
  (1 - Complex.I) / 2

theorem cliffordTransvectionScalar_mul_star :
    cliffordTransvectionScalar * star cliffordTransvectionScalar =
      (1 / 2 : ℂ) := by
  norm_num [cliffordTransvectionScalar]
  ring_nf
  rw [pow_two]
  rw [Complex.I_mul_I]
  norm_num

/-- Unnormalized transvection numerator `I + i H_a`. -/
noncomputable def cliffordTransvectionNumerator (K : ℕ)
    (a : PauliLabel K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  1 + Complex.I • hermitianBinaryPauliMatrix K a

/-- Adjoint of the transvection numerator. -/
theorem cliffordTransvectionNumerator_conjTranspose (K : ℕ)
    (a : PauliLabel K) :
    (cliffordTransvectionNumerator K a).conjTranspose =
      1 + (-Complex.I) • hermitianBinaryPauliMatrix K a := by
  simp [cliffordTransvectionNumerator, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    hermitianBinaryPauliMatrix_conjTranspose]

/-- The numerator times its adjoint is twice the identity. -/
theorem cliffordTransvectionNumerator_mul_conjTranspose (K : ℕ)
    (a : PauliLabel K) :
    cliffordTransvectionNumerator K a *
        (cliffordTransvectionNumerator K a).conjTranspose =
      (2 : ℂ) • 1 := by
  rw [cliffordTransvectionNumerator_conjTranspose]
  unfold cliffordTransvectionNumerator
  rw [add_mul, mul_add, mul_add]
  simp only [one_mul, mul_one]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    hermitianBinaryPauliMatrix_sq]
  have hi : Complex.I * -Complex.I = 1 := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  rw [hi]
  module

/-- Concrete matrix lifting the symplectic transvection along `a`. -/
noncomputable def cliffordTransvectionMatrix (K : ℕ) (a : PauliLabel K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  cliffordTransvectionScalar • cliffordTransvectionNumerator K a

/-- Adjoint formula for the normalized transvection lift. -/
theorem cliffordTransvectionMatrix_conjTranspose (K : ℕ)
    (a : PauliLabel K) :
    (cliffordTransvectionMatrix K a).conjTranspose =
      star cliffordTransvectionScalar •
        (cliffordTransvectionNumerator K a).conjTranspose := by
  exact Matrix.conjTranspose_smul _ _

/-- The transvection lift is a unitary matrix. -/
theorem cliffordTransvectionMatrix_mem_unitaryGroup (K : ℕ)
    (a : PauliLabel K) :
    cliffordTransvectionMatrix K a ∈
      Matrix.unitaryGroup (PauliBinaryWord K) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    cliffordTransvectionMatrix_conjTranspose]
  unfold cliffordTransvectionMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    cliffordTransvectionNumerator_mul_conjTranspose, smul_smul,
    cliffordTransvectionScalar_mul_star]
  norm_num

/-- The normalized transvection as an element of the matrix unitary group. -/
noncomputable def cliffordTransvectionUnitary (K : ℕ) (a : PauliLabel K) :
    Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
  ⟨cliffordTransvectionMatrix K a,
    cliffordTransvectionMatrix_mem_unitaryGroup K a⟩

/-! ## Conjugation action on concrete Paulis -/

/-- The Hermitian Pauli lift has the same commutation character as the
unphased matrix. -/
theorem hermitianBinaryPauliMatrix_mul_swap (K : ℕ)
    (a p : PauliLabel K) :
    hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p =
      (pauliCharacter K a p : ℂ) •
        (binaryPauliMatrix K p * hermitianBinaryPauliMatrix K a) := by
  unfold hermitianBinaryPauliMatrix
  rw [Matrix.smul_mul, Matrix.mul_smul,
    binaryPauliMatrix_mul_swap, smul_smul, smul_smul]
  congr 1
  ring

/-- Multiplying on the right by a Hermitian Pauli adds its binary label,
with an explicit nonzero phase. -/
theorem binaryPauliMatrix_mul_hermitianBinaryPauliMatrix (K : ℕ)
    (p a : PauliLabel K) :
    binaryPauliMatrix K p * hermitianBinaryPauliMatrix K a =
      (hermitianPauliPhase K a *
          (binaryWordCharacter K p.2 a.1 : ℂ)) •
        binaryPauliMatrix K (p + a) := by
  unfold hermitianBinaryPauliMatrix
  rw [Matrix.mul_smul, binaryPauliMatrix_mul, smul_smul]

/-- Sandwiching by `H_a` multiplies a Pauli by its commutation sign. -/
theorem hermitianBinaryPauliMatrix_sandwich (K : ℕ)
    (a p : PauliLabel K) :
    (hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) *
        hermitianBinaryPauliMatrix K a =
      (pauliCharacter K a p : ℂ) • binaryPauliMatrix K p := by
  rw [hermitianBinaryPauliMatrix_mul_swap]
  rw [Matrix.smul_mul, mul_assoc,
    hermitianBinaryPauliMatrix_sq, mul_one]

/-- Pure algebraic expansion of numerator conjugation. -/
theorem cliffordTransvectionNumerator_conjugation_expand (K : ℕ)
    (a p : PauliLabel K) :
    (cliffordTransvectionNumerator K a * binaryPauliMatrix K p) *
        (cliffordTransvectionNumerator K a).conjTranspose =
      binaryPauliMatrix K p +
        Complex.I •
          (hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) +
        (-Complex.I) •
          (binaryPauliMatrix K p * hermitianBinaryPauliMatrix K a) +
        (Complex.I * -Complex.I) •
          ((hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) *
            hermitianBinaryPauliMatrix K a) := by
  rw [cliffordTransvectionNumerator_conjTranspose]
  unfold cliffordTransvectionNumerator
  noncomm_ring
  module

/-- Normalized conjugation is one half of numerator conjugation. -/
theorem cliffordTransvectionMatrix_conjugation_eq_half (K : ℕ)
    (a p : PauliLabel K) :
    (cliffordTransvectionMatrix K a * binaryPauliMatrix K p) *
        (cliffordTransvectionMatrix K a).conjTranspose =
      (1 / 2 : ℂ) •
        ((cliffordTransvectionNumerator K a * binaryPauliMatrix K p) *
          (cliffordTransvectionNumerator K a).conjTranspose) := by
  rw [cliffordTransvectionMatrix_conjTranspose]
  unfold cliffordTransvectionMatrix
  rw [
    Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul,
    mul_comm (star cliffordTransvectionScalar) cliffordTransvectionScalar,
    cliffordTransvectionScalar_mul_star]

/-- When `p` pairs trivially with `a`, the transvection lift fixes its Pauli
matrix exactly. -/
theorem cliffordTransvectionMatrix_conjugates_of_pair_zero (K : ℕ)
    (a p : PauliLabel K)
    (hpair : pauliSymplecticForm K p a = 0) :
    (cliffordTransvectionMatrix K a * binaryPauliMatrix K p) *
        (cliffordTransvectionMatrix K a).conjTranspose =
      binaryPauliMatrix K p := by
  have hchar : pauliCharacter K a p = 1 := by
    unfold pauliCharacter
    rw [pauliSymplecticForm_symm, hpair]
    simp
  have hi : Complex.I * -Complex.I = 1 := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  calc
    (cliffordTransvectionMatrix K a * binaryPauliMatrix K p) *
          (cliffordTransvectionMatrix K a).conjTranspose =
        (1 / 2 : ℂ) •
          ((cliffordTransvectionNumerator K a * binaryPauliMatrix K p) *
            (cliffordTransvectionNumerator K a).conjTranspose) :=
      cliffordTransvectionMatrix_conjugation_eq_half K a p
    _ = (1 / 2 : ℂ) •
          (binaryPauliMatrix K p +
            Complex.I •
              (hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) +
            (-Complex.I) •
              (binaryPauliMatrix K p * hermitianBinaryPauliMatrix K a) +
            (Complex.I * -Complex.I) •
              ((hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) *
                hermitianBinaryPauliMatrix K a)) := by
      rw [cliffordTransvectionNumerator_conjugation_expand]
    _ = binaryPauliMatrix K p := by
      rw [hermitianBinaryPauliMatrix_sandwich,
        hermitianBinaryPauliMatrix_mul_swap, hchar, hi]
      simp only [one_smul]
      module

/-- When the symplectic pairing is one, conjugation adds the transvection
label, with an explicit nonzero phase. -/
theorem cliffordTransvectionMatrix_conjugates_of_pair_one (K : ℕ)
    (a p : PauliLabel K)
    (hpair : pauliSymplecticForm K p a = 1) :
    (cliffordTransvectionMatrix K a * binaryPauliMatrix K p) *
        (cliffordTransvectionMatrix K a).conjTranspose =
      ((-Complex.I) * hermitianPauliPhase K a *
          (binaryWordCharacter K p.2 a.1 : ℂ)) •
        binaryPauliMatrix K (p + a) := by
  have hchar : pauliCharacter K a p = -1 := by
    unfold pauliCharacter
    rw [pauliSymplecticForm_symm, hpair]
    simp
  have hi : Complex.I * -Complex.I = 1 := by
    rw [mul_neg, Complex.I_mul_I]
    norm_num
  calc
    (cliffordTransvectionMatrix K a * binaryPauliMatrix K p) *
          (cliffordTransvectionMatrix K a).conjTranspose =
        (1 / 2 : ℂ) •
          ((cliffordTransvectionNumerator K a * binaryPauliMatrix K p) *
            (cliffordTransvectionNumerator K a).conjTranspose) :=
      cliffordTransvectionMatrix_conjugation_eq_half K a p
    _ = (1 / 2 : ℂ) •
          (binaryPauliMatrix K p +
            Complex.I •
              (hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) +
            (-Complex.I) •
              (binaryPauliMatrix K p * hermitianBinaryPauliMatrix K a) +
            (Complex.I * -Complex.I) •
              ((hermitianBinaryPauliMatrix K a * binaryPauliMatrix K p) *
                hermitianBinaryPauliMatrix K a)) := by
      rw [cliffordTransvectionNumerator_conjugation_expand]
    _ = (-Complex.I) •
          (binaryPauliMatrix K p * hermitianBinaryPauliMatrix K a) := by
      rw [hermitianBinaryPauliMatrix_sandwich,
        hermitianBinaryPauliMatrix_mul_swap, hchar, hi]
      simp only [neg_smul, one_smul]
      module
    _ = ((-Complex.I) * hermitianPauliPhase K a *
          (binaryWordCharacter K p.2 a.1 : ℂ)) •
        binaryPauliMatrix K (p + a) := by
      rw [binaryPauliMatrix_mul_hermitianBinaryPauliMatrix, smul_smul]
      congr 1
      ring

/-- The explicit phase in the nontrivial transvection branch is nonzero. -/
theorem cliffordTransvectionPhase_ne_zero (K : ℕ)
    (a p : PauliLabel K) :
    (-Complex.I) * hermitianPauliPhase K a *
        (binaryWordCharacter K p.2 a.1 : ℂ) ≠ 0 := by
  apply mul_ne_zero
  · exact mul_ne_zero (by simp) (hermitianPauliPhase_ne_zero K a)
  · exact_mod_cast binarySign_ne_zero (binaryDotProduct K p.2 a.1)

/-- A binary symplectic transvection has a concrete unitary Clifford lift:
conjugation maps every Pauli to the transvected label, up to nonzero phase. -/
theorem cliffordTransvectionMatrix_conjugates_pauli (K : ℕ)
    (a p : PauliLabel K) :
    ∃ phase : ℂ, phase ≠ 0 ∧
      (cliffordTransvectionMatrix K a * binaryPauliMatrix K p) *
          (cliffordTransvectionMatrix K a).conjTranspose =
        phase • binaryPauliMatrix K (pauliTransvection K a p) := by
  rcases zmodTwo_eq_zero_or_one (pauliSymplecticForm K p a) with hpair | hpair
  · refine ⟨1, one_ne_zero, ?_⟩
    rw [cliffordTransvectionMatrix_conjugates_of_pair_zero K a p hpair,
      pauliTransvection_apply, hpair, zero_smul, add_zero, one_smul]
  · refine ⟨(-Complex.I) * hermitianPauliPhase K a *
        (binaryWordCharacter K p.2 a.1 : ℂ),
      cliffordTransvectionPhase_ne_zero K a p, ?_⟩
    rw [cliffordTransvectionMatrix_conjugates_of_pair_one K a p hpair,
      pauliTransvection_apply, hpair, one_smul]

end TomographyOracleCore
