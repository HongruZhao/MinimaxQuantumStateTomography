import TomographyOracleCore.PauliCharacterDiagonalization
import Mathlib.LinearAlgebra.Matrix.Trace

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Concrete binary Pauli matrices and computational-basis dephasing

The Hilbert-space basis is indexed by binary words.  We realize the unphased
Pauli label `(x,z)` as the monomial matrix `X^x Z^z` and prove directly that
the computational-basis measurement/dephasing channel retains it exactly
when `x = 0` and kills it otherwise.

This closes the matrix calculation inside one measurement basis.  The
remaining physical Clifford interface is the theorem that conjugation by a
uniform Clifford permutes these matrices through the binary symplectic
action, up to a phase that cancels under conjugated dephasing.
-/

/-- Concrete computational-basis projector `|b><b|`. -/
def computationalBasisProjector {K : ℕ} (b : PauliBinaryWord K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  Matrix.single b b 1

/-- The measurement channel of the computational basis, written literally
as the sum of Born trace coefficients times rank-one basis projectors. -/
noncomputable def computationalBasisMeasurementChannel (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  ∑ b : PauliBinaryWord K,
    (A * computationalBasisProjector b).trace •
      computationalBasisProjector b

/-- The literal measurement-channel sum is the diagonal projection. -/
theorem computationalBasisMeasurementChannel_apply (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (i j : PauliBinaryWord K) :
    computationalBasisMeasurementChannel K A i j =
      if i = j then A i i else 0 := by
  classical
  simp [computationalBasisMeasurementChannel,
    computationalBasisProjector, Matrix.trace_mul_single]
  rw [Matrix.sum_apply (β := PauliBinaryWord K) i j Finset.univ
    (fun b : PauliBinaryWord K ↦ Matrix.single b b (A b b))]
  by_cases hij : i = j
  · subst j
    simp [Matrix.single_apply]
  · rw [if_neg hij]
    have hno (b : PauliBinaryWord K) : ¬(b = i ∧ b = j) := by
      rintro ⟨rfl, h⟩
      exact hij h
    simp [hno]

/-- Matrix form of the computational-basis measurement channel. -/
theorem computationalBasisMeasurementChannel_eq_diagonal (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    computationalBasisMeasurementChannel K A =
      Matrix.diagonal (Matrix.diag A) := by
  classical
  ext i j
  rw [computationalBasisMeasurementChannel_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij]

/-- Computational-basis measurement is homogeneous over complex scalars. -/
theorem computationalBasisMeasurementChannel_smul (K : ℕ) (c : ℂ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    computationalBasisMeasurementChannel K (c • A) =
      c • computationalBasisMeasurementChannel K A := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    simp [computationalBasisMeasurementChannel_apply]
  · simp [computationalBasisMeasurementChannel_apply, hij]

/-- Unphased binary Pauli matrix `X^x Z^z`.  Rows and columns are binary
computational-basis words. -/
noncomputable def binaryPauliMatrix (K : ℕ) (p : PauliLabel K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ :=
  fun a b ↦
    if a = b + p.1 then
      (binaryWordCharacter K p.2 b : ℂ)
    else 0

/-- Adding a fixed binary word to a basis word fixes that basis word only
for the zero word. -/
theorem binaryWord_eq_add_iff_right_eq_zero (K : ℕ)
    (a x : PauliBinaryWord K) : a = a + x ↔ x = 0 := by
  constructor
  · intro h
    apply add_left_cancel (a := a)
    simpa using h.symm
  · rintro rfl
    simp

/-- A binary Pauli is computational-basis diagonal exactly when its `X`
word is zero. -/
theorem computationalBasisMeasurementChannel_binaryPauliMatrix
    (K : ℕ) (p : PauliLabel K) :
    computationalBasisMeasurementChannel K (binaryPauliMatrix K p) =
      if p.1 = 0 then binaryPauliMatrix K p else 0 := by
  classical
  ext i j
  rw [computationalBasisMeasurementChannel_apply]
  by_cases hx : p.1 = 0
  · rw [if_pos hx]
    by_cases hij : i = j
    · subst j
      simp [binaryPauliMatrix, hx]
    · simp [binaryPauliMatrix, hx, hij]
  · rw [if_neg hx]
    by_cases hij : i = j
    · subst j
      have hfix : ¬i = i + p.1 := by
        simpa [binaryWord_eq_add_iff_right_eq_zero K i p.1] using hx
      simp [binaryPauliMatrix, hfix]
    · simp [hij]

/-- The identity Pauli is represented by the identity matrix. -/
theorem binaryPauliMatrix_zero (K : ℕ) :
    binaryPauliMatrix K 0 = 1 := by
  classical
  ext i j
  simp [binaryPauliMatrix, Matrix.one_apply]

/-- Every binary Pauli matrix has a nonzero entry and is therefore nonzero. -/
theorem binaryPauliMatrix_ne_zero (K : ℕ) (p : PauliLabel K) :
    binaryPauliMatrix K p ≠ 0 := by
  classical
  intro hzero
  let b : PauliBinaryWord K := 0
  have hentry := congrFun (congrFun hzero (b + p.1)) b
  simp [binaryPauliMatrix, b] at hentry

end TomographyOracleCore
