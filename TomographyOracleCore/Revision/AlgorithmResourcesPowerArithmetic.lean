import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Rational complex arithmetic and the executable column-power search.
The procedure uses exact rational arithmetic, including a rational Rayleigh
quotient. No algebraic eigenvectors or square-root routine are assumed.
-/

namespace TomographyOracleCore.Revision.AlgorithmResources

open scoped BigOperators
open Matrix

/-- Gaussian rational numbers, with the existing computable ring operations. -/
abbrev QComplex := QuadraticAlgebra ℚ (-1) 0

/-- Mathematical interpretation of the executable rational-complex data. -/
noncomputable def qComplexToComplex : QComplex →+* ℂ :=
  (QuadraticAlgebra.lift (R := ℚ) (a := -1) (b := 0) (A := ℂ)
    ⟨Complex.I, by simp [Algebra.smul_def]⟩).toRingHom

@[simp] theorem qComplexToComplex_apply (z : QComplex) :
    qComplexToComplex z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  simp [qComplexToComplex, QuadraticAlgebra.lift, Algebra.smul_def]

@[simp] theorem qComplexToComplex_re (z : QComplex) :
    (qComplexToComplex z).re = (z.re : ℝ) := by
  simp [qComplexToComplex_apply]

@[simp] theorem qComplexToComplex_im (z : QComplex) :
    (qComplexToComplex z).im = (z.im : ℝ) := by
  simp [qComplexToComplex_apply]

theorem qComplexToComplex_injective : Function.Injective qComplexToComplex := by
  intro z w h
  apply QuadraticAlgebra.ext
  · have hr := congrArg Complex.re h
    simpa using hr
  · have hi := congrArg Complex.im h
    simpa using hi

@[simp] theorem qComplexToComplex_star (z : QComplex) :
    qComplexToComplex (star z) = star (qComplexToComplex z) := by
  apply Complex.ext <;> simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

def qNormSq (z : QComplex) : ℚ := z.re ^ 2 + z.im ^ 2

theorem qNormSq_nonneg (z : QComplex) : 0 ≤ qNormSq z :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

@[simp] theorem qNormSq_eq_zero (z : QComplex) : qNormSq z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hr : z.re = 0 := by
      have := sq_nonneg z.im
      unfold qNormSq at h
      nlinarith [sq_nonneg z.re]
    have hi : z.im = 0 := by
      unfold qNormSq at h
      rw [hr] at h
      nlinarith [sq_nonneg z.im]
    ext <;> assumption
  · rintro rfl
    simp [qNormSq]

@[simp] theorem qComplexToComplex_normSq (z : QComplex) :
    Complex.normSq (qComplexToComplex z) = (qNormSq z : ℝ) := by
  simp [Complex.normSq_apply, qNormSq, pow_two]

def qVectorNormSq {n : Type*} [Fintype n] (v : n → QComplex) : ℚ :=
  ∑ i, qNormSq (v i)

theorem qVectorNormSq_nonneg {n : Type*} [Fintype n] (v : n → QComplex) :
    0 ≤ qVectorNormSq v := Finset.sum_nonneg fun _ _ => qNormSq_nonneg _

@[simp] theorem qVectorNormSq_eq_zero {n : Type*} [Fintype n] (v : n → QComplex) :
    qVectorNormSq v = 0 ↔ v = 0 := by
  simp only [qVectorNormSq, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => qNormSq_nonneg (v i)), Finset.mem_univ, forall_const,
    qNormSq_eq_zero, funext_iff, Pi.zero_apply]

noncomputable def castQMatrix {n m : Type*} (A : Matrix n m QComplex) :
    Matrix n m ℂ := A.map qComplexToComplex

@[simp] theorem castQMatrix_apply {n m : Type*} (A : Matrix n m QComplex) (i j) :
    castQMatrix A i j = qComplexToComplex (A i j) := rfl

@[simp] theorem castQMatrix_mul {n : Type*} [Fintype n]
    (A B : Matrix n n QComplex) :
    castQMatrix (A * B) = castQMatrix A * castQMatrix B := Matrix.map_mul

@[simp] theorem castQMatrix_pow {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n QComplex) (k : ℕ) :
    castQMatrix (A ^ k) = castQMatrix A ^ k := Matrix.map_pow _ _ _

/-- The unnormalized column used by the power iteration. -/
def qPowerColumn {d : ℕ} (A : Matrix (Fin d) (Fin d) QComplex)
    (k : ℕ) (j : Fin d) : Fin d → QComplex := fun i => (A ^ k) i j

def qRayleigh {d : ℕ} (A : Matrix (Fin d) (Fin d) QComplex)
    (v : Fin d → QComplex) : ℚ :=
  (∑ i, star (v i) * (A *ᵥ v) i).re / qVectorNormSq v

/-- A completely executable maximum search over the d standard starting vectors. -/
def qBestPowerColumn {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) : Fin d :=
  ((List.finRange d).argmax (fun j => qRayleigh A (qPowerColumn A k j))).getD ⟨0, hD⟩

theorem qBestPowerColumn_max {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) (j : Fin d) :
    qRayleigh A (qPowerColumn A k j) ≤
      qRayleigh A (qPowerColumn A k (qBestPowerColumn hD A k)) := by
  unfold qBestPowerColumn
  cases ho : (List.finRange d).argmax
      (fun j => qRayleigh A (qPowerColumn A k j)) with
  | none =>
    have he := List.argmax_eq_none.mp ho
    have hj : j ∈ List.finRange d := List.mem_finRange j
    rw [he] at hj
    simp at hj
  | some best =>
    simp only [Option.getD_some]
    exact List.le_of_mem_argmax (f := fun j => qRayleigh A (qPowerColumn A k j))
      (List.mem_finRange j) ho

#print axioms qComplexToComplex_injective
#print axioms qBestPowerColumn_max

end TomographyOracleCore.Revision.AlgorithmResources
