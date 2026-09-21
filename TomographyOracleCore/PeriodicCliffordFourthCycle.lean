import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace TomographyOracleCore

/-!
# The elementary periodic trace-cycle bound

This file closes the finite-matrix part of the periodic fourth-copy transfer.
It uses only entrywise nonnegativity and a constant row sum.  No spectral
theorem, Clifford classification, twirling identity, or probabilistic input is
used here.
-/

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Powers of a finite matrix with constant row sum `g` have constant row sum
`g ^ k`. -/
theorem matrixPow_rowSum_eq_pow
    (G : Matrix ι ι ℝ) (g : ℝ)
    (hrow : ∀ i, ∑ j, G i j = g) :
    ∀ k i, ∑ j, (G ^ k) i j = g ^ k := by
  intro k
  induction k with
  | zero =>
      intro i
      simp [Matrix.one_apply]
  | succ k ih =>
      intro i
      rw [pow_succ]
      simp_rw [Matrix.mul_apply]
      calc
        ∑ j, ∑ l, (G ^ k) i l * G l j =
            ∑ l, ∑ j, (G ^ k) i l * G l j := Finset.sum_comm
        _ = ∑ l, (G ^ k) i l * g := by
          apply Finset.sum_congr rfl
          intro l _
          rw [← Finset.mul_sum, hrow l]
        _ = (∑ l, (G ^ k) i l) * g := by rw [Finset.sum_mul]
        _ = g ^ k * g := by rw [ih i]
        _ = g ^ (k + 1) := by rw [pow_succ]

/-- The trace of a power of an entrywise nonnegative constant-row-sum matrix
is at most the number of rows times the corresponding row-sum power. -/
theorem matrixTrace_pow_le_card_mul_rowSum_pow
    (G : Matrix ι ι ℝ) (g : ℝ)
    (hG : ∀ i j, 0 ≤ G i j)
    (hrow : ∀ i, ∑ j, G i j = g)
    (k : ℕ) :
    Matrix.trace (G ^ k) ≤ (Fintype.card ι : ℝ) * g ^ k := by
  have hpow : ∀ i j, 0 ≤ (G ^ k) i j :=
    Matrix.pow_apply_nonneg hG k
  have hdiag : ∀ i, (G ^ k) i i ≤ ∑ j, (G ^ k) i j := by
    intro i
    exact Finset.single_le_sum (fun j _ ↦ hpow i j) (Finset.mem_univ i)
  rw [Matrix.trace]
  calc
    ∑ i, Matrix.diag (G ^ k) i ≤ ∑ i, ∑ j, (G ^ k) i j := by
      exact Finset.sum_le_sum fun i _ ↦ hdiag i
    _ = ∑ _i : ι, g ^ k := by
      apply Finset.sum_congr rfl
      intro i _
      exact matrixPow_rowSum_eq_pow G g hrow k i
    _ = (Fintype.card ι : ℝ) * g ^ k := by simp

/-- The exact `30`-sector specialization used in the periodic Clifford
fourth-copy argument. -/
theorem periodicCliffordFourthTraceCycle_le
    (G : Matrix (Fin 30) (Fin 30) ℝ) (g : ℝ)
    (hG : ∀ i j, 0 ≤ G i j)
    (hrow : ∀ i, ∑ j, G i j = g)
    (m : ℕ) :
    Matrix.trace (G ^ (2 * m)) ≤ 30 * g ^ (2 * m) := by
  simpa using matrixTrace_pow_le_card_mul_rowSum_pow G g hG hrow (2 * m)

end

end TomographyOracleCore
