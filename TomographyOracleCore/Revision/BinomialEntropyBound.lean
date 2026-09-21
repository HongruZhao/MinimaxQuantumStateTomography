import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Nat.Choose.Bounds

namespace TomographyOracleCore.Revision.BinomialEntropyBound

/-- The usual binomial entropy estimate, derived directly from one term of
the exponential series. -/
theorem choose_le_exp_mul_div_pow (N h : ℕ) (hh : 0 < h) :
    (N.choose h : ℝ) ≤ (Real.exp 1 * N / h) ^ h := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hf : (0 : ℝ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  have he := Real.pow_div_factorial_le_exp (h : ℝ) hhR.le h
  calc
    (N.choose h : ℝ) ≤ (N : ℝ) ^ h / h.factorial := Nat.choose_le_pow_div h N
    _ = ((N : ℝ) / h) ^ h * ((h : ℝ) ^ h / h.factorial) := by
      rw [div_pow]
      field_simp
    _ ≤ ((N : ℝ) / h) ^ h * Real.exp h :=
      mul_le_mul_of_nonneg_left he (by positivity)
    _ = (Real.exp 1 * N / h) ^ h := by
      rw [show Real.exp (h : ℝ) = (Real.exp 1) ^ h by
        rw [← Real.exp_nat_mul]; simp]
      rw [← mul_pow]
      congr 1
      ring

end TomographyOracleCore.Revision.BinomialEntropyBound
