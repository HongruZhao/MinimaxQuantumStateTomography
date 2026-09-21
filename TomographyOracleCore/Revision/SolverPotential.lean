import TomographyOracleCore.MathlibImports

/-! Scalar potential summation for the concrete projected subgradient solver.
The matrix subgradient and projection adapters are not claimed complete here. -/
namespace TomographyOracleCore.Revision
open scoped BigOperators

theorem solver_telescope
    (potential gap : ℕ → ℝ) (h G : ℝ) (J : ℕ) :
    (∀ j < J, potential (j + 1) ≤ potential j - 2 * h * gap j + h ^ 2 * G ^ 2) →
    2 * h * (∑ j ∈ Finset.range J, gap j) ≤
      potential 0 - potential J + (J : ℝ) * h ^ 2 * G ^ 2 := by
  induction J with
  | zero =>
      intro _
      simp
  | succ J ih =>
      intro hs
      have hp := ih (fun j hj => hs j (Nat.lt_trans hj (Nat.lt_succ_self J)))
      have hl := hs J (Nat.lt_succ_self J)
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

/-- The two elementary step-size budget inequalities yield the mean-gap bound. -/
theorem solver_budget_bound
    (potential gap : ℕ → ℝ) (h G gamma : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 0 < J)
    (hzero : potential 0 ≤ 2) (hend : 0 ≤ potential J)
    (hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j + h ^ 2 * G ^ 2)
    (hbudget : 2 ≤ h * (J : ℝ) * gamma)
    (hvariance : h * G ^ 2 ≤ gamma) :
    (∑ j ∈ Finset.range J, gap j) / (J : ℝ) ≤ gamma := by
  have ht := solver_telescope potential gap h G J hstep
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hm := mul_le_mul_of_nonneg_left hvariance
    (show 0 ≤ (J : ℝ) * h by positivity)
  have hmain : 2 * h * (∑ j ∈ Finset.range J, gap j) ≤
      2 * h * ((J : ℝ) * gamma) := by nlinarith
  have hsum : (∑ j ∈ Finset.range J, gap j) ≤ (J : ℝ) * gamma :=
    le_of_mul_le_mul_left hmain (show 0 < 2 * h by positivity)
  apply (div_le_iff₀ hJreal).2
  simpa [mul_comm] using hsum

end TomographyOracleCore.Revision
