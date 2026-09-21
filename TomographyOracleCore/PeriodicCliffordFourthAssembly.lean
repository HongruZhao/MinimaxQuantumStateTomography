import TomographyOracleCore.PeriodicCliffordFourthCycle
import TomographyOracleCore.PeriodicCliffordFourthTransferArithmetic

namespace TomographyOracleCore

/-!
# Assembly of the finite trace cycle with the scalar fourth-copy transfer

This module removes the formerly abstract trace-cycle hypothesis from the
scalar transfer theorem.  The remaining scientific premise is the concrete
Clifford-twirl expansion that bounds `moment` by the displayed boundary and
Weingarten factors.
-/

noncomputable section

/-- Once the periodic label sum is identified with the trace of a
nonnegative 30-sector Gram power, the cycle estimate is automatic. -/
theorem periodicCliffordFourthContraction_of_matrixCycle_under_block
    {m : ℕ} {s moment boundary : ℝ}
    (G : Matrix (Fin 30) (Fin 30) ℝ)
    (hblock : PeriodicCliffordFourthBlockPredicate m s)
    (hG : ∀ i j, 0 ≤ G i j)
    (hrow : ∀ i, ∑ j, G i j = cliffordFourthGramRowSum s)
    (hboundary0 : 0 ≤ boundary) (hboundary1 : boundary ≤ 1)
    (hmoment : moment ≤
      boundary * cliffordFourthWgSignedRowSum (s ^ 2) ^ m *
        cliffordFourthWgAbsoluteRowSum (s ^ 2) ^ m *
          Matrix.trace (G ^ (2 * m))) :
    moment ≤ 30 * (2 : ℝ) ^ (7 / 46 : ℝ) /
      ((s ^ 2) ^ 4) ^ m := by
  have hpow : ∀ i j, 0 ≤ (G ^ (2 * m)) i j :=
    Matrix.pow_apply_nonneg hG (2 * m)
  have hcycle0 : 0 ≤ Matrix.trace (G ^ (2 * m)) := by
    rw [Matrix.trace]
    exact Finset.sum_nonneg fun i _ ↦ hpow i i
  have hcycle : Matrix.trace (G ^ (2 * m)) ≤
      30 * cliffordFourthGramRowSum s ^ (2 * m) :=
    periodicCliffordFourthTraceCycle_le G
      (cliffordFourthGramRowSum s) hG hrow m
  exact periodicCliffordFourthContraction_under_block hblock
    hboundary0 hboundary1 hcycle0 hmoment hcycle

/-- Algebraically rewrite the accumulated dimension denominator in terms of
`D = (s^2)^m`. -/
theorem periodicCliffordFourth_dimension_pow_four
    (m : ℕ) (s : ℝ) :
    ((s ^ 2) ^ 4) ^ m = ((s ^ 2) ^ m) ^ 4 := by
  calc
    ((s ^ 2) ^ 4) ^ m = (s ^ 2) ^ (4 * m) :=
      (pow_mul (s ^ 2) 4 m).symm
    _ = (s ^ 2) ^ (m * 4) := by rw [Nat.mul_comm]
    _ = ((s ^ 2) ^ m) ^ 4 := pow_mul (s ^ 2) m 4

/-- The same assembled endpoint in the conventional `D^-4` form. -/
theorem periodicCliffordFourthContraction_dimension_form
    {m : ℕ} {s moment boundary : ℝ}
    (G : Matrix (Fin 30) (Fin 30) ℝ)
    (hblock : PeriodicCliffordFourthBlockPredicate m s)
    (hG : ∀ i j, 0 ≤ G i j)
    (hrow : ∀ i, ∑ j, G i j = cliffordFourthGramRowSum s)
    (hboundary0 : 0 ≤ boundary) (hboundary1 : boundary ≤ 1)
    (hmoment : moment ≤
      boundary * cliffordFourthWgSignedRowSum (s ^ 2) ^ m *
        cliffordFourthWgAbsoluteRowSum (s ^ 2) ^ m *
          Matrix.trace (G ^ (2 * m))) :
    moment ≤ 30 * (2 : ℝ) ^ (7 / 46 : ℝ) /
      ((s ^ 2) ^ m) ^ 4 := by
  rw [← periodicCliffordFourth_dimension_pow_four m s]
  exact periodicCliffordFourthContraction_of_matrixCycle_under_block G
    hblock hG hrow hboundary0 hboundary1 hmoment

end

end TomographyOracleCore
