import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

/-!
# Exact periodic Cho--Kim block condition

This module records only the arithmetic and architecture side conditions from
the manuscript.  It makes no Pauli-channel, design, variance, oracle, or
minimax assertion.
-/

/-- Hilbert-space dimension of an `n`-qubit system. -/
def qubitDimension (n : ℕ) : ℕ := 2 ^ n

/-- The manuscript's explicit sufficient periodic block condition.  `K` is a
positive even divisor of `n`, and the numerical lower bound fixes the hidden
constant in `K * 2^(K/2) = Omega(n)` to `92 / log 2`. -/
def ChoKimBlockCondition (n K : ℕ) : Prop :=
  0 < K ∧ Even K ∧ K ∣ n ∧
    (92 / Real.log 2) * (n : ℝ) ≤
      (K : ℝ) * (2 : ℝ) ^ (K / 2)

theorem ChoKimBlockCondition.block_pos {n K : ℕ}
    (h : ChoKimBlockCondition n K) : 0 < K :=
  h.1

theorem ChoKimBlockCondition.block_even {n K : ℕ}
    (h : ChoKimBlockCondition n K) : Even K :=
  h.2.1

theorem ChoKimBlockCondition.block_dvd {n K : ℕ}
    (h : ChoKimBlockCondition n K) : K ∣ n :=
  h.2.2.1

theorem ChoKimBlockCondition.explicit_growth {n K : ℕ}
    (h : ChoKimBlockCondition n K) :
    (92 / Real.log 2) * (n : ℝ) ≤
      (K : ℝ) * (2 : ℝ) ^ (K / 2) :=
  h.2.2.2

theorem log_two_pos : 0 < Real.log 2 :=
  Real.log_pos (by norm_num)

/-- A positive divisor is no larger than a positive ambient qubit count. -/
theorem ChoKimBlockCondition.block_le_qubits {n K : ℕ}
    (h : ChoKimBlockCondition n K) (hn : 0 < n) : K ≤ n :=
  Nat.le_of_dvd hn h.block_dvd

end TomographyOracleCore
