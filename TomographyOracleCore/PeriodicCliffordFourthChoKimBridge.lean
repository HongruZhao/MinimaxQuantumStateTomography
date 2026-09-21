import TomographyOracleCore.ChoKimBlockDimensionOptimization
import TomographyOracleCore.PeriodicCliffordFourthTransferArithmetic

namespace TomographyOracleCore

/-!
# Exact Cho--Kim parameters for the fourth-copy transfer

This file discharges the arithmetic interface between the physical block
condition and the scalar fourth-copy argument.  For `m = n / K` and
`q = 2^(K/2)`, it proves both `D = q^(2m)` and the exact accumulation
predicate.  No Clifford-moment statement is used here.
-/

noncomputable section

/-- An even block size splits into two equal half-blocks. -/
theorem ChoKimBlockCondition.halfBlock_add_halfBlock_fourth
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    K / 2 + K / 2 = K := by
  obtain ⟨k, rfl⟩ := h.block_even
  omega

/-- Exact Hilbert-space dimension identity for the periodic architecture:
`2^n = ((2^(K/2))^2)^(n/K)` when `K` is an even divisor of `n`. -/
theorem ChoKimBlockCondition.periodicCliffordFourth_dimension
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    (((2 ^ n : ℕ) : ℝ)) =
      (choKimOverlapDimension K ^ 2) ^ (n / K) := by
  obtain ⟨m, rfl⟩ := h.block_dvd
  have hquot : K * m / K = m := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left m h.block_pos
  have hhalf := h.halfBlock_add_halfBlock_fourth
  have htwice : K / 2 * 2 = K := by omega
  rw [hquot]
  simp only [Nat.cast_pow, Nat.cast_ofNat, choKimOverlapDimension]
  calc
    (2 : ℝ) ^ (K * m) = (2 : ℝ) ^ ((K / 2 * 2) * m) := by
      rw [htwice]
    _ = (((2 : ℝ) ^ (K / 2)) ^ 2) ^ m := by
      rw [pow_mul, pow_mul]

/-- The manuscript block condition implies precisely the scalar accumulation
predicate used by the fourth-copy transfer, with `m=n/K` and
`q=2^(K/2)`. -/
theorem ChoKimBlockCondition.periodicCliffordFourth_blockPredicate
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    PeriodicCliffordFourthBlockPredicate (n / K)
      (choKimOverlapDimension K) := by
  constructor
  · have hlarge := h.oneTwentyEight_lt_overlap hn
    linarith
  · obtain ⟨m, rfl⟩ := h.block_dvd
    have hquot : K * m / K = m := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_left m h.block_pos
    rw [hquot]
    have hK : 0 < (K : ℝ) := by exact_mod_cast h.block_pos
    have hlog : 0 < Real.log 2 := log_two_pos
    have hq : 0 < choKimOverlapDimension K :=
      choKimOverlapDimension_pos K
    have hgrowth := h.explicit_growth
    have hcancel :
        (92 / Real.log 2) * (m : ℝ) ≤ choKimOverlapDimension K := by
      apply (mul_le_mul_iff_of_pos_left hK).mp
      calc
        (K : ℝ) * ((92 / Real.log 2) * (m : ℝ)) =
            (92 / Real.log 2) * ((K : ℝ) * (m : ℝ)) := by ring
        _ ≤ (K : ℝ) * choKimOverlapDimension K := by
          simpa [Nat.cast_mul, choKimOverlapDimension] using hgrowth
    apply (div_le_iff₀ hq).2
    have hscale : 0 ≤ Real.log 2 / 92 := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hcancel hscale
    calc
      (m : ℝ) = (Real.log 2 / 92) *
          ((92 / Real.log 2) * (m : ℝ)) := by
        field_simp [hlog.ne']
      _ ≤ (Real.log 2 / 92) * choKimOverlapDimension K := hscaled
      _ = Real.log 2 / 92 * choKimOverlapDimension K := rfl

/-- The complete deterministic parameter package needed by the abstract U4
endpoint. -/
theorem ChoKimBlockCondition.periodicCliffordFourth_parameters
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    (((2 ^ n : ℕ) : ℝ)) =
        (choKimOverlapDimension K ^ 2) ^ (n / K) ∧
      PeriodicCliffordFourthBlockPredicate (n / K)
        (choKimOverlapDimension K) ∧
      65536 ≤ 2 ^ n := by
  exact ⟨h.periodicCliffordFourth_dimension,
    h.periodicCliffordFourth_blockPredicate hn,
    h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn⟩

end

end TomographyOracleCore
