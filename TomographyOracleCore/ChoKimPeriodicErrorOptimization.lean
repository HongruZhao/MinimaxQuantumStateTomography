import TomographyOracleCore.ChoKimPeriodicUnconditionalRelativeDesign

namespace TomographyOracleCore

noncomputable section

/-!
# Optimized periodic Cho--Kim gluing error

The original unconditional endpoint records the convenient bound
`choKimPeriodicThirdDesignError n K ≤ 1`.  The exact same hypotheses imply
the sharper universal estimate `≤ 2 / 3`.  The key point is to retain the
literal spanning-path edge count `2 * (n / K) - 1`: its final subtraction
absorbs all finite-overlap corrections to the asymptotic coefficient `63/2`.

No circuit, design, or statistical assumption is changed in this module.
-/

/-- Exact rational form of the order-three two-block gluing loss. -/
theorem choKimFThree_eq_rational
    {q : ℝ} (hq : 0 < q) (hden : 9 < 4 * q) :
    choKimFThree q =
      9 * (28 * q ^ 3 + 144 * q ^ 2 - 81 * q - 729) /
        (2 * q ^ 3 * (4 * q - 9)) := by
  have hqne : q ≠ 0 := ne_of_gt hq
  have h4qne : 4 * q - 9 ≠ 0 :=
    ne_of_gt (by linarith : 0 < 4 * q - 9)
  have hfrac :
      (9 / (4 * q)) / (1 - 9 / (4 * q)) = 9 / (4 * q - 9) := by
    field_simp [hqne, h4qne]
  unfold choKimFThree
  rw [hfrac]
  ring_nf
  have h4qne' : -9 + q * 4 ≠ 0 := by nlinarith
  have h8qne' : -18 + q * 8 ≠ 0 := by nlinarith
  field_simp [hqne, h4qne, h4qne', h8qne']
  ring

/-- Exact accumulated exponent estimate.  Here `m` is the number of
`K`-qubit blocks and `q` is their staggered overlap dimension. -/
theorem choKimAccumulatedExactExponent_le_sixtyThree
    {m : ℕ} (hm : 0 < m) {q : ℝ} (hq : 18 ≤ q)
    (hgrowth : (92 / Real.log 2) * (m : ℝ) ≤ q) :
    (((2 * m - 1 : ℕ) : ℝ)) * choKimFThree q ≤
      (63 / 92 : ℝ) * Real.log 2 := by
  let c : ℝ := Real.log 2 / 92
  have hlog : 0 < Real.log 2 := log_two_pos
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 / 92 := by
    dsimp [c]
    have hl : Real.log 2 ≤ 1 :=
      (Real.log_two_lt_d9.trans (by norm_num)).le
    nlinarith
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have h4q9 : 9 < 4 * q := by nlinarith
  have hmle : (m : ℝ) ≤ c * q := by
    have hg' : 92 * (m : ℝ) ≤ q * Real.log 2 := by
      apply (div_le_iff₀ hlog).mp
      calc
        92 * (m : ℝ) / Real.log 2 =
            (92 / Real.log 2) * (m : ℝ) := by ring
        _ ≤ q := hgrowth
    dsimp [c]
    nlinarith
  have hrcast : (((2 * m - 1 : ℕ) : ℝ)) = 2 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    rfl
  have hf0 : 0 ≤ choKimFThree q := choKimFThree_nonneg hq
  have hrle : (((2 * m - 1 : ℕ) : ℝ)) ≤ 2 * c * q - 1 := by
    rw [hrcast]
    nlinarith
  have hcoef : 0 ≤ 252 - 3726 * c := by nlinarith
  have hmain :
      0 ≤ q ^ 3 * (252 - 3726 * c) +
        q ^ 2 * (1296 + 1458 * c) +
        q * (13122 * c - 729) - 6561 := by
    have hA : 0 ≤ q ^ 3 * (252 - 3726 * c) :=
      mul_nonneg (pow_nonneg hq0.le 3) hcoef
    have hB : 0 ≤ 1458 * c * q ^ 2 := by positivity
    have hC : 0 ≤ 13122 * c * q := by positivity
    have hD : 0 ≤ 1296 * q ^ 2 - 729 * q - 6561 := by
      nlinarith
    nlinarith
  have hscalar :
      (2 * c * q - 1) * choKimFThree q ≤ 63 * c := by
    rw [choKimFThree_eq_rational hq0 h4q9]
    have hdenpos : 0 < 2 * q ^ 3 * (4 * q - 9) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hdenpos).2
    dsimp [c] at hmain ⊢
    nlinarith
  calc
    (((2 * m - 1 : ℕ) : ℝ)) * choKimFThree q ≤
        (2 * c * q - 1) * choKimFThree q :=
      mul_le_mul_of_nonneg_right hrle hf0
    _ ≤ 63 * c := hscalar
    _ = (63 / 92 : ℝ) * Real.log 2 := by
      dsimp [c]
      ring

/-- The literal periodic error schedule is bounded by the sharp exponential
constant delivered by the exact accumulated exponent. -/
theorem ChoKimBlockCondition.choKimPeriodicThirdDesignError_add_one_le_exp
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    1 + choKimPeriodicThirdDesignError n K ≤
      Real.exp ((63 / 92 : ℝ) * Real.log 2) := by
  let m := n / K
  let q := choKimOverlapDimension K
  have hm : 0 < m := by
    dsimp [m]
    exact Nat.div_pos (h.block_le_qubits hn) h.block_pos
  have hq : 18 ≤ q := by
    simpa [q] using h.eighteen_le_overlap hn
  have hgrowth : (92 / Real.log 2) * (m : ℝ) ≤ q := by
    obtain ⟨r, rfl⟩ := h.block_dvd
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast h.block_pos
    have hdiv : K * r / K = r := by
      rw [Nat.mul_comm]
      exact Nat.mul_div_left r h.block_pos
    dsimp [m]
    rw [hdiv]
    have hg := h.explicit_growth
    push_cast at hg
    simpa [q, mul_assoc] using
      (mul_le_mul_iff_of_pos_left hKreal).mp (by
        calc
          (K : ℝ) * ((92 / Real.log 2) * (r : ℝ)) =
              (92 / Real.log 2) * ((K : ℝ) * (r : ℝ)) := by ring
          _ ≤ (K : ℝ) * choKimOverlapDimension K := by
            simpa [choKimOverlapDimension] using hg)
  have hexponent :=
    choKimAccumulatedExactExponent_le_sixtyThree hm hq hgrowth
  have hpow := one_add_pow_le_exp_nat_mul
    (choKimFThree_nonneg hq) (2 * m - 1)
  rw [choKimPeriodicThirdDesignError_eq]
  change 1 + ((1 + choKimFThree q) ^ (2 * m - 1) - 1) ≤ _
  calc
    1 + ((1 + choKimFThree q) ^ (2 * m - 1) - 1) =
        (1 + choKimFThree q) ^ (2 * m - 1) := by ring
    _ ≤ _ := hpow.trans (Real.exp_le_exp.mpr hexponent)

/-- A rational envelope for the optimized exponential constant. -/
theorem exp_sixtyThree_div_ninetyTwo_log_two_le_five_thirds :
    Real.exp ((63 / 92 : ℝ) * Real.log 2) ≤ 5 / 3 := by
  have hx : (63 / 92 : ℝ) * Real.log 2 ≤ 1 / 2 := by
    nlinarith [Real.log_two_lt_d9]
  have hehalf : Real.exp (1 / 2 : ℝ) < 5 / 3 := by
    have hsquare : (Real.exp (1 / 2 : ℝ)) ^ 2 = Real.exp 1 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have he : Real.exp (1 : ℝ) < (5 / 3 : ℝ) ^ 2 :=
      Real.exp_one_lt_d9.trans (by norm_num)
    have hp : 0 < Real.exp (1 / 2 : ℝ) := Real.exp_pos _
    rw [← hsquare] at he
    nlinarith
  exact (Real.exp_le_exp.mpr hx).trans hehalf.le

/-- Optimized unconditional periodic relative-design error.  This has the
same hypotheses and quantifiers as the earlier bound by one. -/
theorem ChoKimBlockCondition.choKimPeriodicThirdDesignError_le_two_thirds
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimPeriodicThirdDesignError n K ≤ 2 / 3 := by
  have he := h.choKimPeriodicThirdDesignError_add_one_le_exp hn
  have hf := exp_sixtyThree_div_ninetyTwo_log_two_le_five_thirds
  nlinarith

end

end TomographyOracleCore
