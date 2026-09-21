import TomographyOracleCore.ChoKimGluingArithmetic

namespace TomographyOracleCore

noncomputable section

/-!
# Product-form arithmetic for one order-three gluing step

This module converts the four multiplicative factors in the general
two-layer gluing estimate into the single reusable loss `choKimFThree`.
It is independent of the operator-valued relative-design proof.
-/

/-- At overlap dimension `q ≥ 18`, the product of the two local B.22 losses,
the B.27 reference-gluing exponential, and the final global B.22 loss is
bounded by the one-step Cho--Kim loss. -/
theorem choKimGluingProduct_le_one_add_fThree
    {q : ℝ} (hq : 18 ≤ q) :
    (1 + (9 / (4 * q)) / (1 - 9 / (4 * q))) ^ 2 *
        Real.exp (9 / (2 * q)) * (1 + 9 / (2 * q)) ≤
      1 + choKimFThree q := by
  let a : ℝ := 9 / q
  let b : ℝ := 9 / (2 * q)
  let c : ℝ := 81 / (2 * q ^ 2)
  let d : ℝ := (9 / (4 * q)) / (1 - 9 / (4 * q))
  let R : ℝ := a + b + c
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hb : b ≤ 1 / 4 := by
    dsimp [b]
    rw [div_le_iff₀ (by positivity : 0 < 2 * q)]
    nlinarith
  have hb1 : b ≤ 1 := hb.trans (by norm_num)
  have hden : 0 < 1 - 9 / (4 * q) := by
    rw [sub_pos]
    apply (div_lt_one (by positivity : 0 < 4 * q)).2
    nlinarith
  have hd0 : 0 ≤ d := by dsimp [d]; positivity
  have hd_le_b : d ≤ b := by
    dsimp [d, b]
    rw [div_le_iff₀ hden]
    field_simp
    nlinarith
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hc_eq : c = a * b := by
    dsimp [a, b, c]
    field_simp
    norm_num
  have hR_eq : R = a + b + a * b := by
    dsimp only [R]
    rw [hc_eq]
  have ha_eq : a = 2 * b := by
    dsimp [a, b]
    field_simp
  have hR1 : R ≤ 1 := by
    have hbquarter : 0 ≤ b * (1 / 4 - b) :=
      mul_nonneg hb0 (sub_nonneg.mpr hb)
    rw [hR_eq, ha_eq]
    nlinarith
  have hnorm : ‖b‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hb0]
    exact hb1
  have hrem := Real.norm_exp_sub_one_sub_id_le hnorm
  have hexp : Real.exp b ≤ 1 + a := by
    have hupper : Real.exp b ≤ 1 + b + b ^ 2 := by
      simp only [Real.norm_eq_abs, abs_of_nonneg hb0] at hrem
      have habs : Real.exp b - 1 - b ≤
          |Real.exp b - 1 - b| := le_abs_self _
      nlinarith
    have hb_sq : b ^ 2 ≤ b := by nlinarith [mul_nonneg hb0 (sub_nonneg.mpr hb1)]
    rw [ha_eq]
    nlinarith
  have hleft_nonneg : 0 ≤ (1 + d) ^ 2 := sq_nonneg _
  have hright_nonneg : 0 ≤ 1 + b := by linarith
  have hproduct :
      (1 + d) ^ 2 * Real.exp b * (1 + b) ≤
        (1 + d) ^ 2 * (1 + a) * (1 + b) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hexp hleft_nonneg) hright_nonneg
  have hfactor : 0 ≤ 2 * b - d * (1 + R) := by
    have hmul : d * (1 + R) ≤ b * 2 := by
      calc
        d * (1 + R) ≤ b * (1 + R) :=
          mul_le_mul_of_nonneg_right hd_le_b (by linarith)
        _ ≤ b * 2 := mul_le_mul_of_nonneg_left (by linarith) hb0
    linarith
  have hpoly :
      (1 + d) ^ 2 * (1 + R) ≤
        1 + 2 * (R + d) * (1 + b) := by
    have hterm1 : 0 ≤ R * (1 + 2 * (b - d)) := by
      exact mul_nonneg hR0 (by nlinarith [sub_nonneg.mpr hd_le_b])
    have hterm2 : 0 ≤ d * (2 * b - d * (1 + R)) :=
      mul_nonneg hd0 hfactor
    nlinarith
  calc
    (1 + (9 / (4 * q)) / (1 - 9 / (4 * q))) ^ 2 *
          Real.exp (9 / (2 * q)) * (1 + 9 / (2 * q)) =
        (1 + d) ^ 2 * Real.exp b * (1 + b) := by rfl
    _ ≤ (1 + d) ^ 2 * (1 + a) * (1 + b) := hproduct
    _ = (1 + d) ^ 2 * (1 + R) := by rw [hR_eq]; ring
    _ ≤ 1 + 2 * (R + d) * (1 + b) := hpoly
    _ = 1 + choKimFThree q := by
      dsimp [R, a, b, c, d, choKimFThree]

end

end TomographyOracleCore
