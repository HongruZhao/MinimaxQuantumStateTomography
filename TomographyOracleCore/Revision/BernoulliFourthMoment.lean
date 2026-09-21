import TomographyOracleCore.Revision.BernoulliFiniteAverage

namespace TomographyOracleCore.Revision.BernoulliFourthMoment

open FiniteProbabilityAverage BernoulliFiniteAverage
open scoped BigOperators
noncomputable section

theorem average_centeredSum_sq (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) :
    average (bernoulliLaw p hp k) (fun omega => centeredSum p a omega ^ 2) =
      p * (1 - p) * ∑ i, a i ^ 2 := by
  induction k with
  | zero => simp [centeredSum]
  | succ k ih =>
    rw [average_succ_inside]
    calc
      _ = average (bernoulliLaw p hp k) (fun omega =>
          centeredSum p (fun i => a i.succ) omega ^ 2 + p * (1 - p) * a 0 ^ 2) := by
        apply average_congr
        intro omega
        simp only [centeredSum_cons, bitValue, if_true, Bool.false_eq_true, if_false]
        ring
      _ = _ := by rw [average_add, average_const, ih, Fin.sum_univ_succ]; ring

/-- Exact fourth moment, including the Bernoulli fourth cumulant. -/
theorem average_centeredSum_fourth (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) :
    average (bernoulliLaw p hp k) (fun omega => centeredSum p a omega ^ 4) =
      p * (1 - p) * (1 - 6 * p + 6 * p ^ 2) * ∑ i, a i ^ 4 +
        3 * p ^ 2 * (1 - p) ^ 2 * (∑ i, a i ^ 2) ^ 2 := by
  induction k with
  | zero => simp [centeredSum]
  | succ k ih =>
    rw [average_succ_inside]
    calc
      _ = average (bernoulliLaw p hp k) (fun omega =>
          centeredSum p (fun i => a i.succ) omega ^ 4 +
          (6 * p * (1 - p) * a 0 ^ 2) * centeredSum p (fun i => a i.succ) omega ^ 2 +
          (4 * p * (1 - p) * (1 - 2 * p) * a 0 ^ 3) * centeredSum p (fun i => a i.succ) omega +
          p * (1 - p) * (1 - 3 * p + 3 * p ^ 2) * a 0 ^ 4) := by
        apply average_congr
        intro omega
        simp only [centeredSum_cons, bitValue, if_true, Bool.false_eq_true, if_false]
        ring
      _ = _ := by
        simp only [average_add, average_const_mul, average_const,
          average_centeredSum, mul_zero, add_zero, average_centeredSum_sq, ih,
          Fin.sum_univ_succ]
        ring

theorem average_centeredSum_fourth_le (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) :
    average (bernoulliLaw p hp k) (fun omega => centeredSum p a omega ^ 4) ≤
      p * ∑ i, a i ^ 4 + 3 * p ^ 2 * (∑ i, a i ^ 2) ^ 2 := by
  rw [average_centeredSum_fourth]
  have hpp : p ^ 2 ≤ p := by nlinarith [hp.1, hp.2]
  have hc1 : p * (1 - p) * (1 - 6 * p + 6 * p ^ 2) ≤ p := by
    calc
      _ ≤ p * (1 - p) * 1 := mul_le_mul_of_nonneg_left (by nlinarith)
        (mul_nonneg hp.1 (by linarith [hp.2]))
      _ ≤ p := by nlinarith [sq_nonneg p]
  have hc2 : 3 * p ^ 2 * (1 - p) ^ 2 ≤ 3 * p ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg p) (show 0 ≤ 1 - (1 - p) ^ 2 by nlinarith)]
  exact add_le_add
    (mul_le_mul_of_nonneg_right hc1 (Finset.sum_nonneg fun _ _ => by positivity))
    (mul_le_mul_of_nonneg_right hc2 (sq_nonneg _))

theorem average_selectedSum_sq (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) :
    average (bernoulliLaw p hp k) (fun omega => selectedSum a omega ^ 2) =
      p ^ 2 * (∑ i, a i) ^ 2 + p * (1 - p) * ∑ i, a i ^ 2 := by
  calc
    _ = average (bernoulliLaw p hp k) (fun omega =>
        centeredSum p a omega ^ 2 + (2 * p * ∑ i, a i) * centeredSum p a omega +
          p ^ 2 * (∑ i, a i) ^ 2) := by
      apply average_congr
      intro omega
      rw [selectedSum_eq_centeredSum_add p]
      ring
    _ = _ := by
      rw [average_add, average_add, average_const_mul, average_const,
        average_centeredSum, average_centeredSum_sq]
      ring

theorem add_fourth_le (a b : ℝ) : (a + b) ^ 4 ≤ 8 * (a ^ 4 + b ^ 4) := by
  have h := mul_nonneg (sq_nonneg (a - b))
    (show 0 ≤ 2 * (a ^ 2 + b ^ 2) + 5 * (a + b) ^ 2 by positivity)
  nlinarith

theorem average_selectedSum_fourth_le (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) :
    average (bernoulliLaw p hp k) (fun omega => selectedSum a omega ^ 4) ≤
      8 * p ^ 4 * (∑ i, a i) ^ 4 +
        8 * p * ∑ i, a i ^ 4 + 24 * p ^ 2 * (∑ i, a i ^ 2) ^ 2 := by
  have hpoint (omega : Fin k → Bool) :=
    add_fourth_le (centeredSum p a omega) (p * ∑ i, a i)
  simp only [← selectedSum_eq_centeredSum_add] at hpoint
  have h := average_mono (bernoulliLaw p hp k) hpoint
  rw [average_const_mul, average_add, average_const] at h
  have hc := average_centeredSum_fourth_le p hp a
  nlinarith

/-- A coefficient-size condition prevents excessive fourth-moment growth
under Bernoulli coordinate sparsification. -/
theorem average_selectedSum_fourth_le_second_sq (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (hphalf : p ≤ 1 / 2) {k : ℕ} (a : Fin k → ℝ)
    (hcoeff : ∀ i, |a i| ≤ p * |∑ j, a j|) :
    average (bernoulliLaw p hp k) (fun omega => selectedSum a omega ^ 4) ≤
      128 * average (bernoulliLaw p hp k) (fun omega => selectedSum a omega ^ 2) ^ 2 := by
  have hp0 : 0 ≤ p := hp.1
  let M := ∑ i, a i
  let V := ∑ i, a i ^ 2
  have hV : 0 ≤ V := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hfourth : (∑ i, a i ^ 4) ≤ p ^ 2 * M ^ 2 * V := by
    calc
      _ ≤ ∑ i, (p ^ 2 * M ^ 2) * a i ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have hs : a i ^ 2 ≤ p ^ 2 * M ^ 2 := by
          have h := sq_le_sq₀ (abs_nonneg (a i)) (mul_nonneg hp.1 (abs_nonneg M))
          have h' := h.2 (hcoeff i)
          simpa only [sq_abs, mul_pow] using h'
        have h := mul_le_mul_of_nonneg_right hs (sq_nonneg (a i))
        nlinarith
      _ = _ := by rw [← Finset.mul_sum]
  have hraw := average_selectedSum_fourth_le p hp a
  have hweighted := mul_le_mul_of_nonneg_left hfourth (show 0 ≤ 8 * p by positivity)
  have hlow : p ^ 2 * M ^ 2 + p * V / 2 ≤
      average (bernoulliLaw p hp k) (fun omega => selectedSum a omega ^ 2) := by
    rw [average_selectedSum_sq]
    change _ ≤ p ^ 2 * M ^ 2 + p * (1 - p) * V
    nlinarith [mul_nonneg (mul_nonneg hp.1 hV) (show 0 ≤ 1 / 2 - p by linarith)]
  have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ p ^ 2 * M ^ 2 + p * V / 2) hlow 2
  have hcross : 0 ≤ p ^ 3 * M ^ 2 * V := by positivity
  change _ ≤ _ at hraw
  dsimp [M, V] at hweighted hsquare hcross
  nlinarith [sq_nonneg (p * ∑ i, a i ^ 2)]

end
end TomographyOracleCore.Revision.BernoulliFourthMoment
