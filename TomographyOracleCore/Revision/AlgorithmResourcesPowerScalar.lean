import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Elementary, gap-free power-method estimates. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open scoped BigOperators

theorem power_tangent_le (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (p : ℕ) :
    x ^ (p + 1) + ((p : ℝ) + 1) * x ^ p * y ≤ (x + y) ^ (p + 1) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have hm := mul_le_mul_of_nonneg_right ih (add_nonneg hx hy)
    have hn : 0 ≤ (p : ℝ) + 1 := by positivity
    have hterm : 0 ≤ ((p : ℝ) + 1) * x ^ p * y ^ 2 := by positivity
    simp only [Nat.cast_add, Nat.cast_one, pow_succ] at *
    nlinarith

/-- A scalar spectral value below M contributes a controlled power-weighted gap. -/
theorem power_weighted_gap_le (x M : ℝ) (hx : 0 ≤ x) (hxM : x ≤ M) (p : ℕ) :
    ((p : ℝ) + 1) * x ^ p * (M - x) ≤ M ^ (p + 1) := by
  have h := power_tangent_le x (M - x) hx (sub_nonneg.mpr hxM) p
  rw [add_sub_cancel] at h
  exact (le_add_of_nonneg_left (pow_nonneg hx (p + 1))).trans h

/-- Trace-moment ratio is close to the largest nonnegative spectral value.
No eigenvalue separation assumption is made. -/
theorem spectral_moment_ratio_lower
    {ι : Type*} [Fintype ι] (values : ι → ℝ) (j : ι)
    (hvalues : ∀ i, 0 ≤ values i)
    (hmax : ∀ i, values i ≤ values j) (hpos : 0 < values j) (p : ℕ) :
    values j - (Fintype.card ι : ℝ) * values j / ((p : ℝ) + 1) ≤
      (∑ i, values i ^ (p + 1)) / (∑ i, values i ^ p) := by
  classical
  have hsumPos : 0 < ∑ i, values i ^ p :=
    Finset.sum_pos' (fun i _ => pow_nonneg (hvalues i) p)
      ⟨j, Finset.mem_univ _, pow_pos hpos p⟩
  have hsingle : values j ^ p ≤ ∑ i, values i ^ p :=
    Finset.single_le_sum (fun i _ => pow_nonneg (hvalues i) p) (Finset.mem_univ j)
  have hsum := Finset.sum_le_sum
    (fun i (_hi : i ∈ (Finset.univ : Finset ι)) =>
      power_weighted_gap_le (values i) (values j) (hvalues i) (hmax i) p)
  have hid : (∑ i, ((p : ℝ) + 1) * values i ^ p * (values j - values i)) =
      ((p : ℝ) + 1) *
        (values j * (∑ i, values i ^ p) - (∑ i, values i ^ (p + 1))) := by
    simp_rw [mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring
  rw [hid] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hlast : (Fintype.card ι : ℝ) * values j ^ (p + 1) ≤
      (Fintype.card ι : ℝ) * values j * (∑ i, values i ^ p) := by
    rw [pow_succ]
    nlinarith [mul_le_mul_of_nonneg_left hsingle
      (mul_nonneg (Nat.cast_nonneg (Fintype.card ι)) hpos.le)]
  have hfull := hsum.trans hlast
  have hp : 0 < (p : ℝ) + 1 := by positivity
  have hquot : (values j * (∑ i, values i ^ p) - (∑ i, values i ^ (p + 1))) /
      (∑ i, values i ^ p) ≤
        (Fintype.card ι : ℝ) * values j / ((p : ℝ) + 1) := by
    apply (div_le_div_iff₀ hsumPos hp).2
    nlinarith [hfull]
  rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt hsumPos)] at hquot
  linarith

theorem weighted_ratio_le_of_pointwise
    {ι : Type*} [Fintype ι] (weights scores : ι → ℝ) (R : ℝ)
    (hsum : 0 < ∑ i, weights i)
    (hpoint : ∀ i, scores i ≤ R * weights i) :
    (∑ i, scores i) / (∑ i, weights i) ≤ R := by
  apply (div_le_iff₀ hsum).2
  simpa only [Finset.mul_sum] using
    (Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset ι)) => hpoint i)

#print axioms spectral_moment_ratio_lower

end TomographyOracleCore.Revision.AlgorithmResources
