import TomographyOracleCore.Revision.SparseNetConstants
import TomographyOracleCore.Revision.BinomialEntropyBound
import Mathlib.Analysis.Complex.ExponentialBounds

set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseEntropyRate

open SparseNetConstants BinomialEntropyBound
noncomputable section

/-- The entropy inequalities require only a threshold factor 15 after tightening the net radius. The former
factor 1048576 was needlessly large before the final fourth power. -/
def marginalTailRate (L : ℝ) : ℝ := 1 / (15 ^ 6 * L * Real.sqrt L)
def marginalThreshold (kappa s L : ℝ) : ℝ := 15 * kappa * Real.sqrt s * Real.sqrt (Real.sqrt L)

theorem sqrt_sixth {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ^ 6 = x ^ 3 := by
  rw [show 6 = 2 * 3 by norm_num, pow_mul, Real.sq_sqrt hx]
theorem sqrt_sqrt_sixth {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) ^ 6 = x * Real.sqrt x := by
  rw [sqrt_sixth (Real.sqrt_nonneg x)]
  rw [pow_succ, Real.sq_sqrt hx]

theorem marginalThreshold_pos {kappa s L : ℝ} (hk : 0 < kappa) (hs : 0 < s) (hL : 0 < L) :
    0 < marginalThreshold kappa s L := by unfold marginalThreshold; positivity
theorem marginalTailRate_pos {L : ℝ} (hL : 0 < L) : 0 < marginalTailRate L := by
  unfold marginalTailRate; positivity
theorem sixth_tail_rate {kappa s L : ℝ} (hk : 0 < kappa) (hs : 0 < s) (hL : 0 < L) :
    kappa ^ 6 * s ^ 3 / marginalThreshold kappa s L ^ 6 = marginalTailRate L := by
  have hsqrt := (Real.sqrt_pos.mpr hL).ne'
  unfold marginalThreshold marginalTailRate
  rw [mul_pow, mul_pow, mul_pow, sqrt_sixth hs.le, sqrt_sqrt_sixth hL.le]
  field_simp

theorem net_entropy_base {N h : ℝ} (hh : 0 < h) (hN : 0 ≤ N) :
    (Real.exp 1 * N / h) * (1 + 2 / netRadius) ≤
      (2 : ℝ) ^ 61 * (N / (65536 * h)) := by
  have he := Real.exp_one_lt_three.le
  have hprod := mul_le_mul_of_nonneg_right he (show 0 ≤ N / h by positivity)
  have heq : Real.exp 1 * N / h = Real.exp 1 * (N / h) := by ring
  rw [heq]
  dsimp [netRadius]
  have heq' : N / (65536 * h) = (N / h) / 65536 := by field_simp
  rw [heq']
  norm_num
  nlinarith [div_nonneg hN hh.le]

theorem row_entropy_base {N h : ℝ} (hh : 0 < h) (hN : 0 < N) :
    (Real.exp 1 * N / (8 * h)) * marginalTailRate (N / (65536 * h)) ≤
      1 / (500 * Real.sqrt (N / (65536 * h))) := by
  have hL : 0 < N / (65536 * h) := by positivity
  have hsqrt : 0 < Real.sqrt (N / (65536 * h)) := Real.sqrt_pos.mpr hL
  have heq : (Real.exp 1 * N / (8 * h)) * marginalTailRate (N / (65536 * h)) =
      Real.exp 1 * 8192 / (15 ^ 6 * Real.sqrt (N / (65536 * h))) := by
    unfold marginalTailRate
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  have he := mul_le_mul_of_nonneg_right
    (le_trans Real.exp_one_lt_d9.le (by norm_num : (2.7182818286 : ℝ) ≤ 11 / 4)) hsqrt.le
  norm_num at *
  nlinarith [Real.sqrt_nonneg (N / (65536 * h))]

theorem combined_entropy_base {L : ℝ} (hL : 1 ≤ L) :
    ((2 : ℝ) ^ 61 * L) * (1 / (500 * Real.sqrt L)) ^ 8 ≤ 1 / (256 * L ^ 2) := by
  have hL0 : 0 < L := by linarith
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hs8 : Real.sqrt L ^ 8 = L ^ 4 := by
    rw [show 8 = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt hL0.le]
  have heq : ((2 : ℝ) ^ 61 * L) * (1 / (500 * Real.sqrt L)) ^ 8 =
      (2 ^ 61 / 500 ^ 8) / L ^ 3 := by
    rw [div_pow, mul_pow, hs8]
    field_simp
  rw [heq]
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < L ^ 3) (by positivity)).mpr
  norm_num
  nlinarith [mul_le_mul_of_nonneg_right hL (sq_nonneg L)]

/-- Entropy of the sparse net and of the selected rows is dominated by the
sixth-moment tail. This calculation is uniform in the ambient dimension. -/
theorem sparse_net_entropy_bound {N h : ℕ} (hh : 0 < h) (hNh : 65536 * h ≤ N) :
    ((N.choose h : ℝ) * (1 + 2 / netRadius) ^ h) *
        (N.choose (8 * h) : ℝ) * marginalTailRate ((N : ℝ) / (65536 * h)) ^ (8 * h) ≤
      (1 / (256 * ((N : ℝ) / (65536 * h)) ^ 2)) ^ h := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hN : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL : 1 ≤ (N : ℝ) / (65536 * h) := by
    apply (le_div_iff₀ (by positivity)).mpr
    norm_num
    exact_mod_cast hNh
  have hp := (marginalTailRate_pos (show 0 < (N : ℝ) / (65536 * h) by positivity)).le
  have hnetR : 0 ≤ 1 + 2 / netRadius := by norm_num [netRadius]
  have hn := choose_le_exp_mul_div_pow N h hh
  have hr := choose_le_exp_mul_div_pow N (8 * h) (by omega)
  have hn' : (N.choose h : ℝ) * (1 + 2 / netRadius) ^ h ≤
      ((2 : ℝ) ^ 61 * ((N : ℝ) / (65536 * h))) ^ h := by
    calc
      _ ≤ (Real.exp 1 * N / h) ^ h * (1 + 2 / netRadius) ^ h :=
        mul_le_mul_of_nonneg_right hn (pow_nonneg hnetR _)
      _ = ((Real.exp 1 * N / h) * (1 + 2 / netRadius)) ^ h := (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by positivity) hnetR) (net_entropy_base hhR hNR.le) h
  have hr' : (N.choose (8 * h) : ℝ) * marginalTailRate ((N : ℝ) / (65536 * h)) ^ (8 * h) ≤
      (1 / (500 * Real.sqrt ((N : ℝ) / (65536 * h)))) ^ (8 * h) := by
    calc
      _ ≤ (Real.exp 1 * N / (8 * h)) ^ (8 * h) *
          marginalTailRate ((N : ℝ) / (65536 * h)) ^ (8 * h) := by
        apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using hr
      _ = ((Real.exp 1 * N / (8 * h)) * marginalTailRate ((N : ℝ) / (65536 * h))) ^ (8 * h) :=
        (mul_pow _ _ _).symm
      _ ≤ _ := pow_le_pow_left₀ (by positivity) (row_entropy_base hhR hNR) _
  calc
    _ = ((N.choose h : ℝ) * (1 + 2 / netRadius) ^ h) *
        ((N.choose (8 * h) : ℝ) * marginalTailRate ((N : ℝ) / (65536 * h)) ^ (8 * h)) := by ring
    _ ≤ ((2 : ℝ) ^ 61 * ((N : ℝ) / (65536 * h))) ^ h *
        (1 / (500 * Real.sqrt ((N : ℝ) / (65536 * h)))) ^ (8 * h) :=
      mul_le_mul hn' hr' (by positivity) (by positivity)
    _ = (((2 : ℝ) ^ 61 * ((N : ℝ) / (65536 * h))) *
        (1 / (500 * Real.sqrt ((N : ℝ) / (65536 * h)))) ^ 8) ^ h := by rw [pow_mul, ← mul_pow]
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (combined_entropy_base hL) h

end
end TomographyOracleCore.Revision.SparseEntropyRate
