import TomographyOracleCore.Revision.SparseDyadicScales

set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseRecursionWeights

open SparseDyadicScales
noncomputable section

def amplification (N : ℕ) : ℝ := (10 / 9 : ℝ) ^ Nat.log 2 N
def signalWeight (N : ℝ) (j : ℕ) : ℝ := Real.sqrt (Real.sqrt (N * size j))

theorem amplification_ge_one (N : ℕ) : 1 ≤ amplification N := by
  unfold amplification
  exact one_le_pow₀ (by norm_num)
theorem amplification_sixth_le {N : ℕ} (hN : 0 < N) : amplification N ^ 6 ≤ N := by
  calc
    _ = ((10 / 9 : ℝ) ^ 6) ^ Nat.log 2 N := by unfold amplification; rw [← pow_mul, ← pow_mul]; congr 1; omega
    _ ≤ (2 : ℝ) ^ Nat.log 2 N := pow_le_pow_left₀ (by positivity) (by norm_num) _
    _ ≤ (N : ℝ) := by exact_mod_cast Nat.pow_log_le_self 2 hN.ne'
theorem level_amplification_le {N j : ℕ} (hN : size j ≤ N) :
    (10 / 9 : ℝ) ^ j ≤ amplification N := by
  have hp : 2 ^ (22 + j) ≤ N := by simpa only [size_eq_pow] using hN
  have hl := Nat.le_log_of_pow_le (by omega : 1 < 2) hp
  exact pow_le_pow_right₀ (by norm_num) (by omega)

theorem signalWeight_nonneg (N : ℝ) (j : ℕ) : 0 ≤ signalWeight N j := Real.sqrt_nonneg _
theorem signalWeight_sq (N : ℝ) (j : ℕ) :
    signalWeight N j ^ 2 = Real.sqrt (N * size j) := Real.sq_sqrt (Real.sqrt_nonneg _)
theorem sqrt_ratio_scale {N k : ℝ} (hk : 0 < k) :
    Real.sqrt k * Real.sqrt (Real.sqrt (N / k)) = Real.sqrt (Real.sqrt (N * k)) := by
  have heq : N * k = k ^ 2 * (N / k) := by field_simp
  rw [heq, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk.le, Real.sqrt_mul hk.le]
theorem signalWeight_succ (N : ℝ) (j : ℕ) :
    signalWeight N (j + 1) = Real.sqrt (Real.sqrt 2) * signalWeight N j := by
  unfold signalWeight
  rw [size_succ]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  rw [show N * (2 * (size j : ℝ)) = 2 * (N * size j) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul (Real.sqrt_nonneg 2)]
theorem fourth_root_two_ge : (9 / 8 : ℝ) ≤ Real.sqrt (Real.sqrt 2) := by
  have h1 : (81 / 64 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  nlinarith [Real.sq_sqrt (Real.sqrt_nonneg (2 : ℝ)), Real.sqrt_nonneg (Real.sqrt (2 : ℝ))]
theorem signalWeight_growth (N : ℝ) (j : ℕ) :
    (9 / 8 : ℝ) * signalWeight N j ≤ signalWeight N (j + 1) := by
  rw [signalWeight_succ]
  exact mul_le_mul_of_nonneg_right fourth_root_two_ge (signalWeight_nonneg N j)

/-- A scalar dyadic recursion with explicit constants. The small geometric
growth in its first term has a sixth power bounded by the sample size. -/
theorem recursion_bound (G w : ℕ → ℝ) (J : ℕ) {D M H F : ℝ}
    (hD : 0 ≤ D) (hM : 0 ≤ M) (hH : 0 ≤ H) (hF : 0 ≤ F)
    (hw : ∀ j, 0 ≤ w j) (hwgrowth : ∀ j, (9 / 8 : ℝ) * w j ≤ w (j + 1))
    (hzero : G 0 ≤ D * M)
    (hstep : ∀ j < J, G (j + 1) ≤ (17 / 16 : ℝ) * G j + D * M + D * H * w (j + 1) * F) :
    G J ≤ 32 * D * ((10 / 9 : ℝ) ^ J * M + H * w J * F) := by
  induction J with
  | zero =>
    norm_num only [pow_zero, one_mul]
    nlinarith [mul_nonneg hD hM, mul_nonneg (mul_nonneg (mul_nonneg hD hH) (hw 0)) hF]
  | succ J ih =>
    have hprev := ih (fun j hj => hstep j (by omega))
    have hrec := hstep J (by omega)
    have hb : 1 ≤ (10 / 9 : ℝ) ^ J := one_le_pow₀ (by norm_num)
    have hnoise : (17 / 16 : ℝ) * (32 * D * ((10 / 9 : ℝ) ^ J * M)) + D * M ≤
        32 * D * ((10 / 9 : ℝ) ^ (J + 1) * M) := by
      rw [pow_succ]
      have hmul := mul_le_mul_of_nonneg_right hb (mul_nonneg hD hM)
      nlinarith [mul_nonneg hD hM]
    have hsignal : (17 / 16 : ℝ) * (32 * D * (H * w J * F)) + D * H * w (J + 1) * F ≤
        32 * D * (H * w (J + 1) * F) := by
      have hm := mul_le_mul_of_nonneg_left (hwgrowth J) (mul_nonneg (mul_nonneg hD hH) hF)
      have hn := mul_nonneg (mul_nonneg (mul_nonneg hD hH) hF) (hw J)
      nlinarith
    have hp := mul_le_mul_of_nonneg_left hprev (by norm_num : (0 : ℝ) ≤ 17 / 16)
    nlinarith

end
end TomographyOracleCore.Revision.SparseRecursionWeights
