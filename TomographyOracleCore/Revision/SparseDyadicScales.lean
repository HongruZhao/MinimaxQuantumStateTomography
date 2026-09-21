import TomographyOracleCore.Revision.SparseEntropyRate
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseDyadicScales

noncomputable section

def block (j : ℕ) : ℕ := 2 ^ (6 + j)
def size (j : ℕ) : ℕ := 65536 * block j

theorem block_pos (j : ℕ) : 0 < block j := by unfold block; positivity
theorem block_ge_64 (j : ℕ) : 64 ≤ block j := by
  unfold block
  have h : 1 ≤ (2 : ℕ) ^ j := Nat.one_le_pow _ _ (by omega)
  rw [pow_add]
  norm_num
  omega
theorem block_succ (j : ℕ) : block (j + 1) = 2 * block j := by
  unfold block
  rw [show 6 + (j + 1) = (6 + j) + 1 by omega, pow_succ]
  omega
theorem size_eq_pow (j : ℕ) : size j = 2 ^ (22 + j) := by
  unfold size block
  rw [pow_add, pow_add]
  norm_num
  ring
theorem size_pos (j : ℕ) : 0 < size j := by unfold size; exact Nat.mul_pos (by omega) (block_pos j)
theorem size_mono {i j : ℕ} (hij : i ≤ j) : size i ≤ size j := by
  rw [size_eq_pow, size_eq_pow]
  exact Nat.pow_le_pow_right (by omega) (by omega)
theorem size_succ (j : ℕ) : size (j + 1) = 2 * size j := by
  simp only [size, block_succ]
  ring
theorem block_le_size (j : ℕ) : block j ≤ size j := by unfold size; omega
theorem index_lt_size (j : ℕ) : j < size j := by
  induction j with
  | zero => exact size_pos 0
  | succ j ih => rw [size_succ]; have h := size_pos j; omega

theorem exists_lower_dyadic_size {k : ℕ} (hk : size 0 ≤ k) :
    ∃ j, size j ≤ k ∧ k ≤ 2 * size j := by
  have hkpos : 0 < k := (size_pos 0).trans_le hk
  have hpow : 2 ^ 22 ≤ k := by simpa only [size_eq_pow, Nat.add_zero] using hk
  have hl : 22 ≤ Nat.log 2 k := Nat.le_log_of_pow_le (by omega) hpow
  refine ⟨Nat.log 2 k - 22, ?_, ?_⟩
  · rw [size_eq_pow, show 22 + (Nat.log 2 k - 22) = Nat.log 2 k by omega]
    exact Nat.pow_log_le_self 2 hkpos.ne'
  · rw [size_eq_pow, show 22 + (Nat.log 2 k - 22) = Nat.log 2 k by omega]
    have h := Nat.lt_pow_succ_log_self (by omega : 1 < 2) k
    rw [pow_succ] at h
    omega
theorem exponent_room (j : ℕ) : 4 * (22 + j) ≤ 8 * block j := by
  induction j with
  | zero => norm_num [block]
  | succ j ih =>
    rw [block_succ]
    have h := block_pos j
    omega

/-- At every retained dyadic scale the net failure estimate is at most N^-4. -/
theorem dyadic_rate_le_inv_four {N : ℕ} (j : ℕ) (hN : size j ≤ N) :
    (1 / (256 * ((N : ℝ) / size j) ^ 2)) ^ block j ≤ 1 / (N : ℝ) ^ 4 := by
  have hs : 0 < size j := size_pos j
  have hsR : (0 : ℝ) < size j := by exact_mod_cast hs
  have hNR : (0 : ℝ) < N := by exact_mod_cast hs.trans_le hN
  let L : ℝ := (N : ℝ) / size j
  have hL : 1 ≤ L := by
    dsimp [L]
    apply (le_div_iff₀ hsR).mpr
    norm_num
    exact_mod_cast hN
  have hL0 : 0 < L := by linarith
  have hsize : ((size j : ℕ) : ℝ) = (2 : ℝ) ^ (22 + j) := by exact_mod_cast size_eq_pow j
  have hkpow : (size j : ℝ) ^ 4 ≤ (2 : ℝ) ^ (8 * block j) := by
    rw [hsize, ← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    have h := exponent_room j
    omega
  have hLpow : L ^ 4 ≤ L ^ (2 * block j) := by
    apply pow_le_pow_right₀ hL
    have h := block_ge_64 j
    omega
  have hprod := mul_le_mul hkpow hLpow (by positivity) (by positivity)
  have hden : (N : ℝ) ^ 4 ≤ (256 * L ^ 2) ^ block j := by
    calc
      _ = (size j : ℝ) ^ 4 * L ^ 4 := by dsimp [L]; field_simp
      _ ≤ (2 : ℝ) ^ (8 * block j) * L ^ (2 * block j) := hprod
      _ = _ := by rw [pow_mul, pow_mul, ← mul_pow]; norm_num
  change (1 / (256 * L ^ 2)) ^ block j ≤ _
  rw [div_pow, one_pow]
  exact one_div_le_one_div_of_le (by positivity) hden

end
end TomographyOracleCore.Revision.SparseDyadicScales
