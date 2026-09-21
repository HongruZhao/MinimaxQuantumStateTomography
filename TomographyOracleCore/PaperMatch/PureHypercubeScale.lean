import TomographyOracleCore.PaperMatch.SmallRankReduction

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1000000

def cubeAmplitude (m T : ℕ) : ℝ := 1 / (8 * Real.sqrt (max m T : ℕ))

theorem cubeAmplitude_bounds {m T : ℕ} (hm : 1 ≤ m) :
    0 < cubeAmplitude m T ∧ (m : ℝ) * (cubeAmplitude m T) ^ 2 ≤ 1 / 64 ∧
      (T : ℝ) * (cubeAmplitude m T) ^ 2 ≤ 1 / 64 ∧ (cubeAmplitude m T) ^ 2 ≤ 1 := by
  have hM : (0 : ℝ) < (max m T : ℕ) := by exact_mod_cast (show 0 < max m T by omega)
  have hmp : 0 < Real.sqrt (max m T : ℕ) := Real.sqrt_pos.2 hM
  have ha : 0 < cubeAmplitude m T := by unfold cubeAmplitude; positivity
  have hsq := Real.sq_sqrt hM.le
  have hcancel : ((max m T : ℕ) : ℝ) * (cubeAmplitude m T) ^ 2 = 1 / 64 := by
    unfold cubeAmplitude
    rw [div_pow, mul_pow, hsq]
    field_simp
    <;> ring
  have hmn : (m : ℝ) ≤ (max m T : ℕ) := by exact_mod_cast (le_max_left m T)
  have hTn : (T : ℝ) ≤ (max m T : ℕ) := by exact_mod_cast (le_max_right m T)
  have hmB : (m : ℝ) * (cubeAmplitude m T) ^ 2 ≤ 1 / 64 :=
    (mul_le_mul_of_nonneg_right hmn (sq_nonneg _)).trans_eq hcancel
  have hTB : (T : ℝ) * (cubeAmplitude m T) ^ 2 ≤ 1 / 64 :=
    (mul_le_mul_of_nonneg_right hTn (sq_nonneg _)).trans_eq hcancel
  refine ⟨ha, hmB, hTB, ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := mul_le_mul_of_nonneg_right hm1 (sq_nonneg (cubeAmplitude m T))
  nlinarith

theorem pureRate_le_cube_ratio {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) :
    rankRate (m + 1) T 1 ≤ 2 * Real.sqrt m / Real.sqrt (max m T : ℕ) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hmp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by linarith)
  by_cases hTm : T ≤ m
  · rw [max_eq_left hTm]
    have hid : 2 * Real.sqrt (m : ℝ) / Real.sqrt (m : ℝ) = 2 := by field_simp
    rw [hid]
    exact (min_le_left _ _).trans (by norm_num)
  · rw [max_eq_right (le_of_not_ge hTm)]
    have hp : 0 < Real.sqrt (T : ℝ) := Real.sqrt_pos.2 hTR
    have hms := Real.sq_sqrt (Nat.cast_nonneg m)
    have hTs := Real.sq_sqrt hTR.le
    have hds := Real.sq_sqrt (show 0 ≤ ((m : ℝ) + 1) / (T : ℝ) by positivity)
    have hcs : (2 * Real.sqrt (m : ℝ) / Real.sqrt (T : ℝ)) ^ 2 = 4 * (m : ℝ) / T := by
      rw [div_pow, mul_pow, hms, hTs]
      norm_num
    have hq : ((m : ℝ) + 1) / (T : ℝ) ≤ 4 * (m : ℝ) / T :=
      div_le_div_of_nonneg_right (by linarith) hTR.le
    have hc : Real.sqrt (((m : ℝ) + 1) / (T : ℝ)) ≤
        2 * Real.sqrt (m : ℝ) / Real.sqrt (T : ℝ) := by
      have hn : 0 ≤ 2 * Real.sqrt (m : ℝ) / Real.sqrt (T : ℝ) := by positivity
      nlinarith [Real.sqrt_nonneg (((m : ℝ) + 1) / (T : ℝ))]
    exact (min_le_right _ _).trans (by simpa [rankRate] using hc)

/-- The explicit amplitude yields the advertised universal full-trace constant. -/
theorem cubeAmplitude_risk_scale {m T : ℕ} (hm : 1 ≤ m) (hT : 1 ≤ T) :
    (1 / 128 : ℝ) * rankRate (m + 1) T 1 ≤
      Real.sqrt (1 - (m : ℝ) * (cubeAmplitude m T) ^ 2) *
        cubeAmplitude m T * Real.sqrt m / 4 := by
  obtain ⟨ha, hma, _, _⟩ := cubeAmplitude_bounds (T := T) hm
  have hs := Real.sq_sqrt (show 0 ≤ 1 - (m : ℝ) * (cubeAmplitude m T) ^ 2 by linarith)
  have hh : 1 / 2 ≤ Real.sqrt (1 - (m : ℝ) * (cubeAmplitude m T) ^ 2) := by
    nlinarith [Real.sqrt_nonneg (1 - (m : ℝ) * (cubeAmplitude m T) ^ 2)]
  have hrate := mul_le_mul_of_nonneg_left (pureRate_le_cube_ratio hm hT)
    (show (0 : ℝ) ≤ 1 / 128 by norm_num)
  calc
    _ ≤ (1 / 128 : ℝ) * (2 * Real.sqrt m / Real.sqrt (max m T : ℕ)) := hrate
    _ = (1 / 2 : ℝ) * (cubeAmplitude m T * Real.sqrt m / 4) := by
      unfold cubeAmplitude
      ring
    _ ≤ Real.sqrt (1 - (m : ℝ) * (cubeAmplitude m T) ^ 2) *
        (cubeAmplitude m T * Real.sqrt m / 4) :=
      mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by ring
end
end TomographyOracleCore.PaperMatch.RankMinimax
