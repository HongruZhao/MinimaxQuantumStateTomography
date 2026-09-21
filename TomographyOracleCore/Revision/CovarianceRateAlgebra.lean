import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option maxHeartbeats 2400000

namespace TomographyOracleCore.Revision.CovarianceRateAlgebra

noncomputable section

def varianceRate (s q N : ℝ) : ℝ := Real.sqrt (s * q / N)
def clippingParameter (s q N : ℝ) : ℝ := varianceRate s q N / s ^ 2

theorem varianceRate_nonneg (s q N : ℝ) : 0 ≤ varianceRate s q N := Real.sqrt_nonneg _
theorem varianceRate_pos {s q N : ℝ} (hs : 0 < s) (hq : 0 < q) (hN : 0 < N) :
    0 < varianceRate s q N := Real.sqrt_pos.mpr (by positivity)
theorem clippingParameter_pos {s q N : ℝ} (hs : 0 < s) (hq : 0 < q) (hN : 0 < N) :
    0 < clippingParameter s q N := div_pos (varianceRate_pos hs hq hN) (sq_pos_of_pos hs)
theorem varianceRate_sq {s q N : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hN : 0 ≤ N) :
    varianceRate s q N ^ 2 = s * q / N := Real.sq_sqrt (by positivity)
theorem varianceRate_sq_mul {s q N : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hN : 0 < N) :
    varianceRate s q N ^ 2 * N = s * q := by
  rw [varianceRate_sq hs hq hN.le, div_mul_cancel₀ _ hN.ne']
theorem clippingParameter_mul_sq {s q N : ℝ} (hs : 0 < s) :
    clippingParameter s q N * s ^ 2 = varianceRate s q N := by
  exact div_mul_cancel₀ _ (pow_ne_zero 2 hs.ne')
theorem totalRate_sq {s q N : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hN : 0 < N) :
    (N * varianceRate s q N) ^ 2 = N * s * q := by
  have h := varianceRate_sq_mul hs hq hN
  calc
    _ = N * (varianceRate s q N ^ 2 * N) := by ring
    _ = _ := by rw [h]; ring
theorem sqrt_total_eq {s q N : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hN : 0 < N) :
    Real.sqrt (s * q * N) = N * varianceRate s q N := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hN.le (varianceRate_nonneg _ _ _))).mp
  rw [Real.sq_sqrt (by positivity), totalRate_sq hs hq hN]
  ring
theorem q_le_totalRate {s q N : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hN : 0 < N)
    (hregime : q ≤ N * s) : q ≤ N * varianceRate s q N := by
  apply (sq_le_sq₀ hq (mul_nonneg hN.le (varianceRate_nonneg _ _ _))).mp
  rw [totalRate_sq hs hq hN]
  nlinarith [mul_le_mul_of_nonneg_right hregime hq]
theorem exceptional_rate_le {s q N : ℝ} (hs : 0 ≤ s) (hq : 0 ≤ q) (hN : 1 ≤ N)
    (hregime : q ≤ N * s) : q / N ^ 3 ≤ varianceRate s q N := by
  have hNpos : 0 < N := by linarith
  have hqT := q_le_totalRate hs hq hNpos hregime
  have hN3 : N ≤ N ^ 3 := by simpa using pow_le_pow_right₀ hN (by decide : 1 ≤ 3)
  apply (div_le_iff₀ (pow_pos hNpos 3)).mpr
  exact hqT.trans (by nlinarith [mul_le_mul_of_nonneg_right hN3 (varianceRate_nonneg s q N)])
theorem rank_over_clipping_samples {s q N : ℝ} (hs : 0 < s) (hq : 0 < q) (hN : 0 < N) :
    (q / s) / (clippingParameter s q N * N) = varianceRate s q N := by
  have ht := varianceRate_pos hs hq hN
  have heq := varianceRate_sq_mul hs.le hq.le hN
  unfold clippingParameter
  field_simp
  nlinarith
theorem varianceRate_eq_effectiveRank {s q N : ℝ} (hs : 0 < s) (hq : 0 ≤ q) (hN : 0 ≤ N) :
    varianceRate s q N = s * Real.sqrt ((q / s) / N) := by
  apply (sq_eq_sq₀ (varianceRate_nonneg _ _ _) (mul_nonneg hs.le (Real.sqrt_nonneg _))).mp
  rw [varianceRate_sq hs.le hq hN, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp

/-- Pure scalar control of the mixed square-root term in the expected peaky
envelope. The root expectation is used through its elementary second-moment
bound, with no fractional moment inequalities left as assumptions. -/
theorem peaky_mixed_bound {N s kappa lambda t b v : ℝ}
    (hN : 0 < N) (hs : 0 ≤ s) (hkappa : 1 ≤ kappa) (hlambda : 0 ≤ lambda)
    (ht : 0 ≤ t) (hv : 0 ≤ v) (hscale : lambda * s ^ 2 = t)
    (hb : b ≤ 3 * kappa * N * t) (hv2 : v ^ 2 ≤ lambda * b) :
    kappa ^ 2 * s * Real.sqrt N * v ≤ 2 * kappa ^ 3 * N * t := by
  have hk0 : 0 ≤ kappa := by linarith
  have hroot := Real.sq_sqrt hN.le
  have hm1 := mul_le_mul_of_nonneg_left hv2 (show 0 ≤ kappa ^ 4 * s ^ 2 * N by positivity)
  have hm2 := mul_le_mul_of_nonneg_left hb (show 0 ≤ kappa ^ 4 * s ^ 2 * N * lambda by positivity)
  have hleft : (kappa ^ 2 * s * Real.sqrt N * v) ^ 2 = kappa ^ 4 * s ^ 2 * N * v ^ 2 := by
    calc
      _ = kappa ^ 4 * s ^ 2 * (Real.sqrt N) ^ 2 * v ^ 2 := by ring
      _ = _ := by rw [hroot]
  have hscale2 : kappa ^ 4 * s ^ 2 * N * lambda * (3 * kappa * N * t) =
      3 * kappa ^ 5 * N ^ 2 * t ^ 2 := by
    calc
      _ = 3 * kappa ^ 5 * N ^ 2 * t * (lambda * s ^ 2) := by ring
      _ = _ := by rw [hscale]; ring
  have hk56 : kappa ^ 5 ≤ kappa ^ 6 := pow_le_pow_right₀ hkappa (by decide)
  have hp := mul_le_mul_of_nonneg_right hk56 (show 0 ≤ 3 * N ^ 2 * t ^ 2 by positivity)
  have hn : 0 ≤ kappa ^ 6 * N ^ 2 * t ^ 2 := by positivity
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  rw [hleft]
  nlinarith

theorem peaky_numerator_bound {N s kappa lambda t b v : ℝ}
    (hN : 0 < N) (hs : 0 ≤ s) (hkappa : 1 ≤ kappa) (hlambda : 0 ≤ lambda)
    (ht : 0 ≤ t) (hv : 0 ≤ v) (hscale : lambda * s ^ 2 = t)
    (hb : b ≤ 3 * kappa * N * t) (hv2 : v ^ 2 ≤ lambda * b) :
    b + 2 * (kappa ^ 2 * s) * Real.sqrt N * v + lambda * (kappa ^ 2 * s) ^ 2 * N ≤
      8 * kappa ^ 4 * N * t := by
  have hmix := peaky_mixed_bound hN hs hkappa hlambda ht hv hscale hb hv2
  have hk14 : kappa ≤ kappa ^ 4 := by simpa using pow_le_pow_right₀ hkappa (by decide : 1 ≤ 4)
  have hk34 : kappa ^ 3 ≤ kappa ^ 4 := pow_le_pow_right₀ hkappa (by decide)
  have hb' := mul_le_mul_of_nonneg_right hk14 (show 0 ≤ 3 * N * t by positivity)
  have hm' := mul_le_mul_of_nonneg_right hk34 (show 0 ≤ 4 * N * t by positivity)
  have heq : lambda * (kappa ^ 2 * s) ^ 2 * N = kappa ^ 4 * N * t := by
    calc
      _ = kappa ^ 4 * N * (lambda * s ^ 2) := by ring
      _ = _ := by rw [hscale]
  rw [heq]
  nlinarith

end
end TomographyOracleCore.Revision.CovarianceRateAlgebra
