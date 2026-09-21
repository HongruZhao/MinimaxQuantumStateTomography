import TomographyOracleCore.Revision.SparseDyadicEnergy

set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.PeakySelfConsistency

open SparseDyadicEnergy
noncomputable section

/-- Solving the exceedance-count and sparse-energy inequalities gives a
uniform peaky bound. No probabilistic estimate is assumed in this algebraic step. -/
theorem peaky_scalar_bound {N m lambda C B D S : ℝ}
    (hN : 0 < N) (hm : 0 ≤ m) (hlambda : 0 < lambda) (hC : 1 ≤ C)
    (hB : 0 ≤ B) (hD : 0 ≤ D)
    (henergy : S ≤ C * (B + D * Real.sqrt (N * m)))
    (hcount : m ≤ lambda * S) :
    S / N ≤ C ^ 2 * (B + 2 * D * Real.sqrt N * Real.sqrt (lambda * B) + lambda * D ^ 2 * N) / N := by
  have hC0 : 0 ≤ C := by linarith
  have hn := Real.sqrt_nonneg N
  have hm0 := Real.sqrt_nonneg m
  have hr := Real.sqrt_nonneg (lambda * B)
  have hn2 := Real.sq_sqrt hN.le
  have hm2 := Real.sq_sqrt hm
  have hr2 := Real.sq_sqrt (mul_nonneg hlambda.le hB)
  rw [Real.sqrt_mul hN.le] at henergy
  have hself : Real.sqrt m ^ 2 ≤ lambda * C * B +
      (lambda * C * D * Real.sqrt N) * Real.sqrt m := by
    have h := mul_le_mul_of_nonneg_left henergy hlambda.le
    nlinarith
  have hquad := scalar_quadratic_bound hself
  have hcb : 2 * lambda * C * B ≤ 4 * C ^ 2 * (lambda * B) := by
    have hcoeff : 2 * C ≤ 4 * C ^ 2 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hlambda.le hB)
    nlinarith
  have hroot : Real.sqrt m ≤ 2 * C * Real.sqrt (lambda * B) + lambda * C * D * Real.sqrt N := by
    apply (sq_le_sq₀ hm0 (by positivity)).mp
    have hcross : 0 ≤ (2 * C * Real.sqrt (lambda * B)) * (lambda * C * D * Real.sqrt N) := by positivity
    nlinarith
  have hplug := mul_le_mul_of_nonneg_left hroot
    (mul_nonneg (mul_nonneg hC0 hD) hn)
  have hCB : C * B ≤ C ^ 2 * B := by
    have hcoeff : C ≤ C ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right hcoeff hB
  have hex : C * D * Real.sqrt N *
      (2 * C * Real.sqrt (lambda * B) + lambda * C * D * Real.sqrt N) =
      2 * C ^ 2 * D * Real.sqrt N * Real.sqrt (lambda * B) + lambda * C ^ 2 * D ^ 2 * N := by
    calc
      _ = 2 * C ^ 2 * D * Real.sqrt N * Real.sqrt (lambda * B) +
          lambda * C ^ 2 * D ^ 2 * (Real.sqrt N) ^ 2 := by ring
      _ = _ := by rw [hn2]
  rw [hex] at hplug
  apply div_le_div_of_nonneg_right _ hN.le
  nlinarith

end
end TomographyOracleCore.Revision.PeakySelfConsistency
