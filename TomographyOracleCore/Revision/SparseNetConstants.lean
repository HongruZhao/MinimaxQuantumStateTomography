import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace TomographyOracleCore.Revision.SparseNetConstants

noncomputable section

def sparsifyingFraction : ℝ := 1 / 65536
def netRadius : ℝ := 1 / 4398046511104
def rowThreshold (k M tau g : ℝ) : ℝ :=
  274877906944 * (M / Real.sqrt k + tau) + g / (64 * Real.sqrt k)

theorem rowThreshold_mul_sqrt {k : ℝ} (hk : 0 < k) (M tau g : ℝ) :
    rowThreshold k M tau g * Real.sqrt k =
      274877906944 * M + 274877906944 * tau * Real.sqrt k + g / 64 := by
  have h := (Real.sqrt_pos.mpr hk).ne'
  unfold rowThreshold
  field_simp

theorem rowThreshold_pos {k M tau g : ℝ} (hk : 0 < k) (hM : 0 ≤ M)
    (htau : 0 < tau) (hg : 0 ≤ g) : 0 < rowThreshold k M tau g := by
  unfold rowThreshold
  positivity

theorem rowThreshold_entry_bound {k M tau g : ℝ} (hk : 0 < k) (hM : 0 ≤ M)
    (htau : 0 < tau) (hg : 0 ≤ g) :
    M ≤ sparsifyingFraction * Real.sqrt (sparsifyingFraction * k) *
      rowThreshold k M tau g / 16384 := by
  have heq := rowThreshold_mul_sqrt hk M tau g
  have hs : Real.sqrt (sparsifyingFraction * k) = Real.sqrt k / 256 := by
    rw [Real.sqrt_mul (by norm_num [sparsifyingFraction] : 0 ≤ sparsifyingFraction)]
    norm_num [sparsifyingFraction, Real.sqrt_div]
    ring
  rw [hs]
  dsimp [sparsifyingFraction]
  have ht : 0 ≤ tau * Real.sqrt k := mul_nonneg htau.le (Real.sqrt_nonneg _)
  nlinarith

theorem sqrt_scale_comparison {k r : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hkr : k = 8192 * r) : Real.sqrt k ≤ 128 * Real.sqrt r := by
  have hk2 := Real.sq_sqrt hk.le
  have hr2 := Real.sq_sqrt hr.le
  have hks := Real.sqrt_nonneg k
  have hrs := Real.sqrt_nonneg r
  nlinarith

theorem rowThreshold_separation {k r M tau g : ℝ} (hk : 0 < k) (hr : 0 < r)
    (hkr : k = 8192 * r) (hM : 0 ≤ M) (htau : 0 < tau) (hg : 0 ≤ g) :
    tau + netRadius * g / Real.sqrt r <
      sparsifyingFraction * rowThreshold k M tau g / 8192 := by
  have hks := Real.sqrt_pos.mpr hk
  have hrs := Real.sqrt_pos.mpr hr
  have hcomp := sqrt_scale_comparison hk hr hkr
  have herr : netRadius * g / Real.sqrt r ≤ g / (34359738368 * Real.sqrt k) := by
    apply (div_le_div_iff₀ hrs (by positivity : 0 < 34359738368 * Real.sqrt k)).mpr
    have hm := mul_le_mul_of_nonneg_left hcomp hg
    dsimp [netRadius]
    nlinarith [mul_nonneg hg hrs.le]
  have hstrict : tau + g / (34359738368 * Real.sqrt k) <
      sparsifyingFraction * rowThreshold k M tau g / 8192 := by
    have heq := rowThreshold_mul_sqrt hk M tau g
    have ht : 0 < tau * Real.sqrt k := mul_pos htau hks
    apply (mul_lt_mul_iff_left₀ hks).mp
    have hdiv : g / (34359738368 * Real.sqrt k) * Real.sqrt k = g / 34359738368 := by
      field_simp
    rw [add_mul, hdiv]
    dsimp [sparsifyingFraction]
    nlinarith
  linarith

end
end TomographyOracleCore.Revision.SparseNetConstants
