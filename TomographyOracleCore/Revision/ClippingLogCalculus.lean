import TomographyOracleCore.Candidate2PeakySpreadDecomposition
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace TomographyOracleCore.Revision.ClippingLogCalculus

open MeasureTheory Real Set
open TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
noncomputable section

def quadratic (x : ℝ) : ℝ := 1 + x + x ^ 2
def logQuadratic (x : ℝ) : ℝ := Real.log (quadratic x)
def convexCorrection (x : ℝ) : ℝ := logQuadratic x + x ^ 2

theorem quadratic_lower (x : ℝ) : (3 / 4 : ℝ) ≤ quadratic x := by
  unfold quadratic
  nlinarith [sq_nonneg (x + 1 / 2)]

theorem quadratic_pos (x : ℝ) : 0 < quadratic x := lt_of_lt_of_le (by norm_num) (quadratic_lower x)

theorem quadratic_hasDerivAt (x : ℝ) :
    HasDerivAt quadratic (1 + 2 * x) x := by
  have h := ((hasDerivAt_id x).const_add 1).add ((hasDerivAt_id x).pow 2)
  convert! h using 1 <;> simp [quadratic, Pi.add_def, Pi.pow_def]

theorem logQuadratic_hasDerivAt (x : ℝ) :
    HasDerivAt logQuadratic ((1 + 2 * x) / quadratic x) x :=
  (quadratic_hasDerivAt x).log (quadratic_pos x).ne'

theorem continuous_logQuadratic : Continuous logQuadratic :=
  continuous_iff_continuousAt.2 fun x => (logQuadratic_hasDerivAt x).continuousAt

theorem logQuadratic_lower (x : ℝ) : -1 ≤ logQuadratic x := by
  have h := Real.one_sub_inv_le_log_of_pos (quadratic_pos x)
  have hi : (quadratic x)⁻¹ ≤ 2 := by
    have h := one_div_le_one_div_of_le (show (0 : ℝ) < 3 / 4 by norm_num) (quadratic_lower x)
    norm_num [one_div] at h
    linarith
  exact (by linarith : -1 ≤ 1 - (quadratic x)⁻¹).trans h

theorem logQuadratic_upper (x : ℝ) : logQuadratic x ≤ x + x ^ 2 := by
  have h := Real.log_le_sub_one_of_pos (quadratic_pos x)
  change logQuadratic x ≤ 1 + x + x ^ 2 - 1 at h
  linarith

theorem logQuadratic_sub_id_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => logQuadratic t - t) (x * (1 - x) / quadratic x) x := by
  apply ((logQuadratic_hasDerivAt x).sub (hasDerivAt_id x)).congr_deriv
  field_simp [(quadratic_pos x).ne']
  unfold quadratic
  ring

theorem self_le_logQuadratic_of_le_one {x : ℝ} (hx : x ≤ 1) : x ≤ logQuadratic x := by
  have hc : Continuous (fun t => logQuadratic t - t) := continuous_logQuadratic.sub continuous_id
  by_cases hx0 : x ≤ 0
  · have ha : AntitoneOn (fun t => logQuadratic t - t) (Set.Iic 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic 0) hc.continuousOn
        (fun t _ => (logQuadratic_sub_id_hasDerivAt t).hasDerivWithinAt)
      intro t ht
      have htI : t ∈ Set.Iic (0 : ℝ) := interior_subset ht
      have ht0 : t ≤ 0 := htI
      exact div_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg ht0 (by linarith)) (quadratic_pos t).le
    have h := ha hx0 (by simp) hx0
    norm_num [logQuadratic, quadratic] at h
    exact h
  · have hm : MonotoneOn (fun t => logQuadratic t - t) (Set.Icc 0 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hc.continuousOn
        (fun t _ => (logQuadratic_sub_id_hasDerivAt t).hasDerivWithinAt)
      intro t ht
      have htI : t ∈ Set.Icc (0 : ℝ) 1 := interior_subset ht
      exact div_nonneg (mul_nonneg htI.1 (by linarith [htI.2])) (quadratic_pos t).le
    have h := hm (by norm_num) ⟨le_of_not_ge hx0, hx⟩ (le_of_not_ge hx0)
    norm_num [logQuadratic, quadratic] at h
    exact h

theorem clippedPsi_le_logQuadratic (x : ℝ) : clippedPsi x ≤ logQuadratic x := by
  unfold clippedPsi
  split_ifs with hxneg hxpos
  · exact logQuadratic_lower x
  · apply (Real.le_log_iff_exp_le (quadratic_pos x)).2
    exact Real.exp_one_lt_three.le.trans (by unfold quadratic; nlinarith)
  · exact self_le_logQuadratic_of_le_one (le_of_not_gt hxpos)

theorem clippedPsi_le_one (x : ℝ) : clippedPsi x ≤ 1 := by
  unfold clippedPsi
  split_ifs <;> linarith

theorem convexCorrection_hasDerivAt (x : ℝ) :
    HasDerivAt convexCorrection ((1 + 2 * x) / quadratic x + 2 * x) x := by
  have h := (logQuadratic_hasDerivAt x).add ((hasDerivAt_id x).pow 2)
  convert! h using 1 <;> simp [convexCorrection, Pi.add_def, Pi.pow_def]

theorem convexCorrection_deriv_hasDerivAt (x : ℝ) :
    HasDerivAt (fun t => (1 + 2 * t) / quadratic t + 2 * t)
      ((2 * quadratic x - (1 + 2 * x) ^ 2) / quadratic x ^ 2 + 2) x := by
  apply (((((hasDerivAt_id x).const_mul 2).const_add 1).div
    (quadratic_hasDerivAt x) (quadratic_pos x).ne').add
      ((hasDerivAt_id x).const_mul 2)).congr_deriv
  dsimp
  ring

theorem convexCorrection_deriv2_nonneg (x : ℝ) :
    0 ≤ (2 * quadratic x - (1 + 2 * x) ^ 2) / quadratic x ^ 2 + 2 := by
  have heq : (2 * quadratic x - (1 + 2 * x) ^ 2) / quadratic x ^ 2 + 2 =
      (2 * (x + 1 / 2) ^ 4 + (x + 1 / 2) ^ 2 + 21 / 8) / quadratic x ^ 2 := by
    field_simp [(quadratic_pos x).ne']
    unfold quadratic
    ring
  rw [heq]
  positivity

theorem convexOn_convexCorrection : ConvexOn ℝ Set.univ convexCorrection := by
  apply convexOn_of_hasDerivWithinAt2_nonneg convex_univ
    (continuous_iff_continuousAt.2 (fun x => (convexCorrection_hasDerivAt x).continuousAt)).continuousOn
    (fun x _ => (convexCorrection_hasDerivAt x).hasDerivWithinAt)
    (fun x _ => (convexCorrection_deriv_hasDerivAt x).hasDerivWithinAt)
  intro x _
  exact convexCorrection_deriv2_nonneg x

end
end TomographyOracleCore.Revision.ClippingLogCalculus
