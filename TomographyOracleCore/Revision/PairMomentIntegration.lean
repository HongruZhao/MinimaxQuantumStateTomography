import TomographyOracleCore.Revision.MaximumPairInner
import TomographyOracleCore.Revision.FixedNormMarginalMoments
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.PairMomentIntegration

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance MaximumPairInner FixedNormMarginalMoments
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}

theorem measurable_pair_inner_pow (k : ℕ) :
    Measurable (fun z : E × E => |⟪z.1, z.2⟫_ℝ| ^ k) := by
  have h : Measurable (fun z : E × E => ⟪z.1, z.2⟫_ℝ) := by fun_prop
  simpa only [Real.norm_eq_abs] using h.norm.pow_const k

theorem ae_pair_fixedNorm (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    ∀ᵐ z : E × E ∂mu.prod mu, ‖z.1‖ ^ 2 = q ∧ ‖z.2‖ ^ 2 = q := by
  apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
  filter_upwards [hfixed] with x hx
  filter_upwards [hfixed] with y hy
  exact ⟨hx, hy⟩

theorem integrable_pair_inner_pow (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q) (k : ℕ) :
    Integrable (fun z : E × E => |⟪z.1, z.2⟫_ℝ| ^ k) (mu.prod mu) := by
  apply (integrable_const (q ^ k)).mono' (measurable_pair_inner_pow k).aestronglyMeasurable
  filter_upwards [ae_pair_fixedNorm hfixed] with z hz
  simp only [Real.norm_eq_abs, abs_pow, abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_inner_le_of_fixedNorm hz.1 hz.2) k

theorem integral_pair_inner_sixth_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hL6 : HasL6L2Marginals mu kappa) :
    (∫ z : E × E, |⟪z.1, z.2⟫_ℝ| ^ 6 ∂mu.prod mu) ≤
      kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 := by
  have hg := integrable_pair_inner_pow hfixed hq 6
  rw [integral_prod _ hg]
  calc
    _ ≤ ∫ _x : E, kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 ∂mu := by
      apply integral_mono_ae hg.integral_prod_left (integrable_const _)
      filter_upwards [hfixed] with x hx
      have hm := sixthMoment_le_populationCovariance_norm_mul_sq (fixedNorm_memLp hfixed 2) hL6 x
      have heq : (∫ y : E, |⟪x, y⟫_ℝ| ^ 6 ∂mu) = ∫ y : E, |⟪y, x⟫_ℝ| ^ 6 ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact congrArg (fun z : ℝ => |z| ^ 6) (real_inner_comm _ _)
      rw [heq]
      calc
        _ ≤ kappa ^ 6 * (‖populationCovariance mu‖ * ‖x‖ ^ 2) ^ 3 := hm
        _ = _ := by rw [hx]; ring
    _ = _ := by simp

theorem map_pair_evaluations {ι : Type*} [Fintype ι] (mu : Measure E) [IsProbabilityMeasure mu]
    (i j : ι) (hij : i ≠ j) :
    (Measure.pi (fun _ : ι => mu)).map (fun X : ι → E => (X i, X j)) = mu.prod mu := by
  have hi : iIndepFun (fun i (X : ι → E) => X i) (Measure.pi (fun _ : ι => mu)) := by
    simpa only [id_eq] using (iIndepFun_pi (μ := fun _ : ι => mu) (X := fun _ : ι => id)
      (fun _ => aemeasurable_id))
  have hp := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  rw [(measurePreserving_eval (fun _ : ι => mu) i).map_eq,
    (measurePreserving_eval (fun _ : ι => mu) j).map_eq] at hp
  exact hp

theorem integral_sample_pair_sixth_le {ι : Type*} [Fintype ι]
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hL6 : HasL6L2Marginals mu kappa) (i j : ι) (hij : i ≠ j) :
    (∫ X : ι → E, |⟪X i, X j⟫_ℝ| ^ 6 ∂Measure.pi (fun _ : ι => mu)) ≤
      kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 * q ^ 3 := by
  calc
    _ = ∫ z : E × E, |⟪z.1, z.2⟫_ℝ| ^ 6 ∂mu.prod mu := by
      rw [← map_pair_evaluations mu i j hij]
      exact (integral_map_of_stronglyMeasurable
        (φ := fun X : ι → E => (X i, X j)) (f := fun z : E × E => |⟪z.1, z.2⟫_ℝ| ^ 6)
        (by fun_prop) (measurable_pair_inner_pow 6).stronglyMeasurable).symm
    _ ≤ _ := integral_pair_inner_sixth_le hfixed hq hL6

end
end TomographyOracleCore.Revision.PairMomentIntegration
