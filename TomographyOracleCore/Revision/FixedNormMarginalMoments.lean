import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing
import TomographyOracleCore.Revision.IntegralCauchySchwarz

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.FixedNormMarginalMoments

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance IntegralCauchySchwarz
open scoped RealInnerProductSpace InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
    {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}

theorem integrable_abs_inner_pow (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (u : E) (k : ℕ) :
    Integrable (fun x => |⟪x, u⟫_ℝ| ^ k) mu := by
  have h : MemLp (fun x => ⟪x, u⟫_ℝ) k mu :=
    (fixedNorm_memLp hfixed k).inner_const (𝕜 := ℝ) u
  simpa only [Real.norm_eq_abs] using h.integrable_norm_pow'

theorem integrable_inner_pow (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (u : E) (k : ℕ) :
    Integrable (fun x => ⟪x, u⟫_ℝ ^ k) mu := by
  apply (integrable_abs_inner_pow hfixed u k).mono' (by fun_prop)
  filter_upwards [] with x
  simp only [Real.norm_eq_abs, abs_pow, le_refl]

theorem fourthMoment_le_kappa_cubed_second_sq (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa) (u : E) :
    (∫ x, ⟪x, u⟫_ℝ ^ 4 ∂mu) ≤
      kappa ^ 3 * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ^ 2 := by
  have h := integral_mul_sq_le mu (fun x => |⟪x, u⟫_ℝ|) (fun x => |⟪x, u⟫_ℝ| ^ 3)
    (integrable_abs_inner_pow hfixed u 2)
    (by simpa only [← pow_mul] using integrable_abs_inner_pow hfixed u 6)
    (by simpa only [← pow_succ'] using integrable_abs_inner_pow hfixed u 4)
  have habs4 : (fun x : E => |⟪x, u⟫_ℝ| ^ 4) = fun x => ⟪x, u⟫_ℝ ^ 4 := by
    funext x
    exact (Even.pow_abs (by decide : Even 4)) _
  have h6 := hL6 u
  simp only [← pow_succ', ← pow_mul, habs4, sq_abs] at h h6
  have h2n : 0 ≤ ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  have h4n : 0 ≤ ∫ x, ⟪x, u⟫_ℝ ^ 4 ∂mu := integral_nonneg fun _ => by positivity
  have hsq : (∫ x, ⟪x, u⟫_ℝ ^ 4 ∂mu) ^ 2 ≤
      (kappa ^ 3 * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ^ 2) ^ 2 := by
    calc
      _ ≤ (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) * (∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu) := h
      _ ≤ (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) *
          (kappa ^ 6 * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ^ 3) :=
        mul_le_mul_of_nonneg_left h6 h2n
      _ = _ := by ring
  exact (sq_le_sq₀ h4n (mul_nonneg (pow_nonneg hkappa _) (sq_nonneg _))).1 hsq

theorem fourthMoment_le_population_norm (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa) (u : E) :
    (∫ x, ⟪x, u⟫_ℝ ^ 4 ∂mu) ≤ kappa ^ 3 * ‖populationCovariance mu‖ ^ 2 * ‖u‖ ^ 4 := by
  have hsecond := integral_sq_inner_le_populationCovariance_norm_mul_sq (fixedNorm_memLp hfixed 2) u
  have hsecond0 : 0 ≤ ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu := integral_nonneg fun _ => sq_nonneg _
  calc
    _ ≤ kappa ^ 3 * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ^ 2 :=
      fourthMoment_le_kappa_cubed_second_sq hfixed hkappa hL6 u
    _ ≤ kappa ^ 3 * (‖populationCovariance mu‖ * ‖u‖ ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsecond0 hsecond 2) (pow_nonneg hkappa _)
    _ = _ := by ring

end
end TomographyOracleCore.Revision.FixedNormMarginalMoments
