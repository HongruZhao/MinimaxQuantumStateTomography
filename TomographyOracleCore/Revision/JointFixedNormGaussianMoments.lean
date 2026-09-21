import TomographyOracleCore.Revision.EuclideanGaussianObservable
import TomographyOracleCore.Revision.FixedNormMarginalMoments

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.JointFixedNormGaussianMoments

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance GaussianChangeOfMeasure
open GaussianPairPosterior EuclideanGaussianObservable FixedNormMarginalMoments
open scoped BigOperators NNReal InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]
    {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu] {q : ℝ}

theorem integrable_posterior_second_formula (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun x => (⟪x, asVector m⟫_ℝ ^ 2 + (v : ℝ) * ‖x‖ ^ 2) ^ 2) mu := by
  have hi : Integrable (fun x => ⟪x, asVector m⟫_ℝ ^ 4 +
      (2 * (v : ℝ) * q) * ⟪x, asVector m⟫_ℝ ^ 2 + (v : ℝ) ^ 2 * q ^ 2) mu :=
    ((integrable_inner_pow hfixed (asVector m) 4).add
      ((integrable_inner_pow hfixed (asVector m) 2).const_mul _)).add (integrable_const _)
  apply hi.congr
  filter_upwards [hfixed] with x hx
  rw [hx]
  ring

theorem integrable_observable_sq_joint (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z : EuclideanSpace ℝ ι × ((ι → ℝ) × (ι → ℝ)) => observable z.1 z.2 ^ 2)
      (mu.prod (gaussianPairLaw m v)) := by
  apply (integrable_prod_iff (continuous_observable.pow 2).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ fun x => integrable_observable_sq_posterior x m v
  · have heq : (fun x : EuclideanSpace ℝ ι => ∫ z, ‖observable x z ^ 2‖ ∂gaussianPairLaw m v) =
        fun x => (⟪x, asVector m⟫_ℝ ^ 2 + (v : ℝ) * ‖x‖ ^ 2) ^ 2 := by
      funext x
      simp only [Real.norm_eq_abs, abs_pow, sq_abs]
      exact integral_observable_sq_posterior x m v
    simp only [Pi.pow_apply]
    rw [heq]
    exact integrable_posterior_second_formula hfixed m v

theorem integrable_observable_joint (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z : EuclideanSpace ℝ ι × ((ι → ℝ) × (ι → ℝ)) => observable z.1 z.2)
      (mu.prod (gaussianPairLaw m v)) := by
  apply ((integrable_const (1 : ℝ)).add (integrable_observable_sq_joint hfixed m v)).mono'
    continuous_observable.aestronglyMeasurable
  filter_upwards [] with z
  simp only [Pi.add_apply, Real.norm_eq_abs]
  have h := sq_nonneg (|observable z.1 z.2| - 1)
  nlinarith [abs_nonneg (observable z.1 z.2), sq_abs (observable z.1 z.2)]

theorem double_integral_observable (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, ∫ x, observable x z ∂mu ∂gaussianPairLaw m v) =
      ∫ x, ⟪x, asVector m⟫_ℝ ^ 2 ∂mu := by
  rw [integral_integral_swap (f := fun z x => observable x z)
    (integrable_observable_joint hfixed m v).swap]
  simp_rw [integral_observable_posterior]

theorem double_integral_observable_sq (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, ∫ x, observable x z ^ 2 ∂mu ∂gaussianPairLaw m v) =
      ∫ x, (⟪x, asVector m⟫_ℝ ^ 2 + (v : ℝ) * q) ^ 2 ∂mu := by
  rw [integral_integral_swap (f := fun z x => observable x z ^ 2)
    (integrable_observable_sq_joint hfixed m v).swap]
  simp_rw [integral_observable_sq_posterior]
  apply integral_congr_ae
  filter_upwards [hfixed] with x hx
  rw [hx]

theorem double_integral_observable_sq_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, ∫ x, observable x z ^ 2 ∂mu ∂gaussianPairLaw m v) ≤
      2 * kappa ^ 3 * ‖populationCovariance mu‖ ^ 2 * ‖asVector m‖ ^ 4 +
        2 * (v : ℝ) ^ 2 * q ^ 2 := by
  rw [double_integral_observable_sq hfixed m v]
  have hi := integrable_posterior_second_formula hfixed m v
  have hi' : Integrable (fun x => (⟪x, asVector m⟫_ℝ ^ 2 + (v : ℝ) * q) ^ 2) mu := by
    apply hi.congr
    filter_upwards [hfixed] with x hx
    rw [hx]
  have hupper : Integrable (fun x => 2 * ⟪x, asVector m⟫_ℝ ^ 4 + 2 * (v : ℝ) ^ 2 * q ^ 2) mu :=
    ((integrable_inner_pow hfixed (asVector m) 4).const_mul 2).add (integrable_const _)
  have hmono := integral_mono hi' hupper (fun x => by
    nlinarith [sq_nonneg (⟪x, asVector m⟫_ℝ ^ 2 - (v : ℝ) * q)])
  rw [integral_add ((integrable_inner_pow hfixed (asVector m) 4).const_mul 2) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at hmono
  have hfourth := fourthMoment_le_population_norm hfixed hkappa hL6 (asVector m)
  linarith

end
end TomographyOracleCore.Revision.JointFixedNormGaussianMoments
