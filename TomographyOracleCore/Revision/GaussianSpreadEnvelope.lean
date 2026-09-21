import TomographyOracleCore.Revision.GaussianUniformSpread
import TomographyOracleCore.Revision.FixedNormCovarianceBounds

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.GaussianSpreadEnvelope

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance GaussianChangeOfMeasure
open GaussianPairPosterior EuclideanGaussianObservable GaussianPolynomialWeights GaussianUniformSpread
open NormalizedPositiveWeights ProductPriorWeights FixedNormCovarianceBounds
open TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
open scoped BigOperators NNReal InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

def spreadEnvelope (mu : Measure (EuclideanSpace ℝ ι)) (kappa q lambda : ℝ) (v : ℝ≥0)
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) : ℝ :=
  (v : ℝ)⁻¹ + commonWeight mu spreadC lambda v sample + commonWeight mu spreadC (-lambda) v sample +
    lambda ^ 2 * (T : ℝ) * spreadVarianceBound kappa ‖populationCovariance mu‖ q v

variable {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu] {q : ℝ}

theorem spreadVarianceBound_nonneg {kappa : ℝ} (hkappa : 0 ≤ kappa) (s q : ℝ) (v : ℝ≥0) :
    0 ≤ spreadVarianceBound kappa s q v := by
  have hc0 : 0 ≤ spreadC := le_trans (by norm_num) spreadC_ge_one
  unfold spreadVarianceBound
  positivity

theorem spreadEnvelope_nonneg (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (lambda : ℝ) (v : ℝ≥0)
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) : 0 ≤ spreadEnvelope mu kappa q lambda v sample := by
  have hp := commonWeight_nonneg hfixed spreadC lambda spreadC_ge_one v sample
  have hn := commonWeight_nonneg hfixed spreadC (-lambda) spreadC_ge_one v sample
  have hb := spreadVarianceBound_nonneg hkappa ‖populationCovariance mu‖ q v
  unfold spreadEnvelope
  positivity

theorem integrable_spreadEnvelope (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (kappa lambda : ℝ) (v : ℝ≥0) {T : ℕ} :
    Integrable (spreadEnvelope mu kappa q lambda v : (Fin T → EuclideanSpace ℝ ι) → ℝ)
      (Measure.pi (fun _ : Fin T => mu)) := by
  have hp := integrable_commonWeight hfixed spreadC lambda spreadC_ge_one v (T := T)
  have hn := integrable_commonWeight hfixed spreadC (-lambda) spreadC_ge_one v (T := T)
  exact (((integrable_const ((v : ℝ)⁻¹)).add hp).add hn).add (integrable_const _)

theorem integral_spreadEnvelope (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (kappa lambda : ℝ) (v : ℝ≥0) {T : ℕ} :
    (∫ sample : Fin T → EuclideanSpace ℝ ι, spreadEnvelope mu kappa q lambda v sample
      ∂Measure.pi (fun _ : Fin T => mu)) =
      (v : ℝ)⁻¹ + 2 + lambda ^ 2 * (T : ℝ) * spreadVarianceBound kappa ‖populationCovariance mu‖ q v := by
  have hp := integrable_commonWeight hfixed spreadC lambda spreadC_ge_one v (T := T)
  have hn := integrable_commonWeight hfixed spreadC (-lambda) spreadC_ge_one v (T := T)
  have h1 : Integrable (fun sample : Fin T → EuclideanSpace ℝ ι =>
      (v : ℝ)⁻¹ + commonWeight mu spreadC lambda v sample) (Measure.pi (fun _ : Fin T => mu)) :=
    (integrable_const _).add hp
  have h2 : Integrable (fun sample : Fin T → EuclideanSpace ℝ ι =>
      (v : ℝ)⁻¹ + commonWeight mu spreadC lambda v sample + commonWeight mu spreadC (-lambda) v sample)
      (Measure.pi (fun _ : Fin T => mu)) := h1.add hn
  unfold spreadEnvelope
  rw [integral_add h2 (integrable_const _), integral_add h1 hn, integral_add (integrable_const _) hp,
    integral_commonWeight hfixed spreadC lambda spreadC_ge_one v,
    integral_commonWeight hfixed spreadC (-lambda) spreadC_ge_one v, integral_const, integral_const,
    probReal_univ, one_smul]
  ring

theorem abs_centered_clipped_le_envelope (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (lambda : ℝ) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) (hsample : ∀ i, ‖sample i‖ ^ 2 = q)
    (hplus : Integrable (productWeight (normalizedWeight mu (kernel spreadC lambda)) sample)
      (gaussianPairLaw (fun _ : ι => 0) v))
    (hminus : Integrable (productWeight (normalizedWeight mu (kernel spreadC (-lambda))) sample)
      (gaussianPairLaw (fun _ : ι => 0) v))
    (u : EuclideanSpace ℝ ι) (hu : ‖u‖ ≤ 1) :
    |(∑ i, clippedPsi (lambda * ⟪sample i, u⟫_ℝ ^ 2)) -
      lambda * (T : ℝ) * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu)| ≤ spreadEnvelope mu kappa q lambda v sample := by
  have hp := sum_clipped_centered_le hfixed hkappa hL6 lambda v hv sample hsample hplus (coordinates u) hu
  have hn := sum_clipped_centered_le hfixed hkappa hL6 (-lambda) v hv sample hsample hminus (coordinates u) hu
  simp only [asVector_coordinates, neg_mul, clippedPsi_neg, Finset.sum_neg_distrib, neg_sq] at hp hn
  have hWp := commonWeight_nonneg hfixed spreadC lambda spreadC_ge_one v sample
  have hWn := commonWeight_nonneg hfixed spreadC (-lambda) spreadC_ge_one v sample
  unfold spreadEnvelope
  exact abs_le.2 ⟨by linarith, by linarith⟩

/-- The bound holds simultaneously for every direction in the unit ball on
one measurable full-probability event. -/
theorem ae_all_directions_clipped_bound (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (lambda : ℝ) (v : ℝ≥0) (hv : 0 < (v : ℝ)) {T : ℕ} :
    ∀ᵐ sample : Fin T → EuclideanSpace ℝ ι ∂Measure.pi (fun _ : Fin T => mu),
      ∀ u : EuclideanSpace ℝ ι, ‖u‖ ≤ 1 →
      |(∑ i, clippedPsi (lambda * ⟪sample i, u⟫_ℝ ^ 2)) -
        lambda * (T : ℝ) * (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu)| ≤ spreadEnvelope mu kappa q lambda v sample := by
  have hcoords : ∀ i : Fin T, ∀ᵐ sample ∂Measure.pi (fun _ : Fin T => mu), ‖sample i‖ ^ 2 = q := by
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin T => mu) (i := i)).eventually hfixed
  filter_upwards [Filter.eventually_all.mpr hcoords,
    productWeight_integrable_ae hfixed spreadC lambda spreadC_ge_one v (T := T),
    productWeight_integrable_ae hfixed spreadC (-lambda) spreadC_ge_one v (T := T)] with sample hsample hp hn
  intro u hu
  exact abs_centered_clipped_le_envelope hfixed hkappa hL6 lambda v hv sample hsample hp hn u hu

end
end TomographyOracleCore.Revision.GaussianSpreadEnvelope
