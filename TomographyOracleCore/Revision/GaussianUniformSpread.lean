import TomographyOracleCore.Revision.GaussianPolynomialWeights

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.GaussianUniformSpread

open MeasureTheory ProbabilityTheory InformationTheory PeriodicForwardCovariance
open GaussianChangeOfMeasure GaussianPairPosterior EuclideanGaussianObservable
open GaussianPolynomialWeights GaussianClippingSmoothing GaussianMarginalMoments
open ClippingLogSmoothing QuadraticLogIntegrability NormalizedPositiveWeights ProductPriorWeights
open TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
open scoped BigOperators NNReal InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]
    {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu] {q : ℝ}

def spreadC : ℝ := smoothingCoefficient 16
theorem spreadC_ge_one : 1 ≤ spreadC := smoothingCoefficient_ge_one (by norm_num)

theorem posterior_kernel_sum_bound (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι)
    (hWeight : Integrable (productWeight (normalizedWeight mu (kernel c lambda)) sample)
      (gaussianPairLaw (fun _ : ι => 0) v)) :
    (∑ i, ∫ z, Real.log (kernel c lambda (sample i) z) ∂gaussianPairLaw m v) ≤
      ‖asVector m‖ ^ 2 / (v : ℝ) + commonWeight mu c lambda v sample +
        (T : ℝ) * (∫ z, Real.log (normalizer mu (kernel c lambda) z) ∂gaussianPairLaw m v) := by
  have hpost := posterior_logWeight_le (gaussianPairLaw (fun _ : ι => 0) v)
    (normalizedWeight mu (kernel c lambda))
    (normalizedWeight_pos mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))
    sample (gaussianPairLaw m v) (gaussianPair_kl_finite m v hv)
    (fun i => integrable_log_normalized_kernel_posterior hfixed c lambda hc (sample i) m v) hWeight
  have heq (i : Fin T) :
      (∫ z, Real.log (normalizedWeight mu (kernel c lambda) (sample i) z) ∂gaussianPairLaw m v) =
      (∫ z, Real.log (kernel c lambda (sample i) z) ∂gaussianPairLaw m v) -
        (∫ z, Real.log (normalizer mu (kernel c lambda) z) ∂gaussianPairLaw m v) := by
    simp_rw [log_normalizedWeight mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda)]
    exact integral_sub (integrable_log_kernel_posterior c lambda hc (sample i) m v)
      (integrable_log_kernel_normalizer hfixed c lambda hc m v)
  simp only [heq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, gaussianPair_kl m v hv] at hpost
  have hnorm : (∑ i, m i ^ 2) = ‖asVector m‖ ^ 2 := by
    simpa using coordinateEnergy (asVector m)
  rw [hnorm] at hpost
  change _ ≤ ‖asVector m‖ ^ 2 / (v : ℝ) + commonWeight mu c lambda v sample at hpost
  linarith

theorem sum_clipping_smoothing {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι)
    (hfixed : ∀ i, ‖sample i‖ ^ 2 = q) (m : ι → ℝ) (v : ℝ≥0) (lambda : ℝ) :
    (∑ i, clippedPsi (lambda * ⟪sample i, asVector m⟫_ℝ ^ 2)) ≤
      (∑ i, ∫ z, Real.log (kernel spreadC lambda (sample i) z) ∂gaussianPairLaw m v) +
        (T : ℝ) * (4 * lambda ^ 2 * (v : ℝ) ^ 2 * q ^ 2) := by
  have hi (i : Fin T) := gaussian_clipping_smoothing (coordinates (sample i)) m v lambda
  have hib (i : Fin T) : clippedPsi (lambda * ⟪sample i, asVector m⟫_ℝ ^ 2) ≤
      (∫ z, Real.log (kernel spreadC lambda (sample i) z) ∂gaussianPairLaw m v) +
        4 * lambda ^ 2 * (v : ℝ) ^ 2 * q ^ 2 := by
    have h := hi i
    rw [marginal_coordinates_inner, coordinateEnergy, hfixed i] at h
    exact h
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hib i)
  simpa only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] using h

def spreadVarianceBound (kappa s q : ℝ) (v : ℝ≥0) : ℝ :=
  2 * spreadC * kappa ^ 3 * s ^ 2 + (2 * spreadC + 4) * (v : ℝ) ^ 2 * q ^ 2

theorem sum_clipped_centered_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (lambda : ℝ) (v : ℝ≥0) (hv : 0 < (v : ℝ))
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) (hsample : ∀ i, ‖sample i‖ ^ 2 = q)
    (hWeight : Integrable (productWeight (normalizedWeight mu (kernel spreadC lambda)) sample)
      (gaussianPairLaw (fun _ : ι => 0) v))
    (m : ι → ℝ) (hm : ‖asVector m‖ ≤ 1) :
    (∑ i, clippedPsi (lambda * ⟪sample i, asVector m⟫_ℝ ^ 2)) -
        lambda * (T : ℝ) * (∫ x, ⟪x, asVector m⟫_ℝ ^ 2 ∂mu) ≤
      (v : ℝ)⁻¹ + commonWeight mu spreadC lambda v sample +
        lambda ^ 2 * (T : ℝ) * spreadVarianceBound kappa ‖populationCovariance mu‖ q v := by
  have hv' : v ≠ 0 := by exact_mod_cast hv.ne'
  have hpost := posterior_kernel_sum_bound hfixed spreadC lambda spreadC_ge_one m v hv' sample hWeight
  have hsm := sum_clipping_smoothing sample hsample m v lambda
  have hmean := integral_log_kernel_normalizer_le hfixed hkappa hL6 spreadC lambda spreadC_ge_one m v
  have hm2 : ‖asVector m‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (asVector m)]
  have hm4 : ‖asVector m‖ ^ 4 ≤ 1 := by simpa using pow_le_pow_left₀ (norm_nonneg _) hm 4
  have hkl : ‖asVector m‖ ^ 2 / (v : ℝ) ≤ (v : ℝ)⁻¹ := by
    simpa only [one_div] using div_le_div_of_nonneg_right hm2 hv.le
  have hc0 : 0 ≤ spreadC := le_trans (by norm_num) spreadC_ge_one
  have h4bound := mul_le_mul_of_nonneg_left hm4
    (show 0 ≤ 2 * kappa ^ 3 * ‖populationCovariance mu‖ ^ 2 by positivity)
  have hmeanUnit : (∫ z, Real.log (normalizer mu (kernel spreadC lambda) z) ∂gaussianPairLaw m v) ≤
      lambda * (∫ x, ⟪x, asVector m⟫_ℝ ^ 2 ∂mu) +
      (spreadC * lambda ^ 2) * (2 * kappa ^ 3 * ‖populationCovariance mu‖ ^ 2 +
        2 * (v : ℝ) ^ 2 * q ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left h4bound (mul_nonneg hc0 (sq_nonneg lambda))
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hmeanUnit (Nat.cast_nonneg T)
  unfold spreadVarianceBound
  nlinarith

theorem clippedPsi_neg (x : ℝ) : clippedPsi (-x) = -clippedPsi x := by
  unfold clippedPsi
  split_ifs <;> linarith

end
end TomographyOracleCore.Revision.GaussianUniformSpread
