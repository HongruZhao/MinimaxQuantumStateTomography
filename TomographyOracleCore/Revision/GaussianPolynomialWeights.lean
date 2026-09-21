import TomographyOracleCore.Revision.JointFixedNormGaussianMoments
import TomographyOracleCore.Revision.NormalizedPositiveWeights

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.GaussianPolynomialWeights

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance GaussianChangeOfMeasure
open GaussianPairPosterior EuclideanGaussianObservable JointFixedNormGaussianMoments
open QuadraticLogIntegrability NormalizedPositiveWeights ProductPriorWeights
open scoped BigOperators NNReal InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

def kernel (c lambda : ℝ) (x : EuclideanSpace ℝ ι) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  1 + lambda * observable x z + c * (lambda * observable x z) ^ 2

theorem kernel_lower (c lambda : ℝ) (hc : 1 ≤ c) (x : EuclideanSpace ℝ ι)
    (z : (ι → ℝ) × (ι → ℝ)) : (3 / 4 : ℝ) ≤ kernel c lambda x z :=
  polynomial_lower c (lambda * observable x z) hc

theorem measurable_kernel (c lambda : ℝ) :
    Measurable (fun z : EuclideanSpace ℝ ι × ((ι → ℝ) × (ι → ℝ)) => kernel c lambda z.1 z.2) := by
  exact ((continuous_const.add (continuous_observable.const_mul lambda)).add
    ((continuous_observable.const_mul lambda).pow 2 |>.const_mul c)).measurable

variable {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu] {q : ℝ}

theorem integrable_kernel_sample (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (z : (ι → ℝ) × (ι → ℝ)) : Integrable (fun x => kernel c lambda x z) mu := by
  have h :=
    ((integrable_const (1 : ℝ)).add ((integrable_observable_sample hfixed z).const_mul lambda)).add
      ((integrable_observable_sq_sample hfixed z).const_mul (c * lambda ^ 2))
  apply h.congr
  filter_upwards [] with x
  dsimp [kernel]
  ring

theorem integrable_kernel_joint (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z : EuclideanSpace ℝ ι × ((ι → ℝ) × (ι → ℝ)) => kernel c lambda z.1 z.2)
      (mu.prod (gaussianPairLaw m v)) := by
  have h :=
    ((integrable_const (1 : ℝ)).add ((integrable_observable_joint hfixed m v).const_mul lambda)).add
      ((integrable_observable_sq_joint hfixed m v).const_mul (c * lambda ^ 2))
  apply h.congr
  filter_upwards [] with z
  dsimp [kernel]
  ring

theorem integrable_log_kernel_posterior (c lambda : ℝ) (hc : 1 ≤ c)
    (x : EuclideanSpace ℝ ι) (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z => Real.log (kernel c lambda x z)) (gaussianPairLaw m v) := by
  have hZ := (integrable_observable_posterior x m v).const_mul lambda
  have hZ2 : Integrable (fun z => (lambda * observable x z) ^ 2) (gaussianPairLaw m v) := by
    simpa only [mul_pow] using (integrable_observable_sq_posterior x m v).const_mul (lambda ^ 2)
  exact integrable_quadraticLog _ c hc _ hZ hZ2

theorem normalizer_kernel_eq (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (z : (ι → ℝ) × (ι → ℝ)) :
    normalizer mu (kernel c lambda) z = 1 + lambda * (∫ x, observable x z ∂mu) +
      (c * lambda ^ 2) * (∫ x, observable x z ^ 2 ∂mu) := by
  unfold normalizer kernel
  simp only [mul_pow, ← mul_assoc]
  have hadd := integral_add ((integrable_const (1 : ℝ)).add
    ((integrable_observable_sample hfixed z).const_mul lambda))
    ((integrable_observable_sq_sample hfixed z).const_mul (c * lambda ^ 2))
  simp only [Pi.add_apply] at hadd
  rw [hadd,
    integral_add (integrable_const (1 : ℝ)) ((integrable_observable_sample hfixed z).const_mul lambda),
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul]

theorem integral_normalizer_kernel (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, normalizer mu (kernel c lambda) z ∂gaussianPairLaw m v) =
      1 + lambda * (∫ x, ⟪x, asVector m⟫_ℝ ^ 2 ∂mu) +
        (c * lambda ^ 2) * (∫ z, ∫ x, observable x z ^ 2 ∂mu ∂gaussianPairLaw m v) := by
  have h1 := (integrable_observable_joint hfixed m v).integral_prod_right
  have h2 := (integrable_observable_sq_joint hfixed m v).integral_prod_right
  simp_rw [normalizer_kernel_eq hfixed]
  have hadd := integral_add ((integrable_const (1 : ℝ)).add (h1.const_mul lambda))
    (h2.const_mul (c * lambda ^ 2))
  simp only [Pi.add_apply, Prod.fst, Prod.snd] at hadd
  rw [hadd, integral_add (integrable_const (1 : ℝ)) (h1.const_mul lambda),
    integral_const, probReal_univ, one_smul, integral_const_mul, integral_const_mul,
    double_integral_observable hfixed m v]

theorem integrable_log_kernel_normalizer (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z => Real.log (normalizer mu (kernel c lambda) z)) (gaussianPairLaw m v) :=
  integrable_log_normalizer mu (gaussianPairLaw m v) (kernel c lambda) (measurable_kernel c lambda)
    (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda)
    (integrable_kernel_joint hfixed c lambda m v)

theorem integral_log_kernel_normalizer_le (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa)
    (c lambda : ℝ) (hc : 1 ≤ c) (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, Real.log (normalizer mu (kernel c lambda) z) ∂gaussianPairLaw m v) ≤
      lambda * (∫ x, ⟪x, asVector m⟫_ℝ ^ 2 ∂mu) +
        (c * lambda ^ 2) * (2 * kappa ^ 3 * ‖populationCovariance mu‖ ^ 2 * ‖asVector m‖ ^ 4 +
          2 * (v : ℝ) ^ 2 * q ^ 2) := by
  have h := integral_log_normalizer_le mu (gaussianPairLaw m v) (kernel c lambda)
    (measurable_kernel c lambda) (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda)
    (integrable_kernel_joint hfixed c lambda m v)
  rw [integral_normalizer_kernel hfixed c lambda m v] at h
  have h2 := mul_le_mul_of_nonneg_left (double_integral_observable_sq_le hfixed hkappa hL6 m v)
    (show 0 ≤ c * lambda ^ 2 from mul_nonneg (by linarith) (sq_nonneg _))
  linarith

theorem integrable_log_normalized_kernel_posterior (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (x : EuclideanSpace ℝ ι) (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z => Real.log (normalizedWeight mu (kernel c lambda) x z)) (gaussianPairLaw m v) := by
  have h := (integrable_log_kernel_posterior c lambda hc x m v).sub
    (integrable_log_kernel_normalizer hfixed c lambda hc m v)
  apply h.congr
  filter_upwards [] with z
  exact (log_normalizedWeight mu (kernel c lambda) (kernel_lower c lambda hc)
    (integrable_kernel_sample hfixed c lambda) x z).symm

def commonWeight (mu : Measure (EuclideanSpace ℝ ι)) (c lambda : ℝ) (v : ℝ≥0)
    {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) : ℝ :=
  priorWeight (gaussianPairLaw (fun _ : ι => 0) v)
    (normalizedWeight mu (kernel c lambda)) sample

theorem commonWeight_nonneg (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (v : ℝ≥0) {T : ℕ} (sample : Fin T → EuclideanSpace ℝ ι) :
    0 ≤ commonWeight mu c lambda v sample := by
  apply integral_nonneg
  intro z
  exact (productWeight_pos _ (normalizedWeight_pos mu (kernel c lambda)
    (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda)) sample z).le

theorem integrable_commonWeight (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (v : ℝ≥0) {T : ℕ} :
    Integrable (commonWeight mu c lambda v : (Fin T → EuclideanSpace ℝ ι) → ℝ)
      (Measure.pi (fun _ : Fin T => mu)) :=
  integrable_priorWeight mu (gaussianPairLaw (fun _ : ι => 0) v) _
    (measurable_normalizedWeight mu _ (measurable_kernel c lambda))
    (normalizedWeight_pos mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))
    (integrable_normalizedWeight mu _ (integrable_kernel_sample hfixed c lambda))
    (integral_normalizedWeight mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))

theorem integral_commonWeight (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (v : ℝ≥0) {T : ℕ} :
    (∫ sample : Fin T → EuclideanSpace ℝ ι, commonWeight mu c lambda v sample
      ∂Measure.pi (fun _ : Fin T => mu)) = 1 :=
  integral_priorWeight mu (gaussianPairLaw (fun _ : ι => 0) v) _
    (measurable_normalizedWeight mu _ (measurable_kernel c lambda))
    (normalizedWeight_pos mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))
    (integrable_normalizedWeight mu _ (integrable_kernel_sample hfixed c lambda))
    (integral_normalizedWeight mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))

theorem productWeight_integrable_ae (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (c lambda : ℝ) (hc : 1 ≤ c) (v : ℝ≥0) {T : ℕ} :
    ∀ᵐ sample : Fin T → EuclideanSpace ℝ ι ∂Measure.pi (fun _ : Fin T => mu),
      Integrable (productWeight (normalizedWeight mu (kernel c lambda)) sample)
        (gaussianPairLaw (fun _ : ι => 0) v) :=
  (integrable_productWeight_joint mu (gaussianPairLaw (fun _ : ι => 0) v) _
    (measurable_normalizedWeight mu _ (measurable_kernel c lambda))
    (normalizedWeight_pos mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))
    (integrable_normalizedWeight mu _ (integrable_kernel_sample hfixed c lambda))
    (integral_normalizedWeight mu _ (kernel_lower c lambda hc) (integrable_kernel_sample hfixed c lambda))).prod_right_ae

end
end TomographyOracleCore.Revision.GaussianPolynomialWeights
