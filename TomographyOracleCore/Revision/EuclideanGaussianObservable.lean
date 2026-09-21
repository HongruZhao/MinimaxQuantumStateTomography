import TomographyOracleCore.Revision.GaussianClippingSmoothing
import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.EuclideanGaussianObservable

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance GaussianChangeOfMeasure
open GaussianPairPosterior GaussianMarginalMoments
open scoped BigOperators NNReal RealInnerProductSpace InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

def asVector (theta : ι → ℝ) : EuclideanSpace ℝ ι := WithLp.toLp 2 theta
def coordinates (x : EuclideanSpace ℝ ι) : ι → ℝ := fun i => x i
def observable (x : EuclideanSpace ℝ ι) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  pairMarginal (coordinates x) z

@[simp] theorem asVector_coordinates (x : EuclideanSpace ℝ ι) : asVector (coordinates x) = x := rfl
@[simp] theorem coordinates_asVector (x : ι → ℝ) : coordinates (asVector x) = x := rfl

theorem marginal_coordinates_inner (x : EuclideanSpace ℝ ι) (theta : ι → ℝ) :
    marginal (coordinates x) theta = ⟪x, asVector theta⟫_ℝ := by
  simp [marginal, coordinates, asVector, PiLp.inner_apply, mul_comm]

theorem coordinateEnergy (x : EuclideanSpace ℝ ι) : (∑ i, coordinates x i ^ 2) = ‖x‖ ^ 2 :=
  (EuclideanSpace.real_norm_sq_eq x).symm

theorem observable_eq (x : EuclideanSpace ℝ ι) (z : (ι → ℝ) × (ι → ℝ)) :
    observable x z = ⟪x, asVector z.1⟫_ℝ * ⟪x, asVector z.2⟫_ℝ := by
  unfold observable pairMarginal
  rw [marginal_coordinates_inner, marginal_coordinates_inner]

theorem continuous_observable :
    Continuous (fun z : EuclideanSpace ℝ ι × ((ι → ℝ) × (ι → ℝ)) => observable z.1 z.2) := by
  unfold observable pairMarginal marginal coordinates
  fun_prop

theorem integrable_observable_posterior (x : EuclideanSpace ℝ ι) (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (observable x) (gaussianPairLaw m v) := integrable_pairMarginal (coordinates x) m v

theorem integrable_observable_sq_posterior (x : EuclideanSpace ℝ ι) (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z => observable x z ^ 2) (gaussianPairLaw m v) :=
  integrable_pairMarginal_sq (coordinates x) m v

theorem integral_observable_posterior (x : EuclideanSpace ℝ ι) (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, observable x z ∂gaussianPairLaw m v) = ⟪x, asVector m⟫_ℝ ^ 2 := by
  unfold observable
  rw [integral_pairMarginal, marginal_coordinates_inner]

theorem integral_observable_sq_posterior (x : EuclideanSpace ℝ ι) (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, observable x z ^ 2 ∂gaussianPairLaw m v) =
      (⟪x, asVector m⟫_ℝ ^ 2 + (v : ℝ) * ‖x‖ ^ 2) ^ 2 := by
  unfold observable
  rw [integral_pairMarginal_sq, marginal_coordinates_inner, coordinateEnergy]

theorem memLp_observable_two {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (z : (ι → ℝ) × (ι → ℝ)) :
    MemLp (fun x => observable x z) 2 mu := by
  letI : ENNReal.HolderTriple 4 4 2 := ⟨by
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv]⟩
  have h4 := fixedNorm_memLp hfixed 4
  simpa only [observable_eq, Pi.mul_apply, id_eq] using
    ((h4.inner_const (𝕜 := ℝ) (asVector z.2)).mul' (h4.inner_const (𝕜 := ℝ) (asVector z.1)) :
      MemLp (fun x => ⟪x, asVector z.1⟫_ℝ * ⟪x, asVector z.2⟫_ℝ) 2 mu)

theorem integrable_observable_sample {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (z : (ι → ℝ) × (ι → ℝ)) :
    Integrable (fun x => observable x z) mu := (memLp_observable_two hfixed z).integrable (by norm_num)

theorem integrable_observable_sq_sample {mu : Measure (EuclideanSpace ℝ ι)} [IsProbabilityMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (z : (ι → ℝ) × (ι → ℝ)) :
    Integrable (fun x => observable x z ^ 2) mu := (memLp_observable_two hfixed z).integrable_sq

end
end TomographyOracleCore.Revision.EuclideanGaussianObservable
