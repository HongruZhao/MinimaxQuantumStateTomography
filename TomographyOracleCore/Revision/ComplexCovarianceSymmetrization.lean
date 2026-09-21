import TomographyOracleCore.Revision.CovarianceIsometryTransport
import TomographyOracleCore.Candidate2PhaseRandomization

namespace TomographyOracleCore.Revision.ComplexCovarianceSymmetrization

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance CovarianceIsometryTransport
open Candidate2PhaseRandomization InnerProductSpace
open scoped BigOperators InnerProductSpace RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

local instance : InnerProductSpace ℝ E := InnerProductSpace.complexToReal

def quarterTurn : E ≃ₗᵢ[ℝ] E where
  toFun x := Complex.I • x
  invFun x := -Complex.I • x
  left_inv x := by simp [smul_smul]
  right_inv x := by simp [smul_smul]
  map_add' x y := smul_add _ _ _
  map_smul' c x := by simp only [RingHom.id_apply, smul_comm c Complex.I x]
  norm_map' x := by simp [norm_smul]

def symmetrize : (E →L[ℝ] E) →ₗ[ℝ] (E →L[ℝ] E) :=
  LinearMap.id + quarterTurn.conjStarAlgEquiv.toAlgEquiv.toLinearMap

theorem symmetrize_apply (A : E →L[ℝ] E) :
    symmetrize A = A + quarterTurn.conjStarAlgEquiv A := rfl

theorem norm_symmetrize_le (A : E →L[ℝ] E) : ‖symmetrize A‖ ≤ 2 * ‖A‖ := by
  rw [symmetrize_apply]
  exact (norm_add_le _ _).trans_eq (by rw [norm_conjugate]; ring)

def symmetrizeCLM : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  symmetrize.mkContinuous 2 norm_symmetrize_le

def complexRankOne (x : E) : E →L[ℂ] E := InnerProductSpace.rankOne ℂ x x

theorem complexRankOne_restrict (x : E) :
    (complexRankOne x).restrictScalars ℝ = symmetrize (rankOneCovariance x) := by
  rw [symmetrize_apply, ← rankOneCovariance_map]
  ext u
  change ⟪x, u⟫_ℂ • x = ⟪x, u⟫_ℝ • x + ⟪Complex.I • x, u⟫_ℝ • (Complex.I • x)
  rw [real_inner_eq_re_inner, real_inner_I_smul_left]
  conv_lhs => rw [← Complex.re_add_im ⟪x, u⟫_ℂ]
  module

def complexSampleCovariance {T : ℕ} (X : Fin T → E) : E →L[ℂ] E :=
  (T : ℝ)⁻¹ • ∑ i, complexRankOne (X i)

theorem complexSampleCovariance_restrict {T : ℕ} (X : Fin T → E) :
    (complexSampleCovariance X).restrictScalars ℝ = symmetrize (sampleCovariance X) := by
  let R := ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ
  change R (complexSampleCovariance X) = _
  simp only [complexSampleCovariance, sampleCovariance, map_smul, map_sum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro i _
  exact complexRankOne_restrict (X i)

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℂ E] [SecondCountableTopology E]

theorem integrable_real_rankOne_of_fixedNorm {mu : Measure E} [IsFiniteMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) : Integrable (rankOneCovariance (E := E)) mu := by
  apply (integrable_const q).mono' continuous_rankOneCovariance.aestronglyMeasurable
  filter_upwards [hfixed] with x hx
  rw [norm_rankOneCovariance, hx]

theorem populationCovariance_eq_integral_rankOne {mu : Measure E} [IsFiniteMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    populationCovariance mu = ∫ x, rankOneCovariance x ∂mu := by
  ext u
  rw [ContinuousLinearMap.integral_apply (integrable_real_rankOne_of_fixedNorm hfixed),
    covarianceOperator_apply (fixedNorm_memLp hfixed 2)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rankOneCovariance_apply, real_inner_comm]

theorem continuous_complexRankOne : Continuous (complexRankOne (E := E)) := by
  have hdual : Continuous fun x : E => InnerProductSpace.toDualMap ℂ E x :=
    (InnerProductSpace.toDualMap ℂ E).continuous
  have hpair : Continuous fun x : E =>
      ContinuousLinearMap.smulRight (InnerProductSpace.toDualMap ℂ E x) x :=
    isBoundedBilinearMap_smulRight.continuous.comp (hdual.prodMk continuous_id)
  convert hpair using 1
  funext x
  rw [complexRankOne, InnerProductSpace.rankOne_def]
  rfl

theorem integrable_complex_rankOne_of_fixedNorm {mu : Measure E} [IsFiniteMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) : Integrable (complexRankOne (E := E)) mu := by
  apply (integrable_const q).mono' continuous_complexRankOne.aestronglyMeasurable
  filter_upwards [hfixed] with x hx
  simp only [complexRankOne, InnerProductSpace.norm_rankOne, ← pow_two, hx, le_refl]

def complexPopulationCovariance (mu : Measure E) : E →L[ℂ] E := ∫ x, complexRankOne x ∂mu

theorem complexPopulationCovariance_restrict {mu : Measure E} [IsFiniteMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    (complexPopulationCovariance mu).restrictScalars ℝ = symmetrize (populationCovariance mu) := by
  let R := ContinuousLinearMap.restrictScalarsIsometry ℂ E E ℝ ℝ
  change R (∫ x, complexRankOne x ∂mu) = _
  rw [← R.integral_comp_comm]
  simp_rw [show ∀ x : E, R (complexRankOne x) = symmetrizeCLM (rankOneCovariance x)
    from complexRankOne_restrict]
  rw [symmetrizeCLM.integral_comp_comm (integrable_real_rankOne_of_fixedNorm hfixed),
    ← populationCovariance_eq_integral_rankOne hfixed]
  rfl

/-- Every complex empirical covariance error is bounded by twice the real
covariance error of the same sample. This is a pointwise operator identity
and norm estimate, so no concentration premise enters here. -/
theorem norm_complex_covariance_error_le_two_real {mu : Measure E} [IsFiniteMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) {T : ℕ} (X : Fin T → E) :
    ‖complexSampleCovariance X - complexPopulationCovariance mu‖ ≤
      2 * ‖sampleCovariance X - populationCovariance mu‖ := by
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ)
      (complexSampleCovariance X - complexPopulationCovariance mu),
    ContinuousLinearMap.restrictScalars_sub,
    complexSampleCovariance_restrict, complexPopulationCovariance_restrict hfixed, ← map_sub]
  exact norm_symmetrize_le _

end
end TomographyOracleCore.Revision.ComplexCovarianceSymmetrization
