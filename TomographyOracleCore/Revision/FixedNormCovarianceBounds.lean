import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.FixedNormCovarianceBounds

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance
open scoped InnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}

theorem integrable_rankOne_fixedNorm (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    Integrable (rankOneCovariance (E := E)) mu := by
  apply (integrable_const q).mono' continuous_rankOneCovariance.aestronglyMeasurable
  filter_upwards [hfixed] with x hx
  rw [norm_rankOneCovariance, hx]

theorem populationCovariance_integral_rankOne (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    populationCovariance mu = ∫ x, rankOneCovariance x ∂mu := by
  ext u
  rw [ContinuousLinearMap.integral_apply (integrable_rankOne_fixedNorm hfixed),
    covarianceOperator_apply (fixedNorm_memLp hfixed 2)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [rankOneCovariance_apply, real_inner_comm]

theorem norm_populationCovariance_le_fixedNorm (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    ‖populationCovariance mu‖ ≤ q := by
  rw [populationCovariance_integral_rankOne hfixed]
  calc
    _ ≤ ∫ x, ‖rankOneCovariance x‖ ∂mu := norm_integral_le_integral_norm _
    _ = ∫ _x : E, q ∂mu := by
      apply integral_congr_ae
      filter_upwards [hfixed] with x hx
      rw [norm_rankOneCovariance, hx]
    _ = q := by simp

theorem norm_populationCovariance_pos [FiniteDimensional ℝ E]
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q) : 0 < ‖populationCovariance mu‖ := by
  apply norm_pos_iff.2
  intro hz
  have ht := trace_populationCovariance_eq_fixedNorm hfixed
  rw [hz] at ht
  have hq0 : (0 : ℝ) = q := by simpa using ht
  linarith

theorem effectiveRank_ge_one [FiniteDimensional ℝ E]
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 < q) : 1 ≤ q / ‖populationCovariance mu‖ := by
  rw [le_div_iff₀ (norm_populationCovariance_pos hfixed hq), one_mul]
  exact norm_populationCovariance_le_fixedNorm hfixed

end
end TomographyOracleCore.Revision.FixedNormCovarianceBounds
