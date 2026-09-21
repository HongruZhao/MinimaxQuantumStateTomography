import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing

namespace TomographyOracleCore.Revision.FixedNormCovarianceIntegrability

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance
open scoped BigOperators RealInnerProductSpace
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_sampleCovariance_le_fixedNorm {T : ℕ} (hT : 0 < T)
    (X : Fin T → E) {q : ℝ} (hfixed : ∀ i, ‖X i‖ ^ 2 = q) :
    ‖sampleCovariance X‖ ≤ q := by
  rw [sampleCovariance, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (Nat.cast_nonneg T)]
  calc
    _ ≤ (T : ℝ)⁻¹ * ∑ i, ‖rankOneCovariance (X i)‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = q := by
      simp only [norm_rankOneCovariance, hfixed, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

theorem integrable_fixedNorm_covariance_error {mu : Measure E} [IsProbabilityMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) {T : ℕ} (hT : 0 < T) :
    Integrable (fun X : Fin T → E => ‖sampleCovariance X - populationCovariance mu‖)
      (Measure.pi (fun _ : Fin T => mu)) := by
  apply (integrable_const (q + ‖populationCovariance mu‖)).mono'
    ((measurable_sampleCovariance.sub_const _).norm.aestronglyMeasurable)
  have hcoord : ∀ i : Fin T, ∀ᵐ X ∂Measure.pi (fun _ : Fin T => mu), ‖X i‖ ^ 2 = q := by
    intro i
    exact (Measure.tendsto_eval_ae_ae (μ := fun _ : Fin T => mu) (i := i)).eventually hfixed
  filter_upwards [Filter.eventually_all.mpr hcoord] with X hX
  rw [Real.norm_eq_abs, abs_norm]
  exact (norm_sub_le _ _).trans
    (add_le_add (norm_sampleCovariance_le_fixedNorm hT X hX) le_rfl)

end
end TomographyOracleCore.Revision.FixedNormCovarianceIntegrability
