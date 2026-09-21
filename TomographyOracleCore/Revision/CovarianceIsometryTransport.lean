import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

namespace TomographyOracleCore.Revision.CovarianceIsometryTransport

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance
open scoped BigOperators RealInnerProductSpace
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [InnerProductSpace ℝ E] [InnerProductSpace ℝ F] [CompleteSpace E] [CompleteSpace F]

theorem norm_conjugate_le (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) :
    ‖e.conjStarAlgEquiv A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro x
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.norm_map]
  simpa only [e.symm.norm_map] using A.le_opNorm (e.symm x)

theorem norm_conjugate (e : E ≃ₗᵢ[ℝ] F) (A : E →L[ℝ] E) :
    ‖e.conjStarAlgEquiv A‖ = ‖A‖ := by
  apply le_antisymm (norm_conjugate_le e A)
  have h := norm_conjugate_le e.symm (e.conjStarAlgEquiv A)
  simpa only [← LinearIsometryEquiv.symm_conjStarAlgEquiv,
    StarAlgEquiv.symm_apply_apply] using h

theorem rankOneCovariance_map (e : E ≃ₗᵢ[ℝ] F) (x : E) :
    rankOneCovariance (e x) = e.conjStarAlgEquiv (rankOneCovariance x) := by
  ext y
  obtain ⟨y, rfl⟩ := e.surjective y
  simp only [rankOneCovariance_apply, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    e.symm_apply_apply, e.map_smul, e.inner_map_map]

theorem sampleCovariance_map (e : E ≃ₗᵢ[ℝ] F) {T : ℕ} (X : Fin T → E) :
    sampleCovariance (fun i => e (X i)) = e.conjStarAlgEquiv (sampleCovariance X) := by
  simp only [sampleCovariance, rankOneCovariance_map, map_smul, map_sum]

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [SecondCountableTopology E] [SecondCountableTopology F]

theorem memLp_id_map (e : E ≃ₗᵢ[ℝ] F) {mu : Measure E} (hmu : MemLp id 2 mu) :
    MemLp id 2 (mu.map e) := by
  apply (memLp_map_measure_iff aestronglyMeasurable_id e.continuous.measurable.aemeasurable).2
  simpa only [Function.comp_def, id_eq] using
    e.isometry.lipschitz.comp_memLp e.map_zero hmu

theorem populationCovariance_map (e : E ≃ₗᵢ[ℝ] F) {mu : Measure E}
    (hmu : MemLp id 2 mu) :
    populationCovariance (mu.map e) = e.conjStarAlgEquiv (populationCovariance mu) := by
  ext v
  apply ext_inner_right ℝ
  intro w
  obtain ⟨v, rfl⟩ := e.surjective v
  obtain ⟨w, rfl⟩ := e.surjective w
  rw [populationCovariance_inner (memLp_id_map e hmu),
    integral_map e.continuous.measurable.aemeasurable (by fun_prop),
    LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, e.symm_apply_apply,
    e.inner_map_map, populationCovariance_inner hmu]
  simp only [e.inner_map_map]

theorem hasL6L2_map (e : E ≃ₗᵢ[ℝ] F) {mu : Measure E} {kappa : ℝ}
    (h : HasL6L2Marginals mu kappa) : HasL6L2Marginals (mu.map e) kappa := by
  intro v
  obtain ⟨v, rfl⟩ := e.surjective v
  rw [integral_map e.continuous.measurable.aemeasurable (by fun_prop),
    integral_map e.continuous.measurable.aemeasurable (by fun_prop)]
  simpa only [e.inner_map_map] using h v

theorem fixedNorm_map (e : E ≃ₗᵢ[ℝ] F) {mu : Measure E} {q : ℝ}
    (h : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) : ∀ᵐ x ∂mu.map e, ‖x‖ ^ 2 = q := by
  apply (ae_map_iff (p := fun x : F => ‖x‖ ^ 2 = q)
    e.continuous.measurable.aemeasurable
    (isClosed_eq (continuous_norm.pow 2) continuous_const).measurableSet).2
  simpa only [e.norm_map] using h

theorem integral_id_map (e : E ≃ₗᵢ[ℝ] F) (mu : Measure E) :
    (∫ x, x ∂mu.map e) = e (∫ x, x ∂mu) := by
  calc
    _ = ∫ x, e x ∂mu := integral_map e.continuous.measurable.aemeasurable
      (show AEStronglyMeasurable (fun x : F => x) (mu.map e) from continuous_id.aestronglyMeasurable)
    _ = _ := e.toLinearIsometry.integral_comp_comm id

theorem expected_covariance_error_map (e : E ≃ₗᵢ[ℝ] F) (mu : Measure E)
    [IsProbabilityMeasure mu] (hmu : MemLp id 2 mu) (T : ℕ) :
    (∫ X : Fin T → F, ‖sampleCovariance X - populationCovariance (mu.map e)‖
      ∂Measure.pi (fun _ : Fin T => mu.map e)) =
      ∫ X : Fin T → E, ‖sampleCovariance X - populationCovariance mu‖
        ∂Measure.pi (fun _ : Fin T => mu) := by
  letI : IsProbabilityMeasure (mu.map e) :=
    Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  rw [← Measure.pi_map_pi (fun _ : Fin T => e.continuous.measurable.aemeasurable)]
  rw [integral_map (φ := fun X : Fin T → E => fun i => e (X i))
    (f := fun X : Fin T → F => ‖sampleCovariance X - populationCovariance (mu.map e)‖)
    (measurable_pi_lambda _
    (fun i => e.continuous.measurable.comp (measurable_pi_apply i))).aemeasurable
    (((measurable_sampleCovariance (E := F)).sub_const _).norm.aestronglyMeasurable)]
  apply integral_congr_ae
  filter_upwards [] with X
  rw [sampleCovariance_map, populationCovariance_map e hmu, ← map_sub, norm_conjugate]

end
end TomographyOracleCore.Revision.CovarianceIsometryTransport
