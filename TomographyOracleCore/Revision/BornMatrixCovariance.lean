import TomographyOracleCore.Revision.BornProjectorPushforward
import TomographyOracleCore.Revision.ComplexCovarianceSymmetrization
import TomographyOracleCore.Revision.PhysicalMinimaxEstimator

namespace TomographyOracleCore.Revision.BornMatrixCovariance

open MeasureTheory MatrixReduction PhysicalMinimax FourthVectorBoundary
open BornProjectorPushforward ComplexCovarianceSymmetrization Candidate2FiniteBornVectorLaw
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section

variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]

def matrixOperatorIsometry (D : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗᵢ[ℝ]
      (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D)) where
  toLinearMap := (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)).toAlgEquiv.toLinearMap.restrictScalars ℝ
  norm_map' _ := rfl

theorem matrixOperatorIsometry_projector (x : EuclideanSpace ℂ (Fin D)) :
    matrixOperatorIsometry D (vectorProjector x) = complexRankOne x := by
  ext u i
  change (∑ j, (x i * star (x j)) * u j) = ⟪x, u⟫_ℂ * x i
  simp only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem integrable_id_bornMeasure (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    Integrable (fun B => B) ((finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) := by
  letI : IsProbabilityMeasure ((finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) :=
    (finiteUnitaryProjectivePOVM D hD U).born_probability rho
  have h := IntegrableOn.of_finite
    (μ := (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) (f := fun B => B)
    (Set.finite_range (fun label : A × Fin D =>
      finiteUnitaryMeasurementProjector (U label.1) label.2))
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (ae_mem_projectorSupport hD U rho)] at h

/-- The mean physical projector is exactly the uncalibrated density channel. -/
theorem integral_id_bornMeasure (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    (∫ B, B ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) =
      finiteUnitaryProjectiveDensityForward U rho := by
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  ext i j
  rw [integral_matrix_apply (Fin D) _ _ (integrable_id_bornMeasure hD U rho) i j,
    integral_finiteUnitaryProjectivePOVM_bornMeasure_complex_eq_sum hD]
  simp only [finiteUnitaryProjectiveDensityForward, Matrix.smul_apply,
    Matrix.sum_apply]

theorem integral_projector_phaseBorn (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    (∫ x, vectorProjector x ∂finiteUnitaryPhaseRandomizedBornVectorLaw U rho) =
      ((D : ℝ) + 1) • finiteUnitaryProjectiveDensityForward U rho := by
  have hp : ∀ x : EuclideanSpace ℂ (Fin D),
      vectorProjector x = ((D : ℝ) + 1) • normalizedProjector D x := by
    intro x
    rw [normalizedProjector, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  simp_rw [hp]
  rw [integral_smul]
  congr 1
  rw [← integral_id_bornMeasure hD U rho,
    ← normalizedProjector_map_phaseBornVectorLaw hD U rho,
    integral_map (continuous_normalizedProjector D).measurable.aemeasurable
      (f := fun B : Matrix (Fin D) (Fin D) ℂ => B) continuous_id.aestronglyMeasurable]

theorem complexPopulationCovariance_phaseBorn (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    complexPopulationCovariance (finiteUnitaryPhaseRandomizedBornVectorLaw U rho) =
      matrixOperatorIsometry D (((D : ℝ) + 1) • finiteUnitaryProjectiveDensityForward U rho) := by
  rw [← integral_projector_phaseBorn hD U rho,
    ← (matrixOperatorIsometry D).integral_comp_comm]
  simp only [matrixOperatorIsometry_projector, complexPopulationCovariance]

/-- The literal calibrated matrix error is exactly a complex covariance error. -/
theorem forwardObjective_projector_sample (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D))
    {T : ℕ} (X : Fin T → EuclideanSpace ℂ (Fin D)) :
    forwardObjective U (empiricalForwardMatrix (fun i => normalizedProjector D (X i))) rho =
      ‖complexSampleCovariance X -
        complexPopulationCovariance (finiteUnitaryPhaseRandomizedBornVectorLaw U rho)‖ := by
  have hsample : empiricalForwardMatrix (fun i => normalizedProjector D (X i)) =
      (T : ℝ)⁻¹ • ∑ i, vectorProjector (X i) - 1 := by
    unfold empiricalForwardMatrix normalizedProjector
    rw [← Finset.smul_sum, smul_smul]
    congr 2
    push_cast
    field_simp
  rw [forwardObjective, hsample, finiteUnitaryFullCalibratedLinearChannel_density,
    finiteUnitaryCalibratedDensityChannel, sub_sub_sub_cancel_right]
  change ‖(T : ℝ)⁻¹ • ∑ i, vectorProjector (X i) -
    (((D + 1 : ℕ) : ℝ)) • finiteUnitaryProjectiveDensityForward U rho‖ = _
  rw [← (matrixOperatorIsometry D).norm_map, map_sub, map_smul, map_sum]
  simp only [matrixOperatorIsometry_projector, Nat.cast_add, Nat.cast_one,
    complexSampleCovariance, complexPopulationCovariance_phaseBorn hD, map_smul]

end
end TomographyOracleCore.Revision.BornMatrixCovariance
