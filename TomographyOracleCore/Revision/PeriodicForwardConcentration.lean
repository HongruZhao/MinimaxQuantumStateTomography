import TomographyOracleCore.Revision.BornMatrixCovariance
import TomographyOracleCore.Revision.FixedNormCovarianceIntegrability
import TomographyOracleCore.Revision.PeriodicBornRealConcentration
import TomographyOracleCore.Revision.PhysicalMinimaxRates

namespace TomographyOracleCore.Revision.PeriodicForwardConcentration

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalMinimax
open Candidate2FiniteBornVectorLaw PeriodicForwardCovariance BornProjectorPushforward
open BornMatrixCovariance ComplexCovarianceSymmetrization FixedNormCovarianceIntegrability
open PeriodicBornRealConcentration
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section

local instance {D : ℕ} : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

/-- Transfer from the real covariance of phase-randomized vectors to the
paper's actual physical matrix-valued experiment. -/
theorem expected_forward_error_le_twice_real {D : ℕ} {A : Type*}
    [Fintype A] [Nonempty A] (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D))
    {T : ℕ} (hT : 0 < T) :
    (∫ sample, forwardObjective U (empiricalForwardMatrix sample) rho
      ∂Measure.pi (fun _ : Fin T => (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho)) ≤
      2 * (∫ X : Fin T → EuclideanSpace ℂ (Fin D),
        ‖sampleCovariance X -
          populationCovariance (finiteUnitaryPhaseRandomizedBornVectorLaw U rho)‖
        ∂Measure.pi (fun _ : Fin T => finiteUnitaryPhaseRandomizedBornVectorLaw U rho)) := by
  let mu := finiteUnitaryPhaseRandomizedBornVectorLaw U rho
  let nu := (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho
  let f := fun sample : Fin T → Matrix (Fin D) (Fin D) ℂ =>
    forwardObjective U (empiricalForwardMatrix sample) rho
  let Phi := fun X : Fin T → EuclideanSpace ℂ (Fin D) =>
    fun i => normalizedProjector D (X i)
  letI : IsProbabilityMeasure mu := finiteUnitaryPhaseRandomizedBornVectorLaw_isProbability hD U rho
  letI : IsProbabilityMeasure nu := (finiteUnitaryProjectivePOVM D hD U).born_probability rho
  have hPhi : Measurable Phi := measurable_pi_lambda _
    (fun i => (continuous_normalizedProjector D).measurable.comp (measurable_pi_apply i))
  have hmap : (Measure.pi (fun _ : Fin T => mu)).map Phi =
      Measure.pi (fun _ : Fin T => nu) := by
    rw [Measure.pi_map_pi (fun _ : Fin T =>
      (continuous_normalizedProjector D).measurable.aemeasurable)]
    simp only [mu, normalizedProjector_map_phaseBornVectorLaw hD, nu]
  have hf : AEStronglyMeasurable f ((Measure.pi (fun _ : Fin T => mu)).map Phi) := by
    rw [hmap]
    exact (integrable_productBorn_real hD U T rho f).aestronglyMeasurable
  have heq : (∫ sample, f sample ∂Measure.pi (fun _ : Fin T => nu)) =
      ∫ X, f (Phi X) ∂Measure.pi (fun _ : Fin T => mu) := by
    rw [← hmap, integral_map hPhi.aemeasurable hf]
  change (∫ sample, f sample ∂Measure.pi (fun _ : Fin T => nu)) ≤ _
  rw [heq]
  have hfixed := ae_fixedNorm_finiteUnitaryPhaseRandomizedBornVectorLaw hD U rho
  have hi := (integrable_fixedNorm_covariance_error hfixed hT).const_mul (2 : ℝ)
  calc
    _ = ∫ X : Fin T → EuclideanSpace ℂ (Fin D),
        ‖complexSampleCovariance X - complexPopulationCovariance mu‖
        ∂Measure.pi (fun _ : Fin T => mu) := by
      apply integral_congr_ae
      filter_upwards [] with X
      exact forwardObjective_projector_sample hD U rho X
    _ ≤ ∫ X : Fin T → EuclideanSpace ℂ (Fin D),
        2 * ‖sampleCovariance X - populationCovariance mu‖
        ∂Measure.pi (fun _ : Fin T => mu) := by
      apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) hi
      exact ae_of_all _ (norm_complex_covariance_error_le_two_real hfixed)
    _ = _ := integral_const_mul _ _

/-- Proposition E.1 for the literal periodic Born experiment. Its sole
scientific dependency is the general fixed-norm covariance theorem; all
circuit moments, phase randomization, and matrix-law transport are proved. -/
theorem periodic_expected_forward_covariance :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (H : ChoKimBlockCondition n K),
        0 < n → 0 < T → c * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ) →
        ∀ rho : DensityOperator (Fin (2 ^ n)),
          (∫ sample, periodicForwardError H rho sample
            ∂periodicSampleLaw H T rho) ≤
            A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) := by
  obtain ⟨c, A, hc, hA, hreal⟩ := periodic_real_expected_covariance
  refine ⟨c, 2 * A, hc, by positivity, ?_⟩
  intro n K T H hn hT hsize rho
  have htransfer := expected_forward_error_le_twice_real (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) rho hT
  have hconcentration := mul_le_mul_of_nonneg_left (hreal H hn hT hsize rho) (by norm_num : (0 : ℝ) ≤ 2)
  calc
    _ ≤ _ := htransfer
    _ ≤ 2 * (A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) := hconcentration
    _ = _ := by ring

end
end TomographyOracleCore.Revision.PeriodicForwardConcentration
