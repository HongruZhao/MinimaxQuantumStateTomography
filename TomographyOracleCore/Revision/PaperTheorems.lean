import TomographyOracleCore.Revision.StatisticalMinimaxCertificate
import TomographyOracleCore.Revision.ConstantRankEndpoints

/-!
Paper-facing endpoints in oracle-first order. The statewise result has no
spectral-class hypothesis. Spectral-class minimaxity and the rank consequence
retain the existing proved endpoints and their full hypotheses.
-/
namespace TomographyOracleCore.PaperTheorems

open MeasureTheory MatrixReduction Revision.PhysicalMinimax
open Revision.ConstantCovariance
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- The universal noise coefficient in the statewise oracle. -/
def statewiseOracleConstant : ℝ :=
  (8 * sharpForwardCovarianceConstant + 4) / sharpPeriodicCurvature

theorem statewiseOracleConstant_pos : 0 < statewiseOracleConstant := by
  have ha := sharpPeriodicCurvature_pos
  have hA := sharpForwardCovarianceConstant_pos
  unfold statewiseOracleConstant
  positivity

/-- The all-sample trace-loss cap, for any density-valued record rule. -/
theorem statewise_loss_cap
    {n K T : ℕ} (h : ChoKimBlockCondition n K)
    (estimate : (Fin T → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) →
      DensityOperator (Fin (2 ^ n)))
    (rho : DensityOperator (Fin (2 ^ n))) :
    (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤ 2 := by
  have hi := integrable_productBorn_real (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho
    (fun sample => hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho))
  change Integrable _ (periodicSampleLaw h T rho) at hi
  have hle := integral_mono hi (integrable_const (2 : ℝ))
    (fun sample => density_hermitianTraceNorm_sub_le_two (estimate sample) rho)
  simpa only [integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] using hle

/-- Paper Theorem 1: the expected adaptive oracle for an arbitrary feasible
record-dependent approximate fit. The fitting premise is only almost sure;
there is no rank, eigenbasis, alpha, L, or spectral-decay assumption on rho.
The finite Born record law makes every real record statistic integrable. -/
theorem statewise_adaptive_oracle
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hsize : 2 * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ))
    (estimate : (Fin T → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) →
      DensityOperator (Fin (2 ^ n)))
    (rho : DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) (estimate sample) ≤
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) rho + gamma) :
    ∀ s : ℕ, 1 ≤ s → s ≤ 2 ^ n →
      (∫ sample, hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
        ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤
      4 * orderedSpectralTail rho s + statewiseOracleConstant * (s : ℝ) *
        Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) := by
  intro s hs hsD
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let q := Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))
  have ha := sharpPeriodicCurvature_pos
  have hierr := integrable_productBorn_real (by positivity) U T rho
    (fun sample => hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
      ((estimate sample).sub_isHermitian rho))
  have hieta := integrable_productBorn_real (by positivity) U T rho
    (periodicForwardError h rho)
  have hirhs := integrable_productBorn_real (by positivity) U T rho
    (fun sample => (4 * orderedSpectralTail rho s +
      (4 / sharpPeriodicCurvature) * (s : ℝ) * gamma) +
      (8 / sharpPeriodicCurvature) * (s : ℝ) * periodicForwardError h rho sample)
  change Integrable _ (periodicSampleLaw h T rho) at hierr hieta hirhs
  have hpoint : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      hermitianTraceNorm ((estimate sample).matrix - rho.matrix)
        ((estimate sample).sub_isHermitian rho) ≤
      (4 * orderedSpectralTail rho s + (4 / sharpPeriodicCurvature) * (s : ℝ) * gamma) +
      (8 / sharpPeriodicCurvature) * (s : ℝ) * periodicForwardError h rho sample := by
    filter_upwards [hfit] with sample hsample
    have ho := Candidate2DeterministicOracle.periodicApproximateForwardFit_orderedSpectralOracle_sharp
      h (empiricalForwardMatrix sample) (estimate sample) rho
      (periodicForwardError h rho sample) gamma (matrixOperatorNorm_nonneg _) hgamma
      hsample (le_refl _)
    have hor := ho s hs hsD
    nlinarith
  have hle := integral_mono_ae hierr hirhs hpoint
  have heq : (∫ sample,
      ((4 * orderedSpectralTail rho s + (4 / sharpPeriodicCurvature) * (s : ℝ) * gamma) +
        (8 / sharpPeriodicCurvature) * (s : ℝ) * periodicForwardError h rho sample)
      ∂periodicSampleLaw h T rho) =
      (4 * orderedSpectralTail rho s + (4 / sharpPeriodicCurvature) * (s : ℝ) * gamma) +
        (8 / sharpPeriodicCurvature) * (s : ℝ) *
          (∫ sample, periodicForwardError h rho sample ∂periodicSampleLaw h T rho) := by
    rw [integral_add (integrable_const _) (hieta.const_mul _)]
    simp only [integral_const_mul, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  rw [heq] at hle
  have hmean := periodic_expected_forward_covariance_sharp h hn hT hsize rho
  have hnoise := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ (8 / sharpPeriodicCurvature) * (s : ℝ) by positivity)
  have htolerance := mul_le_mul_of_nonneg_left hgammaScale
    (show 0 ≤ (4 / sharpPeriodicCurvature) * (s : ℝ) by positivity)
  calc
    _ ≤ (4 * orderedSpectralTail rho s +
          (4 / sharpPeriodicCurvature) * (s : ℝ) *
            Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) +
        (8 / sharpPeriodicCurvature) * (s : ℝ) *
          (sharpForwardCovarianceConstant * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) :=
      hle.trans (add_le_add (add_le_add le_rfl htolerance) hnoise)
    _ = _ := by unfold statewiseOracleConstant; ring

/-- Paper Theorem 2: spectral-class upper specialization plus the matching
unrestricted nonadaptive single-copy lower bound; one exact fit serves all classes. -/
alias spectral_class_minimax := Verification.periodic_statistical_minimax_unconditional

/-- Paper Corollary 3: the all-sample rank upper bound for an actual forward solver. -/
alias exact_rank_upper := Revision.ConstantEndpoints.algorithm_rank_physicalRisk_sharp

end
end TomographyOracleCore.PaperTheorems
