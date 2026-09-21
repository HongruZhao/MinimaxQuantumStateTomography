import TomographyOracleCore.Revision.PhysicalMinimaxEstimator
import TomographyOracleCore.UpperRateScaling
import TomographyOracleCore.UpperSmallSample
import TomographyOracleCore.SpectralTailEndpoint

/-!
# Candidate 2: actual expected risk and three-regime optimization

Only the displayed expected forward-covariance estimate is assumed by the
statistical lemmas in this file. Fitting, the physical sampling law, the
Markov estimator, integration, and optimization over truncation ranks are
proved, rather than supplied as hypotheses.
-/

namespace TomographyOracleCore.Revision.PhysicalMinimax

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {n K T : ℕ}

/-- The exact periodic physical matrix-outcome product measure. -/
def periodicSampleLaw (h : ChoKimBlockCondition n K) (T : ℕ)
    (rho : DensityOperator (Fin (2 ^ n))) :
    Measure (Fin T → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  Measure.pi (fun _ : Fin T =>
    (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd).bornMeasure rho)

instance periodicSampleLaw_isProbability (h : ChoKimBlockCondition n K) (T : ℕ)
    (rho : DensityOperator (Fin (2 ^ n))) :
    IsProbabilityMeasure (periodicSampleLaw h T rho) := by
  letI : IsProbabilityMeasure
      ((choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd).bornMeasure rho) :=
    (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd).born_probability rho
  unfold periodicSampleLaw
  infer_instance

/-- Forward estimation noise in the exact calibrated matrix model. -/
def periodicForwardError (h : ChoKimBlockCondition n K)
    (rho : DensityOperator (Fin (2 ^ n)))
    (sample : Fin T → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) : ℝ :=
  forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
    (empiricalForwardMatrix sample) rho

/-- Real expected trace loss of the selected exact forward minimizer. -/
def periodicExpectedError (h : ChoKimBlockCondition n K) (T : ℕ)
    (rho : DensityOperator (Fin (2 ^ n))) : ℝ :=
  ∫ sample, sampleTraceError (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho sample
    ∂periodicSampleLaw h T rho

theorem periodicExpectedError_le_two (h : ChoKimBlockCondition n K) (T : ℕ)
    (rho : DensityOperator (Fin (2 ^ n))) :
    periodicExpectedError h T rho ≤ 2 := by
  have hi := integrable_productBorn_real (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho
    (sampleTraceError (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho)
  change Integrable _ (periodicSampleLaw h T rho) at hi
  have hle := integral_mono hi (integrable_const (2 : ℝ))
    (sampleTraceError_le_two (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho)
  simpa only [periodicExpectedError, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] using hle

/-- Exact physical expected oracle, conditional only on a forward noise
expectation. The exact minimizer fitting property is proved internally. -/
theorem periodicExpectedError_oracle (h : ChoKimBlockCondition n K) (T : ℕ)
    (rho : DensityOperator (Fin (2 ^ n))) (noise : ℝ)
    (hmean : (∫ sample, periodicForwardError h rho sample
      ∂periodicSampleLaw h T rho) ≤ noise) :
    OracleBound (periodicExpectedError h T rho)
      (orderedSpectralTail rho) (64 * noise) (2 ^ n) := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  have hD : 0 < 2 ^ n := by positivity
  intro r hr1 hrd
  have hierr := integrable_productBorn_real hD U T rho (sampleTraceError hD U T rho)
  have hieta := integrable_productBorn_real hD U T rho (periodicForwardError h rho)
  have hirhs := integrable_productBorn_real hD U T rho
    (fun sample => 4 * orderedSpectralTail rho r +
      64 * (r : ℝ) * periodicForwardError h rho sample)
  change Integrable _ (periodicSampleLaw h T rho) at hierr hieta hirhs
  have hpoint : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      sampleTraceError hD U T rho sample ≤ 4 * orderedSpectralTail rho r +
        64 * (r : ℝ) * periodicForwardError h rho sample := by
    have hs := ae_mem_possibleSamples hD U T rho
    filter_upwards [hs] with sample hsample
    have hfit := sampleEstimator_fit hD U T sample hsample rho
    have ho := Candidate2DeterministicOracle.periodicApproximateForwardFit_orderedSpectralOracle
      h (empiricalForwardMatrix sample) (sampleEstimator hD U T sample) rho
      (periodicForwardError h rho sample) 0
      (matrixOperatorNorm_nonneg _) (by norm_num)
      (by simpa [periodicForwardError, forwardObjective, U] using hfit)
      (le_refl _)
    have hor := ho r hr1 hrd
    dsimp only [sampleTraceError]
    simpa only [mul_zero, zero_mul, add_zero, mul_assoc, mul_comm, mul_left_comm] using hor
  have hle := integral_mono_ae hierr hirhs hpoint
  have heq : (∫ sample, (4 * orderedSpectralTail rho r +
        64 * (r : ℝ) * periodicForwardError h rho sample)
      ∂periodicSampleLaw h T rho) =
      4 * orderedSpectralTail rho r + 64 * (r : ℝ) *
        (∫ sample, periodicForwardError h rho sample ∂periodicSampleLaw h T rho) := by
    rw [integral_add (integrable_const _) (hieta.const_mul _)]
    simp only [integral_const_mul, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  rw [heq] at hle
  have hnoise := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ 64 * (r : ℝ) by positivity)
  change periodicExpectedError h T rho ≤ _
  dsimp only [periodicExpectedError] at ⊢
  nlinarith

/-- The exact three-regime expected-risk rate, including the full-rank
endpoint, with no fitting assumption. -/
theorem periodicExpectedError_rate (h : ChoKimBlockCondition n K)
    (hT : 0 < T) (rho : DensityOperator (Fin (2 ^ n)))
    (A alpha L : ℝ) (hA : 0 < A) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hrho : rho ∈ spectralDecayClass (2 ^ n) alpha L)
    (hmean : (∫ sample, periodicForwardError h rho sample
      ∂periodicSampleLaw h T rho) ≤
      A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) :
    periodicExpectedError h T rho ≤
      (12 * max 1 (16 * A)) * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha := by
  let scale := Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))
  have hscale : 0 < scale := by
    dsimp [scale]
    apply Real.sqrt_pos.mpr
    exact div_pos (by positivity) (by exact_mod_cast hT)
  have horacle := periodicExpectedError_oracle h T rho (A * scale) hmean
  have horacle' : OracleBound (periodicExpectedError h T rho)
      (orderedSpectralTail rho) (4 * ((16 * A) * scale)) (2 ^ n) := by
    convert horacle using 1 <;> ring
  have hraw := decay_oracle_three_regime
    (periodicExpectedError h T rho) L ((16 * A) * scale) alpha
    (orderedSpectralTail rho) (2 ^ n) (Nat.one_le_pow n 2 (by norm_num)) hL
    (by positivity) halpha (periodicExpectedError_le_two h T rho) horacle'
    (fun s hs1 hsD => hrho s hs1 hsD)
    (orderedSpectralTail_fin_dimension_eq_zero (2 ^ n) rho)
  have hscaleRate := decayUpperRate_const_mul_sqrt_le_spectralDecayMinimaxRate
    (2 ^ n) (T : ℝ) L alpha (16 * A) (Nat.one_le_pow n 2 (by norm_num))
    (by exact_mod_cast hT) hL halpha (by positivity)
  calc
    periodicExpectedError h T rho ≤
        12 * decayUpperRate (2 ^ n) L ((16 * A) * scale) alpha := hraw
    _ ≤ 12 * (max 1 (16 * A) * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) :=
      mul_le_mul_of_nonneg_left hscaleRate (by norm_num)
    _ = _ := by ring

end
end TomographyOracleCore.Revision.PhysicalMinimax
