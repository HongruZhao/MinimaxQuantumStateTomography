import TomographyOracleCore.Revision.PhysicalMinimaxAlgorithmRates
import TomographyOracleCore.Revision.ConstantOracle
import TomographyOracleCore.Revision.ConstantRates

namespace TomographyOracleCore.Revision.PhysicalMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators Matrix.Norms.L2Operator ENNReal
noncomputable section
variable {n K T : ℕ}
theorem periodicAlgorithmExpectedError_oracle_sharp (h : ChoKimBlockCondition n K) (T : ℕ)
    (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hfit : ∀ Q rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma)
    (rho : DensityOperator (Fin (2 ^ n))) (noise : ℝ)
    (hmean : (∫ sample, periodicForwardError h rho sample
      ∂periodicSampleLaw h T rho) ≤ noise) :
    OracleBound (periodicAlgorithmExpectedError h T solve rho)
      (orderedSpectralTail rho) ((8 / sharpPeriodicCurvature) * noise + (4 / sharpPeriodicCurvature) * gamma) (2 ^ n) := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  have hD : 0 < 2 ^ n := by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity
  intro r hr1 hrd
  have hierr := integrable_productBorn_real hD U T rho (algorithmTraceError hD U T solve rho)
  have hieta := integrable_productBorn_real hD U T rho (periodicForwardError h rho)
  have hirhs := integrable_productBorn_real hD U T rho
    (fun sample => (4 * orderedSpectralTail rho r + (4 / sharpPeriodicCurvature) * (r : ℝ) * gamma) +
      (8 / sharpPeriodicCurvature) * (r : ℝ) * periodicForwardError h rho sample)
  change Integrable _ (periodicSampleLaw h T rho) at hierr hieta hirhs
  have hpoint : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      algorithmTraceError hD U T solve rho sample ≤
        (4 * orderedSpectralTail rho r + (4 / sharpPeriodicCurvature) * (r : ℝ) * gamma) +
        (8 / sharpPeriodicCurvature) * (r : ℝ) * periodicForwardError h rho sample := by
    have hs := ae_mem_possibleSamples hD U T rho
    filter_upwards [hs] with sample hsample
    have hsampleFit : forwardObjective U (empiricalForwardMatrix sample)
        (algorithmSampleEstimator hD U T solve sample) ≤
        forwardObjective U (empiricalForwardMatrix sample) rho + gamma := by
      rw [algorithmSampleEstimator_eq hD U T solve sample hsample]
      exact hfit _ rho
    have ho := Candidate2DeterministicOracle.periodicApproximateForwardFit_orderedSpectralOracle_sharp
      h (empiricalForwardMatrix sample) (algorithmSampleEstimator hD U T solve sample) rho
      (periodicForwardError h rho sample) gamma
      (matrixOperatorNorm_nonneg _) hgamma
      (by exact hsampleFit) (le_refl _)
    have hor := ho r hr1 hrd
    dsimp only [algorithmTraceError]
    nlinarith
  have hle := integral_mono_ae hierr hirhs hpoint
  have heq : (∫ sample,
        ((4 * orderedSpectralTail rho r + (4 / sharpPeriodicCurvature) * (r : ℝ) * gamma) +
          (8 / sharpPeriodicCurvature) * (r : ℝ) * periodicForwardError h rho sample)
      ∂periodicSampleLaw h T rho) =
      (4 * orderedSpectralTail rho r + (4 / sharpPeriodicCurvature) * (r : ℝ) * gamma) + (8 / sharpPeriodicCurvature) * (r : ℝ) *
        (∫ sample, periodicForwardError h rho sample ∂periodicSampleLaw h T rho) := by
    rw [integral_add (integrable_const _) (hieta.const_mul _)]
    simp only [integral_const_mul, integral_const, Measure.real, measure_univ,
      ENNReal.toReal_one, one_smul]
  rw [heq] at hle
  have hnoise := mul_le_mul_of_nonneg_left hmean
    (show 0 ≤ (8 / sharpPeriodicCurvature) * (r : ℝ) by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity)
  change periodicAlgorithmExpectedError h T solve rho ≤ _
  dsimp only [periodicAlgorithmExpectedError]
  nlinarith

/-- The literal expected risk has the advertised exact three-regime rate
whenever the verified solver tolerance is at most `sqrt(D/T)`. -/
theorem periodicAlgorithmExpectedError_rate_sharp (h : ChoKimBlockCondition n K)
    (hT : 0 < T)
    (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ Q rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma)
    (rho : DensityOperator (Fin (2 ^ n)))
    (A alpha L : ℝ) (hA : 0 < A) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hrho : rho ∈ spectralDecayClass (2 ^ n) alpha L)
    (hmean : (∫ sample, periodicForwardError h rho sample
      ∂periodicSampleLaw h T rho) ≤
      A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) :
    periodicAlgorithmExpectedError h T solve rho ≤
      (10 * max 1 ((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature))) * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha := by
  let scale := Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))
  have hscale : 0 < scale := by
    dsimp [scale]
    exact Real.sqrt_pos.mpr (div_pos (by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity) (by exact_mod_cast hT))
  have horacle := periodicAlgorithmExpectedError_oracle_sharp h T solve gamma hgamma hfit
    rho (A * scale) hmean
  have hnoise : (8 / sharpPeriodicCurvature) * (A * scale) +
      (4 / sharpPeriodicCurvature) * gamma ≤
        4 * (((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)) * scale) := by
    have hm := mul_le_mul_of_nonneg_left hgammaScale
      (show 0 ≤ 4 / sharpPeriodicCurvature by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity)
    calc
      _ ≤ (8 / sharpPeriodicCurvature) * (A * scale) +
          (4 / sharpPeriodicCurvature) * scale := add_le_add le_rfl hm
      _ = _ := by ring
  have horacle' : OracleBound (periodicAlgorithmExpectedError h T solve rho)
      (orderedSpectralTail rho) (4 * (((2 / sharpPeriodicCurvature) * A +
        (1 / sharpPeriodicCurvature)) * scale)) (2 ^ n) := by
    intro r hr1 hrD
    exact (horacle r hr1 hrD).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_right hnoise (Nat.cast_nonneg r)))
  have hraw := decay_oracle_three_regime_ten
    (periodicAlgorithmExpectedError h T solve rho) L (((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)) * scale) alpha
    (orderedSpectralTail rho) (2 ^ n) (Nat.one_le_pow n 2 (by norm_num)) hL
    (by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity) halpha (periodicAlgorithmExpectedError_le_two h T solve rho) horacle'
    (fun s hs1 hsD => hrho s hs1 hsD)
    (orderedSpectralTail_fin_dimension_eq_zero (2 ^ n) rho)
  have hscaleRate := decayUpperRate_const_mul_sqrt_le_spectralDecayMinimaxRate
    (2 ^ n) (T : ℝ) L alpha ((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)) (Nat.one_le_pow n 2 (by norm_num))
    (by exact_mod_cast hT) hL halpha (by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity)
  calc
    periodicAlgorithmExpectedError h T solve rho ≤
        10 * decayUpperRate (2 ^ n) L (((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)) * scale) alpha := hraw
    _ ≤ 10 * (max 1 ((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)) * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) :=
      mul_le_mul_of_nonneg_left hscaleRate (by norm_num)
    _ = _ := by ring

/-- The universal constant preserves the two physical sample-size branches. -/
def algorithmUpperConstant_sharp (c A : ℝ) : ℝ := max (2 * c) (10 * max 1 ((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)))

theorem algorithmUpperConstant_sharp_pos (c A : ℝ) (hc : 1 ≤ c) :
    0 < algorithmUpperConstant_sharp c A := by
  exact lt_of_lt_of_le (by linarith : 0 < 2 * c) (le_max_left _ _)

/-- Pointwise all-sample physical risk of the supplied actual solver. -/
theorem periodicAlgorithm_physicalRisk_rate_sharp (h : ChoKimBlockCondition n K)
    (hT : 0 < T)
    (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ Q rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma)
    (c A : ℝ) (hc : 1 ≤ c) (hA : 0 < A)
    (hmean : c * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ) →
      ∀ rho : DensityOperator (Fin (2 ^ n)),
      (∫ sample, periodicForwardError h rho sample ∂periodicSampleLaw h T rho) ≤
        A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (rho : DensityOperator (Fin (2 ^ n))) (alpha L : ℝ)
    (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hrho : rho ∈ spectralDecayClass (2 ^ n) alpha L) :
    statewiseExpectedTraceRisk
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (algorithmPhysicalEstimator (by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity)
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) rho ≤
    ENNReal.ofReal (algorithmUpperConstant_sharp c A *
      spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  have hD1 := Nat.one_le_pow n 2 (by norm_num)
  have hrate0 : 0 ≤ spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha := by
    unfold spectralDecayMinimaxRate samplingDecayRate
    positivity
  by_cases hlarge : c * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ)
  · have herr := periodicAlgorithmExpectedError_rate_sharp h hT solve gamma hgamma hgammaScale
      hfit rho A alpha L hA halpha hL hrho (hmean hlarge rho)
    have hphys := algorithmPhysicalEstimator_risk_le_product_integral (by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve rho
    apply hphys.trans
    apply ENNReal.ofReal_le_ofReal
    exact herr.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hrate0)
  · have hsmall : (T : ℝ) ≤ c * (((2 ^ n : ℕ) : ℝ)) := (lt_of_not_ge hlarge).le
    have hrate := one_div_le_spectralDecayMinimaxRate_of_samples_le
      (2 ^ n) T alpha L c hD1 hT halpha hL hc hsmall
    have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
    have hCrate : 1 ≤ c * spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha := by
      calc
        1 = c * (1 / c) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hrate hcpos.le
    have htwo : (2 : ℝ) ≤ algorithmUpperConstant_sharp c A *
        spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha := by
      have hm := mul_le_mul_of_nonneg_right (le_max_left (2 * c) (10 * max 1 ((2 / sharpPeriodicCurvature) * A + (1 / sharpPeriodicCurvature)))) hrate0
      dsimp only [algorithmUpperConstant_sharp]
      nlinarith
    exact (statewiseExpectedTraceRisk_le_two _ _ _).trans (by
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal htwo)

/-- One physical algorithm adapts simultaneously to every spectral-tail
class; the chosen estimator is independent of alpha and L. -/
theorem periodicAlgorithm_simultaneousPhysicalUpper_sharp (h : ChoKimBlockCondition n K)
    (hT : 0 < T)
    (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
    (gamma : ℝ) (hgamma : 0 ≤ gamma)
    (hgammaScale : gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)))
    (hfit : ∀ Q rho,
      forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
        forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma)
    (c A : ℝ) (hc : 1 ≤ c) (hA : 0 < A)
    (hmean : c * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ) →
      ∀ rho : DensityOperator (Fin (2 ^ n)),
      (∫ sample, periodicForwardError h rho sample ∂periodicSampleLaw h T rho) ≤
        A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) :
    SimultaneousPhysicalUpper (2 ^ n) T
      (constantMatrixPOVMPhysicalDesign (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
      (fun _ => algorithmUpperConstant_sharp c A) := by
  refine ⟨algorithmPhysicalEstimator (by have hcurvaturePositive := sharpPeriodicCurvature_pos; positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve, ?_⟩
  intro alpha L halpha hL
  unfold classWorstCaseRisk
  apply iSup_le
  intro rho
  exact periodicAlgorithm_physicalRisk_rate_sharp h hT solve gamma hgamma hgammaScale hfit
    c A hc hA hmean rho.1 alpha L halpha hL rho.2

end
end TomographyOracleCore.Revision.PhysicalMinimax
