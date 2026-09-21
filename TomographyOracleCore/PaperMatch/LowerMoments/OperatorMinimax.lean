import TomographyOracleCore.PaperMatch.Model.GeneralRisk
import TomographyOracleCore.PaperMatch.LowerMoments.OperatorInformation
import TomographyOracleCore.Revision.ConstantLower

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM
open Revision.NonadaptiveFano
open scoped ENNReal
noncomputable section
set_option maxHeartbeats 1500000
variable {Seed Outcome : Type*} [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- Packing, one-copy information, Fano, and fixed-state extraction for a
fully arbitrary operator-valued experiment, at every admissible rank. -/
theorem per_rank_fixed_state (k m T : ℕ) (L alpha : ℝ)
    (hm : 1 ≤ m) (hkm : 3 * m ≤ k) (hD : 514 ≤ k + 2)
    (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha)
    (design : OperatorDesign (k + 2) T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin (k + 2))))
    [IsMarkovKernel estimator] :
    ∃ rho ∈ spectralDecayClass (k + 2) alpha L,
      (11 / 16 : ENNReal) ≤ tailProbability design.experimentKernel estimator
        (hardFamilyMass m L (Real.sqrt ((k : ℝ) / T)) alpha / 4) rho ∧
      ENNReal.ofReal (11 * hardFamilyMass m L (Real.sqrt ((k : ℝ) / T)) alpha / 64) ≤
        expectedTraceLoss design.experimentKernel estimator rho := by
  obtain ⟨W, _⟩ := exists_complexGrassmannPackingWitness_card_eq hm hkm
  let b := hardFamilyMass m L (Real.sqrt ((k : ℝ) / T)) alpha
  have hb : 0 < b := hardFamilyMass_pos m L _ alpha hm (by linarith)
    (Real.sqrt_pos.mpr (div_pos (by exact_mod_cast (show 0 < k by omega))
      (by exact_mod_cast hT)))
  have hbq : b ≤ 1 / 4 := hardFamilyMass_le_quarter m L _ alpha
  have hscale : b ≤ lowerInformationConstant * (m : ℝ) * Real.sqrt ((k : ℝ) / T) := by
    simpa only [mul_assoc] using hardFamilyMass_le_information_scale m L _ alpha (Real.sqrt_nonneg _)
  have hlog : 4 * Real.log 2 ≤ Real.log W.card :=
    (four_log_two_le_grassmann_exponent (k + 2) m hD hm).trans
      (by simpa [lowerAmbientDimension, grassmannGamma0] using W.log_cardinality_lower)
  let : NeZero W.card := ⟨by
    intro hc
    simp only [hc, Nat.cast_zero, Real.log_zero] at hlog
    have hpos := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    linarith⟩
  obtain ⟨x, w, hmem, htail, hmean⟩ := sectionC_fixed_state_bounds
    design.toDominated estimator W.projector b alpha L hm hD hT hb hbq halpha hL
    (hardFamilyMass_le_decay_scale m L _ alpha (by linarith)) W.pairwise_separated
    (by simpa [grassmannGamma0] using W.log_cardinality_lower) hscale
  exact ⟨_, hmem, htail, hmean⟩

/-- Theorem 11's expected lower rate for each arbitrary procedure. -/
theorem theorem11_expected {D T : ℕ} (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha)
    (design : OperatorDesign D T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin D)))
    [IsMarkovKernel estimator] :
    ENNReal.ofReal (sharpDecayLowerConstant alpha * spectralDecayMinimaxRate D T L alpha) ≤
      worstCaseRisk (spectralDecayClass D alpha L) design estimator := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, D = k + 2 := ⟨D - 2, by omega⟩
  apply sharpSpectralDecayRateENNReal_le_of_perRankFanoMass _ (k + 2) T L alpha hD
    (by exact_mod_cast hT) hL halpha
  intro m hm hmM
  have hkm : 3 * m ≤ k := by
    dsimp [lowerEffectiveRankCap, lowerAmbientDimension] at hmM
    omega
  obtain ⟨rho, hmem, _, hmean⟩ := per_rank_fixed_state k m T L alpha hm hkm hD hT hL halpha
    design estimator
  have hmean' := hmean.trans (le_iSup
    (fun rho : spectralDecayClass (k + 2) alpha L =>
      expectedTraceLoss design.experimentKernel estimator rho.1) ⟨rho, hmem⟩)
  simpa only [lowerAmbientDimension, Nat.add_sub_cancel, worstCaseRisk] using hmean'

/-- The fixed-state probability conclusion, with the proved 11/16 constant. -/
theorem theorem11_probability (D T : ℕ) (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha)
    (design : OperatorDesign D T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin D)))
    [IsMarkovKernel estimator] :
    ∃ rho ∈ spectralDecayClass D alpha L,
      (11 / 16 : ENNReal) ≤ tailProbability design.experimentKernel estimator
        (sharpDecayLowerConstant alpha * spectralDecayMinimaxRate D T L alpha) rho := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, D = k + 2 := ⟨D - 2, by omega⟩
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hT
  let eta := Real.sqrt ((k : ℝ) / T)
  have heta : 0 < eta := Real.sqrt_pos.mpr (div_pos hkpos hTpos)
  obtain ⟨m, hm, hmM, hmval⟩ :=
    (discrete_decayLower_envelope_optimization (lowerEffectiveRankCap (k + 2)) L eta alpha
      (lowerEffectiveRankCap_pos (k + 2) (by omega)) hL heta halpha).2
  have hdimension := lower_hidden_rate_ge_ambient_rate_sharp (k + 2) (T : ℝ) L alpha
    hD hTpos (le_trans zero_le_one hL) halpha
  have hvalue : (33 / 200 : ℝ) * spectralDecayMinimaxRate (k + 2) T L alpha ≤
      decayLowerValue m L eta alpha := by
    have hdimension' : (33 / 100 : ℝ) * spectralDecayMinimaxRate (k + 2) T L alpha ≤
        decayLowerRate (lowerEffectiveRankCap (k + 2)) L eta alpha := by
      simpa only [lowerAmbientDimension, Nat.add_sub_cancel] using hdimension
    linarith
  have hnonneg : 0 ≤ decayLowerValue m L eta alpha := by
    unfold decayLowerValue
    positivity
  have hscaled := mul_le_mul_of_nonneg_left hvalue (hardFamilyScaleConstant_pos alpha).le
  have hmass : 0 ≤ hardFamilyMass m L eta alpha := by
    exact mul_nonneg (hardFamilyScaleConstant_pos alpha).le hnonneg
  have hradius : sharpDecayLowerConstant alpha * spectralDecayMinimaxRate (k + 2) T L alpha ≤
      hardFamilyMass m L eta alpha / 4 := by
    unfold sharpDecayLowerConstant fanoHardMassCoefficient hardFamilyMass
    unfold hardFamilyMass at hmass
    nlinarith only [hscaled, hmass]
  have hkm : 3 * m ≤ k := by
    dsimp [lowerEffectiveRankCap, lowerAmbientDimension] at hmM
    omega
  have hDh : 514 ≤ k + 2 := by omega
  obtain ⟨rho, hrho, htail, _⟩ := per_rank_fixed_state k m T L alpha
    hm hkm hDh hT hL halpha design estimator
  refine ⟨rho, hrho, htail.trans ?_⟩
  apply measure_mono
  intro estimate he
  exact (ENNReal.ofReal_le_ofReal hradius).trans he

/-- Theorem 11 over the minimax domain that includes arbitrary standard
Borel spaces and arbitrary normalized countably additive POVMs. -/
theorem theorem11_minimax {D T : ℕ} (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha) :
    ENNReal.ofReal (sharpDecayLowerConstant alpha * spectralDecayMinimaxRate D T L alpha) ≤
      minimaxRisk (T := T) (spectralDecayClass D alpha L) := by
  apply le_iInf
  intro p
  exact theorem11_expected L alpha hD hT hL halpha p.design p.estimator

end
end TomographyOracleCore.PaperMatch.ExactMain
