import TomographyOracleCore.SharedHaarLowerEndpoint
import TomographyOracleCore.GrassmannHardFamilyUnconditional
import TomographyOracleCore.PhysicalHaarOneCopyDesignKL
import TomographyOracleCore.GrassmannThreshold
import TomographyOracleCore.LowerInformationAlgebra

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

/-!
# Unconditional shared-Haar physical lower bound

This module closes the two former premises of the optimized physical lower
endpoint.  The premise-free Grassmann construction supplies the finite hard
family, while the arbitrary-standard-Borel one-copy theorem supplies every
shot budget for every public-seed randomized nonadaptive design.
-/

/-- The manuscript hard-family mass is strictly positive when the rank,
decay radius, and sampling scale are positive. -/
theorem hardFamilyMass_pos
    (m : ℕ) (L eta alpha : ℝ)
    (hm : 1 ≤ m) (hL : 0 < L) (heta : 0 < eta) :
    0 < hardFamilyMass m L eta alpha := by
  unfold hardFamilyMass decayLowerValue
  apply mul_pos (hardFamilyScaleConstant_pos alpha)
  apply lt_min zero_lt_one
  apply lt_min
  · exact mul_pos hL (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
  · exact mul_pos (by exact_mod_cast hm) heta

namespace PhysicalRisk

/-- At one admissible effective rank, the premise-free Grassmann packing and
the arbitrary-standard-Borel Haar one-copy KL bound construct the exact
procedurewise shared-Haar Fano family consumed by the lower endpoint. -/
theorem procedurewiseSharedHaarFanoFamily_orientedHardProjector
    (k m T : ℕ) (L alpha : ℝ)
    (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hD : 514 ≤ k + 2) (hT : 1 ≤ T)
    (hL : 1 ≤ L) (halpha : 1 < alpha) :
    ProcedurewiseSharedHaarFanoFamily
      (unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
      (k + 2) T alpha L
      (hardFamilyMass m L
        (Real.sqrt ((k : ℝ) / (T : ℝ))) alpha / 4) := by
  intro design estimator
  let b := hardFamilyMass m L
    (Real.sqrt ((k : ℝ) / (T : ℝ))) alpha
  have hk1 : 1 ≤ k := by omega
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast hT
  have hkpos : 0 < (k : ℝ) := by
    exact_mod_cast (show 0 < k by omega)
  have heta : 0 < Real.sqrt ((k : ℝ) / (T : ℝ)) :=
    Real.sqrt_pos.2 (div_pos hkpos hTpos)
  have hbpos : 0 < b := by
    exact hardFamilyMass_pos m L _ alpha hm
      (lt_of_lt_of_le zero_lt_one hL) heta
  have hb0 : 0 ≤ b := hbpos.le
  have hbquarter : b ≤ 1 / 4 := by
    exact hardFamilyMass_le_quarter m L _ alpha
  have hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha) := by
    exact hardFamilyMass_le_decay_scale m L _ alpha
      (le_trans zero_le_one hL)
  obtain ⟨W, _hWcard⟩ :=
    exists_complexGrassmannPackingWitness_card_eq hm hkm
  let state : Fin W.card →
      unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) →
      DensityOperator (Fin (k + 2)) := fun a U ↦
    orientedHardProjectorDensityOperator U (W.projector a) b hm hb0 hbquarter
  let reference :
      unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) →
      DensityOperator (Fin (k + 2)) :=
    orientedHardReferenceDensityOperator k b hk1 hb0 hbquarter
  let budget : Fin T → ENNReal := fun _ ↦
    ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ)))
  have hstate : ∀ a, Measurable (state a) := fun a ↦ by
    simpa only [state] using
      measurable_orientedHardProjectorDensityOperator
        (W.projector a) b hm hb0 hbquarter
  have hreference : Measurable reference := by
    simpa only [reference] using
      measurable_orientedHardReferenceDensityOperator
        k b hk1 hb0 hbquarter
  have hlogTwo : 4 * Real.log 2 ≤ Real.log (W.card : ℝ) := by
    exact (four_log_two_le_grassmann_exponent (k + 2) m hD hm).trans
      (by simpa [lowerAmbientDimension, grassmannGamma0] using
        W.log_cardinality_lower)
  have hN : 2 ≤ W.card := by
    have hlogpos : 0 < Real.log (W.card : ℝ) :=
      (mul_pos (by norm_num) (Real.log_pos (by norm_num))).trans_le hlogTwo
    have hcardone : 1 < (W.card : ℝ) :=
      (Real.log_pos_iff (by positivity)).mp hlogpos
    exact_mod_cast hcardone
  refine ⟨W.card, hN, unitaryHaarProbability (k + 2), inferInstance,
    state, reference, hstate, hreference, ?_, ?_, budget, ?_, ?_, ?_, hlogTwo⟩
  · intro U a
    exact orientedHardProjectorDensityOperator_mem_spectralDecayClass
      U (W.projector a) alpha L b hm halpha hL hb0 hbquarter hbscaled
  · intro U a c hac
    have hsep :=
      orientedHardProjectorDensityOperator_traceDistance_ge_half_mass
        U (W.projector c) (W.projector a) b hm hb0 hbquarter
          (W.pairwise_separated c a hac.symm)
    simpa only [state, realHermitianTraceLoss]
      using (show 2 * (b / 4) ≤
        hermitianTraceNorm
          ((orientedHardProjectorDensityOperator U (W.projector c) b hm hb0 hbquarter).matrix -
           (orientedHardProjectorDensityOperator U (W.projector a) b hm hb0 hbquarter).matrix)
          ((orientedHardProjectorDensityOperator U (W.projector c) b hm hb0 hbquarter).sub_isHermitian
           (orientedHardProjectorDensityOperator U (W.projector a) b hm hb0 hbquarter)) by
             convert hsep using 1 <;> ring)
  · simpa [budget, Finset.sum_const, nsmul_eq_mul] using
      (ENNReal.mul_ne_top (show (T : ENNReal) ≠ ∞ by simp)
        (show ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ))) ≠ ∞ by simp))
  · intro a t
    simpa only [state, reference, budget] using
      (PhysicalPOVM.RandomizedNonadaptiveDesign.klDiv_sharedOrientationShotKernel_orientedHardProjector_le
        design (W.projector a) b hm hk1 hbpos hbquarter t)
  · have hconst : 0 ≤ 8 * b ^ 2 / (3 * (m : ℝ)) := by positivity
    have hscalar :=
      hardFamilyMass_informationRadius_le_logCardinality_div_sixteen
        m L alpha (k : ℝ) (T : ℝ) (Real.log (W.card : ℝ)) hm
          (le_trans zero_le_one hL) hkpos hTpos
          (by simpa only [grassmannGamma0] using W.log_cardinality_lower)
    simpa only [b, budget, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_natCast, ENNReal.toReal_ofReal hconst] using hscalar

/-- Unconditional optimized physical minimax lower bound with the exact
quantifiers and constant of the former procedurewise shared-Haar endpoint. -/
theorem explicitSpectralDecayRateENNReal_le_unrestrictedRisk
    (D T : ℕ) (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha) :
    ENNReal.ofReal
        (explicitDecayLowerConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
      unrestrictedRisk D T alpha L := by
  let k := lowerAmbientDimension D
  have hD_eq : D = k + 2 := by
    dsimp only [k, lowerAmbientDimension]
    omega
  have hD' : 514 ≤ k + 2 := by omega
  rw [hD_eq]
  apply explicitSpectralDecayRateENNReal_le_unrestrictedRisk_of_procedurewiseSharedHaar
    (Orientation := unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (k + 2) T L alpha hD' hT hL halpha
  intro m hm hmcap
  have hmcap' : m ≤ k / 3 := by
    simpa [lowerEffectiveRankCap, lowerAmbientDimension] using hmcap
  have hkm : 3 * m ≤ k := by omega
  simpa only [lowerAmbientDimension, Nat.add_sub_cancel] using
    (procedurewiseSharedHaarFanoFamily_orientedHardProjector
      k m T L alpha hm hkm hD' hT hL halpha)

end PhysicalRisk

end

end TomographyOracleCore
