import TomographyOracleCore.PhysicalLossBounds
import TomographyOracleCore.PhysicalTargets

namespace TomographyOracleCore

open MatrixReduction
open scoped ENNReal

/-!
# The small-sample branch of the physical upper bound

When the sample size is at most a fixed multiple of the dimension, every
term in the three-regime target rate is bounded below by the reciprocal of
that multiple.  The deterministic trace-loss cap therefore supplies the
upper bound with one constant estimator, independently of `alpha` and `L`.
-/

/-- In the small-sample regime, the exact three-regime rate is bounded below
by `1 / C`.  The deliberately loose reciprocal is convenient because it is
uniform in the decay exponent. -/
theorem one_div_le_spectralDecayMinimaxRate_of_samples_le
    (D T : ℕ) (alpha L C : ℝ)
    (hD : 1 ≤ D) (hT : 0 < T) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hC : 1 ≤ C) (hsmall : (T : ℝ) ≤ C * (D : ℝ)) :
    1 / C ≤ spectralDecayMinimaxRate D (T : ℝ) L alpha := by
  let eta : ℝ := Real.sqrt ((D : ℝ) / (T : ℝ))
  let q : ℝ := (alpha - 1) / alpha
  let c : ℝ := 1 / C
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hTreal : 0 < (T : ℝ) := by exact_mod_cast hT
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact (one_div_le_one_div_of_le zero_lt_one hC).trans_eq (one_div_one : (1 / (1 : ℝ) = 1))
  have hquot0 : 0 ≤ (D : ℝ) / (T : ℝ) := by positivity
  have hcquot : c ≤ (D : ℝ) / (T : ℝ) := by
    dsimp [c]
    apply (div_le_div_iff₀ hCpos hTreal).2
    simpa [mul_comm] using hsmall
  have hcsq : c ^ 2 ≤ c := by nlinarith
  have hceta : c ≤ eta := by
    dsimp [eta]
    exact (Real.le_sqrt hc0 hquot0).2 (hcsq.trans hcquot)
  have heta0 : 0 ≤ eta := Real.sqrt_nonneg _
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (div_le_one halpha0).2 (by linarith)
  have hetaPow : c ≤ eta ^ q := by
    by_cases heta1 : eta ≤ 1
    · exact hceta.trans
        (Real.self_le_rpow_of_le_one heta0 heta1 hq1)
    · have honeeta : 1 ≤ eta := le_of_not_ge heta1
      exact hc1.trans (Real.one_le_rpow honeeta hq0)
  have hLpow : 1 ≤ L ^ alpha⁻¹ := by
    exact Real.one_le_rpow hL (inv_nonneg.mpr halpha0.le)
  have hpoly : c ≤ L ^ alpha⁻¹ * eta ^ q := by
    calc
      c ≤ eta ^ q := hetaPow
      _ = 1 * eta ^ q := by ring
      _ ≤ L ^ alpha⁻¹ * eta ^ q :=
        mul_le_mul_of_nonneg_right hLpow (Real.rpow_nonneg heta0 q)
  have hendpoint : c ≤ eta * (D : ℝ) := by
    calc
      c ≤ eta := hceta
      _ = eta * 1 := by ring
      _ ≤ eta * (D : ℝ) :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hD) heta0
  rw [spectralDecayMinimaxRate,
    ← decayUpperRate_sqrt_dimension_div_samples D (T : ℝ) L alpha
      hTreal halpha0.ne']
  change c ≤ decayUpperRate D L eta alpha
  unfold decayUpperRate
  exact le_min hc1 (le_min hpoly hendpoint)

namespace PhysicalRisk

/-- For small samples, a single constant estimator attains the exact target
rate simultaneously for every admissible spectral-decay class. -/
theorem simultaneousPhysicalUpper_of_samples_le
    (D T : ℕ) (design : Design D T) (C : ℝ)
    (hD : 1 ≤ D) (hT : 0 < T) (hC : 1 ≤ C)
    (hsmall : (T : ℝ) ≤ C * (D : ℝ)) :
    SimultaneousPhysicalUpper D T design (fun _ ↦ 2 * C) := by
  let i₀ : Fin D := ⟨0, by omega⟩
  let anchor : DensityOperator (Fin D) := DensityGrid.basisDensityOperator i₀
  refine ⟨constantEstimator anchor, ?_⟩
  intro alpha L halpha hL
  have hrate := one_div_le_spectralDecayMinimaxRate_of_samples_le
    D T alpha L C hD hT halpha hL hC hsmall
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCrate : 1 ≤ C * spectralDecayMinimaxRate D (T : ℝ) L alpha := by
    calc
      1 = C * (1 / C) := by field_simp
      _ ≤ C * spectralDecayMinimaxRate D (T : ℝ) L alpha :=
        mul_le_mul_of_nonneg_left hrate hCpos.le
  have hreal : (2 : ℝ) ≤
      (2 * C) * spectralDecayMinimaxRate D (T : ℝ) L alpha := by
    nlinarith
  calc
    classWorstCaseRisk D T alpha L design (constantEstimator anchor) ≤ 2 :=
      classWorstCaseRisk_le_two design (constantEstimator anchor)
    _ ≤ ENNReal.ofReal
        ((2 * C) * spectralDecayMinimaxRate D (T : ℝ) L alpha) := by
      rw [← ENNReal.ofReal_ofNat]
      exact ENNReal.ofReal_le_ofReal hreal

end PhysicalRisk

end TomographyOracleCore
