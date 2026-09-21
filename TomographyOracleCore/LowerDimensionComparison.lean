import TomographyOracleCore.ExactTargets
import TomographyOracleCore.DecayLowerAlgebra

namespace TomographyOracleCore

/-!
# From the hidden subspace to the advertised ambient-dimensional rate

The lower construction uses `k = D - 2` hidden coordinates and effective
ranks up to `M = floor(k/3)`.  This file proves the manuscript's final
deterministic comparison with the displayed `D,T` rate.  It contains no
packing, information, Fano, or statistical premise.
-/

/-- Dimension of the hidden subspace in the hard-state construction. -/
def lowerAmbientDimension (D : ℕ) : ℕ := D - 2

/-- Largest effective rank used by the Grassmann packing. -/
def lowerEffectiveRankCap (D : ℕ) : ℕ := lowerAmbientDimension D / 3

theorem lowerAmbientDimension_ge_half
    (D : ℕ) (hD : 8 ≤ D) :
    (D : ℝ) / 2 ≤ (lowerAmbientDimension D : ℝ) := by
  have hnat : D ≤ 2 * (D - 2) := by omega
  have hreal : (D : ℝ) ≤ 2 * ((D - 2 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  unfold lowerAmbientDimension
  linarith

theorem lowerEffectiveRankCap_ge_eighth
    (D : ℕ) (hD : 8 ≤ D) :
    (D : ℝ) / 8 ≤ (lowerEffectiveRankCap D : ℝ) := by
  have hnat : D ≤ 8 * ((D - 2) / 3) := by omega
  have hreal : (D : ℝ) ≤ 8 * (((D - 2) / 3 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  unfold lowerEffectiveRankCap lowerAmbientDimension
  linarith

theorem lowerEffectiveRankCap_pos
    (D : ℕ) (hD : 8 ≤ D) :
    1 ≤ lowerEffectiveRankCap D := by
  unfold lowerEffectiveRankCap lowerAmbientDimension
  omega

/-- The hidden-coordinate sampling noise loses at most `sqrt 2` relative to
the ambient-dimensional sampling noise. -/
theorem ambient_noise_div_sqrt_two_le_hidden_noise
    (D : ℕ) (T : ℝ) (hD : 8 ≤ D) (hT : 0 < T) :
    Real.sqrt ((D : ℝ) / T) / Real.sqrt 2 ≤
      Real.sqrt ((lowerAmbientDimension D : ℝ) / T) := by
  let ambientNoise : ℝ := Real.sqrt ((D : ℝ) / T)
  let hiddenNoise : ℝ :=
    Real.sqrt ((lowerAmbientDimension D : ℝ) / T)
  have hD0 : 0 ≤ (D : ℝ) := Nat.cast_nonneg D
  have hk0 : 0 ≤ (lowerAmbientDimension D : ℝ) := Nat.cast_nonneg _
  have hambientQuot : 0 ≤ (D : ℝ) / T := div_nonneg hD0 hT.le
  have hhiddenQuot : 0 ≤ (lowerAmbientDimension D : ℝ) / T :=
    div_nonneg hk0 hT.le
  have hhalf := lowerAmbientDimension_ge_half D hD
  have hquotHalf : ((D : ℝ) / T) / 2 ≤
      (lowerAmbientDimension D : ℝ) / T := by
    calc
      ((D : ℝ) / T) / 2 = ((D : ℝ) / 2) / T := by ring
      _ ≤ (lowerAmbientDimension D : ℝ) / T :=
        div_le_div_of_nonneg_right hhalf hT.le
  have hambientSq : ambientNoise ^ 2 = (D : ℝ) / T := by
    dsimp [ambientNoise]
    exact Real.sq_sqrt hambientQuot
  have hhiddenSq : hiddenNoise ^ 2 =
      (lowerAmbientDimension D : ℝ) / T := by
    dsimp [hiddenNoise]
    exact Real.sq_sqrt hhiddenQuot
  have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsquare : ambientNoise ^ 2 ≤
      (Real.sqrt 2 * hiddenNoise) ^ 2 := by
    rw [mul_pow, hsqrtSq, hambientSq, hhiddenSq]
    nlinarith
  have hambient0 : 0 ≤ ambientNoise := Real.sqrt_nonneg _
  have hproduct0 : 0 ≤ Real.sqrt 2 * hiddenNoise :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hproduct : ambientNoise ≤ Real.sqrt 2 * hiddenNoise :=
    (sq_le_sq₀ hambient0 hproduct0).mp hsquare
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  apply (div_le_iff₀ hsqrtPos).2
  simpa [ambientNoise, hiddenNoise, mul_comm] using hproduct

/-- Before the discrete factor `1/2`, the hidden-dimensional three-regime
rate is at least `1/(8 sqrt 2)` of the advertised ambient-dimensional rate. -/
theorem lower_hidden_rate_ge_ambient_rate
    (D : ℕ) (T L alpha : ℝ)
    (hD : 8 ≤ D) (hT : 0 < T) (hL : 0 ≤ L)
    (halpha : 1 < alpha) :
    (1 / (8 * Real.sqrt 2)) *
        spectralDecayMinimaxRate D T L alpha ≤
      decayLowerRate (lowerEffectiveRankCap D) L
        (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha := by
  let ambientNoise : ℝ := Real.sqrt ((D : ℝ) / T)
  let hiddenNoise : ℝ :=
    Real.sqrt ((lowerAmbientDimension D : ℝ) / T)
  let q : ℝ := (alpha - 1) / alpha
  let c : ℝ := 1 / (8 * Real.sqrt 2)
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (div_le_one halpha0).2 (by linarith)
  have hambient0 : 0 ≤ ambientNoise := Real.sqrt_nonneg _
  have hhidden0 : 0 ≤ hiddenNoise := Real.sqrt_nonneg _
  have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsqrtOne : 1 ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsqrtTwo : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hc_le_half : c ≤ 1 / 2 := by
    dsimp [c]
    rw [div_le_iff₀ (mul_pos (by norm_num) hsqrtPos)]
    nlinarith
  have hc_le_one : c ≤ 1 := hc_le_half.trans (by norm_num)
  have hhiddenExact : ambientNoise / Real.sqrt 2 ≤ hiddenNoise := by
    simpa [ambientNoise, hiddenNoise] using
      ambient_noise_div_sqrt_two_le_hidden_noise D T hD hT
  have hambientDiv : ambientNoise / 2 ≤ ambientNoise / Real.sqrt 2 := by
    apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hsqrtPos).2
    exact mul_le_mul_of_nonneg_left hsqrtTwo hambient0
  have hhiddenHalf : ambientNoise / 2 ≤ hiddenNoise :=
    hambientDiv.trans hhiddenExact
  have hhalfPow : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ q := by
    exact Real.self_le_rpow_of_le_one (by norm_num) (by norm_num) hq1
  have hnoisePowHalf : ambientNoise ^ q / 2 ≤ hiddenNoise ^ q := by
    have hmulPow : ambientNoise ^ q / 2 ≤ (ambientNoise / 2) ^ q := by
      calc
        ambientNoise ^ q / 2 = ambientNoise ^ q * (1 / 2 : ℝ) := by ring
        _ ≤ ambientNoise ^ q * (1 / 2 : ℝ) ^ q :=
          mul_le_mul_of_nonneg_left hhalfPow
            (Real.rpow_nonneg hambient0 q)
        _ = (ambientNoise * (1 / 2 : ℝ)) ^ q := by
          rw [Real.mul_rpow hambient0 (by norm_num : (0 : ℝ) ≤ 1 / 2)]
        _ = (ambientNoise / 2) ^ q := by ring
    exact hmulPow.trans
      (Real.rpow_le_rpow (div_nonneg hambient0 (by norm_num))
        hhiddenHalf hq0)
  have hpolyD0 : 0 ≤ L ^ alpha⁻¹ * ambientNoise ^ q :=
    mul_nonneg (Real.rpow_nonneg hL _) (Real.rpow_nonneg hambient0 _)
  have hpolyHalf :
      (L ^ alpha⁻¹ * ambientNoise ^ q) / 2 ≤
        L ^ alpha⁻¹ * hiddenNoise ^ q := by
    calc
      (L ^ alpha⁻¹ * ambientNoise ^ q) / 2 =
          L ^ alpha⁻¹ * (ambientNoise ^ q / 2) := by ring
      _ ≤ L ^ alpha⁻¹ * hiddenNoise ^ q :=
        mul_le_mul_of_nonneg_left hnoisePowHalf
          (Real.rpow_nonneg hL _)
  have hM : (D : ℝ) / 8 ≤ (lowerEffectiveRankCap D : ℝ) :=
    lowerEffectiveRankCap_ge_eighth D hD
  have hendpoint :
      c * (ambientNoise * (D : ℝ)) ≤
        (lowerEffectiveRankCap D : ℝ) * hiddenNoise := by
    have hprod := mul_le_mul hM hhiddenExact
      (div_nonneg hambient0 hsqrtPos.le)
      (Nat.cast_nonneg (lowerEffectiveRankCap D))
    calc
      c * (ambientNoise * (D : ℝ)) =
          ((D : ℝ) / 8) * (ambientNoise / Real.sqrt 2) := by
        dsimp [c]
        ring
      _ ≤ (lowerEffectiveRankCap D : ℝ) * hiddenNoise := hprod
  have hrate0 : 0 ≤ decayUpperRate D L ambientNoise alpha := by
    unfold decayUpperRate
    apply le_min zero_le_one
    apply le_min hpolyD0
    exact mul_nonneg hambient0 (Nat.cast_nonneg D)
  have hrateOne : decayUpperRate D L ambientNoise alpha ≤ 1 :=
    min_le_left _ _
  have hratePoly : decayUpperRate D L ambientNoise alpha ≤
      L ^ alpha⁻¹ * ambientNoise ^ q := by
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hrateEndpoint : decayUpperRate D L ambientNoise alpha ≤
      ambientNoise * (D : ℝ) := by
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hcomparison :
      c * decayUpperRate D L ambientNoise alpha ≤
        decayLowerRate (lowerEffectiveRankCap D) L hiddenNoise alpha := by
    unfold decayLowerRate
    apply le_min
    · calc
        c * decayUpperRate D L ambientNoise alpha ≤
            1 * decayUpperRate D L ambientNoise alpha :=
          mul_le_mul_of_nonneg_right hc_le_one hrate0
        _ = decayUpperRate D L ambientNoise alpha := one_mul _
        _ ≤ 1 := hrateOne
    · apply le_min
      · calc
          c * decayUpperRate D L ambientNoise alpha ≤
              c * (L ^ alpha⁻¹ * ambientNoise ^ q) :=
            mul_le_mul_of_nonneg_left hratePoly hc0
          _ ≤ (L ^ alpha⁻¹ * ambientNoise ^ q) / 2 := by
            calc
              c * (L ^ alpha⁻¹ * ambientNoise ^ q) ≤
                  (1 / 2 : ℝ) * (L ^ alpha⁻¹ * ambientNoise ^ q) :=
                mul_le_mul_of_nonneg_right hc_le_half hpolyD0
              _ = _ := by ring
          _ ≤ L ^ alpha⁻¹ * hiddenNoise ^ q := hpolyHalf
      · calc
          c * decayUpperRate D L ambientNoise alpha ≤
              c * (ambientNoise * (D : ℝ)) :=
            mul_le_mul_of_nonneg_left hrateEndpoint hc0
          _ ≤ (lowerEffectiveRankCap D : ℝ) * hiddenNoise := hendpoint
  rw [spectralDecayMinimaxRate,
    ← decayUpperRate_sqrt_dimension_div_samples D T L alpha hT
      halpha0.ne']
  simpa [ambientNoise, hiddenNoise, q, c] using hcomparison

end TomographyOracleCore
