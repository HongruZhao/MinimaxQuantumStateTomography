import TomographyOracleCore.PhysicalSharedHaarLowerUnconditional

namespace TomographyOracleCore
open scoped ENNReal
noncomputable section

/-- The actual d>=514 regime loses less than one percent in the rank cap. -/
theorem lowerEffectiveRankCap_ge_85_div_257 (D : ℕ) (hD : 514 ≤ D) :
    (85 / 257 : ℝ) * (D : ℝ) ≤ (lowerEffectiveRankCap D : ℝ) := by
  have hnat : 85 * D ≤ 257 * ((D - 2) / 3) := by omega
  have hr : (85 : ℝ) * (D : ℝ) ≤ 257 * (lowerEffectiveRankCap D : ℝ) := by
    unfold lowerEffectiveRankCap lowerAmbientDimension
    exact_mod_cast hnat
  linarith

theorem hidden_noise_ge_499_div_500 (D : ℕ) (T : ℝ)
    (hD : 514 ≤ D) (hT : 0 < T) :
    (499 / 500 : ℝ) * Real.sqrt ((D : ℝ) / T) ≤
      Real.sqrt ((lowerAmbientDimension D : ℝ) / T) := by
  have hd : (514 : ℝ) ≤ D := by exact_mod_cast hD
  have hk : (lowerAmbientDimension D : ℝ) = (D : ℝ) - 2 := by
    unfold lowerAmbientDimension
    rw [Nat.cast_sub (by omega : 2 ≤ D)]
    norm_num
  have hdim : (499 / 500 : ℝ) ^ 2 * (D : ℝ) ≤ (lowerAmbientDimension D : ℝ) := by
    rw [hk]
    nlinarith
  apply (sq_le_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ (D : ℝ) / T),
    Real.sq_sqrt (by positivity : 0 ≤ (lowerAmbientDimension D : ℝ) / T)]
  have hh := div_le_div_of_nonneg_right hdim hT.le
  convert hh using 1 <;> ring

theorem lower_hidden_rate_ge_ambient_rate_sharp
    (D : ℕ) (T L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 0 < T) (hL : 0 ≤ L)
    (halpha : 1 < alpha) :
    (33 / 100 : ℝ) *
        spectralDecayMinimaxRate D T L alpha ≤
      decayLowerRate (lowerEffectiveRankCap D) L
        (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha := by
  let ambientNoise : ℝ := Real.sqrt ((D : ℝ) / T)
  let hiddenNoise : ℝ :=
    Real.sqrt ((lowerAmbientDimension D : ℝ) / T)
  let q : ℝ := (alpha - 1) / alpha
  let c : ℝ := 33 / 100
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hq1 : q ≤ 1 := by
    dsimp [q]
    exact (div_le_one halpha0).2 (by linarith)
  have hambient0 : 0 ≤ ambientNoise := Real.sqrt_nonneg _
  have hhidden0 : 0 ≤ hiddenNoise := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := by norm_num [c]
  have hc_le_half : c ≤ 1 / 2 := by norm_num [c]
  have hc_le_one : c ≤ 1 := by norm_num [c]
  have hhiddenExact : (499 / 500 : ℝ) * ambientNoise ≤ hiddenNoise := by
    simpa [ambientNoise, hiddenNoise] using hidden_noise_ge_499_div_500 D T hD hT
  have hhiddenHalf : ambientNoise / 2 ≤ hiddenNoise := by linarith
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
  have hM : (85 / 257 : ℝ) * (D : ℝ) ≤ (lowerEffectiveRankCap D : ℝ) :=
    lowerEffectiveRankCap_ge_85_div_257 D hD
  have hendpoint : c * (ambientNoise * (D : ℝ)) ≤
      (lowerEffectiveRankCap D : ℝ) * hiddenNoise := by
    have hprod := mul_le_mul hM hhiddenExact
      (show 0 ≤ (499 / 500 : ℝ) * ambientNoise by positivity)
      (Nat.cast_nonneg (lowerEffectiveRankCap D))
    calc
      c * (ambientNoise * (D : ℝ)) ≤
          ((85 / 257 : ℝ) * (499 / 500)) * (ambientNoise * (D : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num [c]) (by positivity)
      _ = ((85 / 257 : ℝ) * (D : ℝ)) * ((499 / 500 : ℝ) * ambientNoise) := by ring
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

/-- Strengthened lower prefactor, with the same hard family and Fano proof. -/
def sharpDecayLowerConstant (alpha : ℝ) : ℝ :=
  (33 / 100 : ℝ) * (fanoHardMassCoefficient alpha / 2)

theorem sharpDecayLowerConstant_factorization (alpha : ℝ) :
    sharpDecayLowerConstant alpha =
      (fanoHardMassCoefficient alpha / 2) * (33 / 100 : ℝ) := by
  unfold sharpDecayLowerConstant
  ring

theorem sharpDecayLowerConstant_pos (alpha : ℝ) : 0 < sharpDecayLowerConstant alpha := by
  unfold sharpDecayLowerConstant
  exact mul_pos (by norm_num) (div_pos (fanoHardMassCoefficient_pos alpha) (by norm_num))

/-- The lower prefactor improves by exactly (66/25)*sqrt(2), about 3.73. -/
theorem sharpDecayLowerConstant_improvement (alpha : ℝ) :
    sharpDecayLowerConstant alpha = ((66 / 25 : ℝ) * Real.sqrt 2) *
      explicitDecayLowerConstant alpha := by
  unfold sharpDecayLowerConstant explicitDecayLowerConstant fanoHardMassCoefficient
  field_simp
  ring
theorem sharpSpectralDecayRateENNReal_le_of_perRankFanoMass
    (risk : ENNReal) (D : ℕ) (T L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 0 < T) (hL : 1 ≤ L)
    (halpha : 1 < alpha)
    (hperRankFano : ∀ m : ℕ,
      1 ≤ m → m ≤ lowerEffectiveRankCap D →
      ENNReal.ofReal
          (11 * hardFamilyMass m L
            (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha / 64) ≤
        risk) :
    ENNReal.ofReal
        (sharpDecayLowerConstant alpha *
          spectralDecayMinimaxRate D T L alpha) ≤ risk := by
  have hD8 : 8 ≤ D := by omega
  have hM : 1 ≤ lowerEffectiveRankCap D :=
    lowerEffectiveRankCap_pos D hD8
  have hkNat : 0 < lowerAmbientDimension D := by
    unfold lowerAmbientDimension
    omega
  have hkReal : 0 < (lowerAmbientDimension D : ℝ) := by
    exact_mod_cast hkNat
  have heta : 0 < Real.sqrt ((lowerAmbientDimension D : ℝ) / T) :=
    Real.sqrt_pos.2 (div_pos hkReal hT)
  have hprimitive : ∀ m : ℕ,
      1 ≤ m → m ≤ lowerEffectiveRankCap D →
      ENNReal.ofReal
          (fanoHardMassCoefficient alpha *
            decayLowerValue m L
              (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha) ≤
        risk := by
    intro m hm1 hmM
    have hm := hperRankFano m hm1 hmM
    convert hm using 1 <;>
      simp only [fanoHardMassCoefficient, hardFamilyMass] <;> ring
  have hoptimized := decayLowerRateENNReal_le_risk_of_primitive
    risk (fanoHardMassCoefficient alpha) (lowerEffectiveRankCap D) L
    (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha
    hM hL heta halpha (fanoHardMassCoefficient_pos alpha).le hprimitive
  have hdimension := lower_hidden_rate_ge_ambient_rate_sharp D T L alpha
    hD hT (le_trans zero_le_one hL) halpha
  have hreal :
      sharpDecayLowerConstant alpha *
          spectralDecayMinimaxRate D T L alpha ≤
        (fanoHardMassCoefficient alpha / 2) *
          decayLowerRate (lowerEffectiveRankCap D) L
            (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha := by
    calc
      sharpDecayLowerConstant alpha *
          spectralDecayMinimaxRate D T L alpha =
          (fanoHardMassCoefficient alpha / 2) *
            ((33 / 100 : ℝ) *
              spectralDecayMinimaxRate D T L alpha) := by
        rw [sharpDecayLowerConstant_factorization]
        ring
      _ ≤ (fanoHardMassCoefficient alpha / 2) *
          decayLowerRate (lowerEffectiveRankCap D) L
            (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha :=
        mul_le_mul_of_nonneg_left hdimension
          (div_nonneg (fanoHardMassCoefficient_pos alpha).le (by norm_num))
  exact (ENNReal.ofReal_le_ofReal hreal).trans hoptimized

namespace PhysicalRisk
open MatrixReduction
theorem sharpSpectralDecayRateENNReal_le_unrestrictedRisk_of_procedurewiseSharedHaar
    {Orientation : Type*} [MeasurableSpace Orientation]
    [StandardBorelSpace Orientation]
    (D T : ℕ) (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha)
    (hfamily : ∀ m : ℕ,
      1 ≤ m → m ≤ lowerEffectiveRankCap D →
      ProcedurewiseSharedHaarFanoFamily Orientation D T alpha L
        (hardFamilyMass m L
          (Real.sqrt
            ((lowerAmbientDimension D : ℝ) / (T : ℝ))) alpha / 4)) :
    ENNReal.ofReal
        (sharpDecayLowerConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
      unrestrictedRisk D T alpha L := by
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast (show 0 < T by omega)
  apply sharpSpectralDecayRateENNReal_le_of_perRankFanoMass
    (unrestrictedRisk D T alpha L) D (T : ℝ) L alpha
      hD hTreal hL halpha
  intro m hm1 hmcap
  let eta : ℝ :=
    Real.sqrt ((lowerAmbientDimension D : ℝ) / (T : ℝ))
  have heta : 0 ≤ eta := Real.sqrt_nonneg _
  have hmass : 0 ≤ hardFamilyMass m L eta alpha :=
    hardFamilyMass_nonnegative m L eta alpha
      (le_trans zero_le_one hL) heta
  have hradius : 0 ≤ hardFamilyMass m L eta alpha / 4 :=
    div_nonneg hmass (by norm_num)
  have hfano :=
    ofReal_eleven_mul_radius_div_sixteen_le_unrestrictedRisk_of_procedurewiseSharedHaar
      hradius (hfamily m hm1 hmcap)
  simpa only [eta,
    show 11 *
        (hardFamilyMass m L
          (Real.sqrt
            ((lowerAmbientDimension D : ℝ) / (T : ℝ))) alpha / 4) /
          16 =
        11 * hardFamilyMass m L
          (Real.sqrt
            ((lowerAmbientDimension D : ℝ) / (T : ℝ))) alpha /
          64 by ring] using hfano
theorem sharpSpectralDecayRateENNReal_le_unrestrictedRisk
    (D T : ℕ) (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha) :
    ENNReal.ofReal
        (sharpDecayLowerConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
      unrestrictedRisk D T alpha L := by
  let k := lowerAmbientDimension D
  have hD_eq : D = k + 2 := by
    dsimp only [k, lowerAmbientDimension]
    omega
  have hD' : 514 ≤ k + 2 := by omega
  rw [hD_eq]
  apply sharpSpectralDecayRateENNReal_le_unrestrictedRisk_of_procedurewiseSharedHaar
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
