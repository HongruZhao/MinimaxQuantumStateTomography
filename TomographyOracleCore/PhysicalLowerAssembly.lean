import TomographyOracleCore.LowerConstantAssembly
import TomographyOracleCore.LowerDimensionComparison
import TomographyOracleCore.PhysicalTargets

namespace TomographyOracleCore

open scoped ENNReal

/-!
# Physical lower-bound assembly

These lemmas transport the proved integer effective-rank optimization into
the `ENNReal` risk used by the physical experiment.  They make no packing or
information assertion.  In particular, a per-rank premise below is an open
proof obligation, not an admissible endpoint axiom.
-/

/-- `ENNReal` version of the discrete effective-rank optimization: a genuine
per-rank lower estimate implies the optimized three-regime lower estimate. -/
theorem decayLowerRateENNReal_le_risk_of_primitive
    (risk : ENNReal) (lowerConstant : ℝ)
    (M : ℕ) (L eta alpha : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (heta : 0 < eta)
    (halpha : 1 < alpha) (hlowerConstant : 0 ≤ lowerConstant)
    (hprimitive : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ENNReal.ofReal
          (lowerConstant * decayLowerValue m L eta alpha) ≤ risk) :
    ENNReal.ofReal
        ((lowerConstant / 2) * decayLowerRate M L eta alpha) ≤ risk := by
  rcases (discrete_decayLower_envelope_optimization M L eta alpha
    hM hL heta halpha).2 with ⟨m, hm1, hmM, hm⟩
  apply (ENNReal.ofReal_le_ofReal ?_).trans (hprimitive m hm1 hmM)
  calc
    (lowerConstant / 2) * decayLowerRate M L eta alpha =
        lowerConstant * (decayLowerRate M L eta alpha / 2) := by ring
    _ ≤ lowerConstant * decayLowerValue m L eta alpha :=
      mul_le_mul_of_nonneg_left hm hlowerConstant

/-- If the genuine per-rank Fano proof supplies the `11 b / 64` estimate,
then the explicit paper constant and all integer optimization are discharged
for the physical `ENNReal` risk. -/
theorem explicitDecayLowerRateENNReal_le_of_perRankFanoMass
    (risk : ENNReal) (M : ℕ) (L eta alpha : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (heta : 0 < eta)
    (halpha : 1 < alpha)
    (hperRankFano : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      ENNReal.ofReal
          (11 * hardFamilyMass m L eta alpha / 64) ≤ risk) :
    ENNReal.ofReal
        ((explicitDecayLowerConstant alpha / 2) *
          decayLowerRate M L eta alpha) ≤ risk := by
  apply decayLowerRateENNReal_le_risk_of_primitive risk
    (explicitDecayLowerConstant alpha) M L eta alpha
    hM hL heta halpha (explicitDecayLowerConstant_pos alpha).le
  intro m hm1 hmM
  apply (ENNReal.ofReal_le_ofReal ?_).trans (hperRankFano m hm1 hmM)
  exact explicitDecayLowerConstant_mul_value_le_of_fanoMass
    m L eta alpha (11 * hardFamilyMass m L eta alpha / 64)
    (le_trans zero_le_one hL) heta.le le_rfl

/-- Exact manuscript rate and constant after setting `k = D - 2` and
`M = floor(k/3)`.  Thus the only remaining premise is the genuine per-rank
Fano estimate; the discrete optimization, dimension comparison, and all
displayed constants are proved internally. -/
theorem explicitSpectralDecayRateENNReal_le_of_perRankFanoMass
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
        (explicitDecayLowerConstant alpha *
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
  have hdimension := lower_hidden_rate_ge_ambient_rate D T L alpha
    hD8 hT (le_trans zero_le_one hL) halpha
  have hreal :
      explicitDecayLowerConstant alpha *
          spectralDecayMinimaxRate D T L alpha ≤
        (fanoHardMassCoefficient alpha / 2) *
          decayLowerRate (lowerEffectiveRankCap D) L
            (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha := by
    calc
      explicitDecayLowerConstant alpha *
          spectralDecayMinimaxRate D T L alpha =
          (fanoHardMassCoefficient alpha / 2) *
            ((1 / (8 * Real.sqrt 2)) *
              spectralDecayMinimaxRate D T L alpha) := by
        rw [explicitDecayLowerConstant_factorization]
        ring
      _ ≤ (fanoHardMassCoefficient alpha / 2) *
          decayLowerRate (lowerEffectiveRankCap D) L
            (Real.sqrt ((lowerAmbientDimension D : ℝ) / T)) alpha :=
        mul_le_mul_of_nonneg_left hdimension
          (div_nonneg (fanoHardMassCoefficient_pos alpha).le (by norm_num))
  exact (ENNReal.ofReal_le_ofReal hreal).trans hoptimized

end TomographyOracleCore
