import TomographyOracleCore.FanoConstants
import TomographyOracleCore.HardMass

namespace TomographyOracleCore

/-!
# Lower-bound constant assembly

This file connects the explicit constant printed in the minimax theorem to
the hard-family mass and the scalar Fano bookkeeping.  It contains no
packing, information, or minimax premise: the sole input to the final lemma
is the lower estimate already obtained from those earlier proof layers.
-/

/-- Coefficient produced directly by the `11/16` Fano error probability and
the `b/4` loss threshold. -/
noncomputable def fanoHardMassCoefficient (alpha : ℝ) : ℝ :=
  11 * hardFamilyScaleConstant alpha / 64

theorem fanoHardMassCoefficient_pos (alpha : ℝ) :
    0 < fanoHardMassCoefficient alpha := by
  unfold fanoHardMassCoefficient
  exact div_pos
    (mul_pos (by norm_num) (hardFamilyScaleConstant_pos alpha))
    (by norm_num)

/-- Exact factorization of the published constant into the Fano coefficient,
the discrete factor `1/2`, and the ambient-dimension factor
`1/(8 sqrt 2)`. -/
theorem explicitDecayLowerConstant_factorization (alpha : ℝ) :
    explicitDecayLowerConstant alpha =
      (fanoHardMassCoefficient alpha / 2) *
        (1 / (8 * Real.sqrt 2)) := by
  unfold explicitDecayLowerConstant fanoHardMassCoefficient
  ring

/-- The displayed minimax constant is no larger than the coefficient obtained
by multiplying the hard-family mass by the `11/64` Fano factor. -/
theorem explicitDecayLowerConstant_le_fanoMassCoefficient (alpha : ℝ) :
    explicitDecayLowerConstant alpha ≤
      fanoHardMassCoefficient alpha := by
  have hsqrt0 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hsqrt1 : 1 ≤ Real.sqrt 2 := by
    have hsquare : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
      Real.sq_sqrt (by norm_num)
    have hsqrtnonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith
  have hscale0 : 0 ≤ hardFamilyScaleConstant alpha :=
    (hardFamilyScaleConstant_pos alpha).le
  unfold explicitDecayLowerConstant fanoHardMassCoefficient
  have hden : (64 : ℝ) ≤ 1024 * Real.sqrt 2 := by
    nlinarith
  gcongr

/-- Any `11 b / 64` lower estimate at the chosen hard mass implies the
published per-rank lower estimate with `explicitDecayLowerConstant`. -/
theorem explicitDecayLowerConstant_mul_value_le_of_fanoMass
    (m : ℕ) (L eta alpha expectedLoss : ℝ)
    (hL : 0 ≤ L) (heta : 0 ≤ eta)
    (hfano : 11 * hardFamilyMass m L eta alpha / 64 ≤ expectedLoss) :
    explicitDecayLowerConstant alpha *
        decayLowerValue m L eta alpha ≤ expectedLoss := by
  have hvalue : 0 ≤ decayLowerValue m L eta alpha :=
    decayLowerValue_nonnegative m L eta alpha hL heta
  calc
    explicitDecayLowerConstant alpha * decayLowerValue m L eta alpha
        ≤ fanoHardMassCoefficient alpha *
            decayLowerValue m L eta alpha :=
      mul_le_mul_of_nonneg_right
        (explicitDecayLowerConstant_le_fanoMassCoefficient alpha) hvalue
    _ = 11 * hardFamilyMass m L eta alpha / 64 := by
      unfold fanoHardMassCoefficient hardFamilyMass
      ring
    _ ≤ expectedLoss := hfano

/-- Direct scalar composition from the Fano information hypotheses to the
published per-rank constant.  The remaining `hthreshold` premise is precisely
the event-to-risk bridge, not a minimax conclusion. -/
theorem explicitDecayLowerConstant_mul_value_le_of_fano
    (m : ℕ) (L eta alpha information logCardinality expectedLoss : ℝ)
    (hL : 0 ≤ L) (heta : 0 ≤ eta)
    (hlogCardinality : 0 < logCardinality)
    (hinformation : information ≤ logCardinality / 16)
    (hlogTwo : 4 * Real.log 2 ≤ logCardinality)
    (hthreshold :
      (hardFamilyMass m L eta alpha / 4) *
          fanoErrorLower information logCardinality ≤ expectedLoss) :
    explicitDecayLowerConstant alpha *
        decayLowerValue m L eta alpha ≤ expectedLoss := by
  apply explicitDecayLowerConstant_mul_value_le_of_fanoMass
    m L eta alpha expectedLoss hL heta
  exact expectedLoss_ge_eleven_mul_b_div_sixty_four_of_fano
    information logCardinality (hardFamilyMass m L eta alpha) expectedLoss
    hlogCardinality hinformation hlogTwo
    (hardFamilyMass_nonnegative m L eta alpha hL heta) hthreshold

end TomographyOracleCore
