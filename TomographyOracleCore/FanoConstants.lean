import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

/-!
# Scalar Fano bookkeeping constants

This module contains only real-number algebra used after an information bound
and an event-to-expectation comparison have been established.  It states no
information-theoretic or tomography theorem.
-/

/-- The usual scalar lower expression in Fano's inequality, with the mutual
information upper bound represented by `information` and the packing
log-cardinality represented by `logCardinality`. -/
noncomputable def fanoErrorLower
    (information logCardinality : ℝ) : ℝ :=
  1 - (information + Real.log 2) / logCardinality

/-- If the information is at most one sixteenth of the log-cardinality and
`logCardinality` is at least four times `log 2`, then the scalar Fano lower
expression is at least `11/16`. -/
theorem fanoErrorLower_ge_eleven_sixteenths
    (information logCardinality : ℝ)
    (hlogCardinality : 0 < logCardinality)
    (hinformation : information ≤ logCardinality / 16)
    (hlogTwo : 4 * Real.log 2 ≤ logCardinality) :
    (11 : ℝ) / 16 ≤ fanoErrorLower information logCardinality := by
  have hlogTwoQuarter : Real.log 2 ≤ logCardinality / 4 := by
    linarith
  have hsum :
      information + Real.log 2 ≤ (5 : ℝ) / 16 * logCardinality := by
    linarith
  have hratio :
      (information + Real.log 2) / logCardinality ≤ (5 : ℝ) / 16 := by
    exact (div_le_iff₀ hlogCardinality).2 hsum
  unfold fanoErrorLower
  linarith

/-- Scalar event-to-expectation conversion.  The premise `hthreshold` is the
already-established fact that loss at least `b/4` on an event of probability
`eventProbability` contributes at least `(b/4) * eventProbability` to the
expected loss. -/
theorem expectedLoss_ge_eleven_mul_b_div_sixty_four
    (b eventProbability expectedLoss : ℝ)
    (hb : 0 ≤ b)
    (hprobability : (11 : ℝ) / 16 ≤ eventProbability)
    (hthreshold : (b / 4) * eventProbability ≤ expectedLoss) :
    11 * b / 64 ≤ expectedLoss := by
  have hbQuarter : 0 ≤ b / 4 := div_nonneg hb (by norm_num)
  calc
    11 * b / 64 = (b / 4) * ((11 : ℝ) / 16) := by ring
    _ ≤ (b / 4) * eventProbability :=
      mul_le_mul_of_nonneg_left hprobability hbQuarter
    _ ≤ expectedLoss := hthreshold

/-- Direct composition of the two scalar bookkeeping steps.  The information
bound and the threshold-to-expectation bridge remain explicit premises. -/
theorem expectedLoss_ge_eleven_mul_b_div_sixty_four_of_fano
    (information logCardinality b expectedLoss : ℝ)
    (hlogCardinality : 0 < logCardinality)
    (hinformation : information ≤ logCardinality / 16)
    (hlogTwo : 4 * Real.log 2 ≤ logCardinality)
    (hb : 0 ≤ b)
    (hthreshold :
      (b / 4) * fanoErrorLower information logCardinality ≤ expectedLoss) :
    11 * b / 64 ≤ expectedLoss := by
  exact expectedLoss_ge_eleven_mul_b_div_sixty_four b
    (fanoErrorLower information logCardinality) expectedLoss hb
    (fanoErrorLower_ge_eleven_sixteenths information logCardinality
      hlogCardinality hinformation hlogTwo)
    hthreshold

end TomographyOracleCore
