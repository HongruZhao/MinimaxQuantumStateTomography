import TomographyOracleCore.FiniteUnitaryProjectiveScore

/-!
# Third-overlap bridge for finite-unitary projective scores

This module isolates the exact positive third-moment scalar consumed by the
shallow-design variance argument. The weighted overlap square is the Born
average of `Tr(P_u P)^2`. A bound by twice its worst-case Haar value implies
the calibrated score second-moment constant `13`.
-/

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ComplexOrder InnerProductSpace ENNReal

noncomputable section

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- The positive degree-three overlap polynomial appearing in the Born
second moment of a finite-unitary projective measurement. -/
noncomputable def finiteUnitaryProjectiveWeightedOverlapSquare
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : E, ∑ b : Fin D,
      ((haarDirectionProjector u *
        finiteUnitaryMeasurementProjector (U e) b).trace.re) ^ 2 *
      (ρ.matrix * finiteUnitaryMeasurementProjector (U e) b).trace.re

/-- Elementary positivity converts the full calibrated-score square into its
positive cubic overlap term plus the normalized Born mass. -/
theorem finiteUnitaryProjectiveScoreSecondMoment_le_weightedOverlapSquare
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    finiteUnitaryProjectiveScoreSecondMoment U ρ u ≤
      ((D + 1 : ℕ) : ℝ) ^ 2 *
        finiteUnitaryProjectiveWeightedOverlapSquare U ρ u + 1 := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let ccard : ℝ := ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal
  let cdim : ℝ := ((D + 1 : ℕ) : ℝ)
  let a : E → Fin D → ℝ := fun e b ↦
    (haarDirectionProjector u *
      finiteUnitaryMeasurementProjector (U e) b).trace.re
  let w : E → Fin D → ℝ := fun e b ↦
    (ρ.matrix * finiteUnitaryMeasurementProjector (U e) b).trace.re
  have hccard : 0 ≤ ccard := ENNReal.toReal_nonneg
  have hcdim : 0 ≤ cdim := by positivity
  have hw : ∀ e b, 0 ≤ w e b := by
    intro e b
    exact trace_mul_re_nonnegative_of_posSemidef ρ.matrix
      (finiteUnitaryMeasurementProjector (U e) b)
      ρ.posSemidef
      (finiteUnitaryMeasurementProjector_posSemidef (U e) b)
  have ha : ∀ e b, 0 ≤ a e b := by
    intro e b
    exact trace_mul_re_nonnegative_of_posSemidef
      (haarDirectionProjector u)
      (finiteUnitaryMeasurementProjector (U e) b)
      (haarDirectionProjector_posSemidef u)
      (finiteUnitaryMeasurementProjector_posSemidef (U e) b)
  have hterm : ∀ e b,
      (cdim * a e b - 1) ^ 2 * w e b ≤
        (cdim ^ 2 * (a e b) ^ 2 + 1) * w e b := by
    intro e b
    apply mul_le_mul_of_nonneg_right _ (hw e b)
    nlinarith [mul_nonneg hcdim (ha e b)]
  have hsum :
      ∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) ^ 2 * w e b ≤
        ∑ e : E, ∑ b : Fin D,
          (cdim ^ 2 * (a e b) ^ 2 + 1) * w e b := by
    apply Finset.sum_le_sum
    intro e he
    exact Finset.sum_le_sum fun b hb ↦ hterm e b
  have hweight : (∑ e : E, ∑ b : Fin D, w e b) =
      (Fintype.card E : ℝ) := by
    simpa [w] using
      sum_finiteUnitaryMeasurementProjector_ensemble_bornWeight U ρ
  have hcard : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hnormalize : ccard * (Fintype.card E : ℝ) = 1 := by
    dsimp [ccard]
    simp [ENNReal.toReal_inv, hcard]
  unfold finiteUnitaryProjectiveScoreSecondMoment
    finiteUnitaryProjectiveWeightedOverlapSquare
    finiteUnitaryProjectiveScore haarCalibratedRankOneScore
  simp only [Fintype.card_fin, smul_eq_mul]
  change ccard *
      (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) ^ 2 * w e b) ≤
    cdim ^ 2 *
      (ccard * (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b)) + 1
  calc
    ccard *
        (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) ^ 2 * w e b) ≤
      ccard *
        (∑ e : E, ∑ b : Fin D,
          (cdim ^ 2 * (a e b) ^ 2 + 1) * w e b) :=
      mul_le_mul_of_nonneg_left hsum hccard
    _ = cdim ^ 2 *
        (ccard * (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b)) + 1 := by
      have hsplit :
        (∑ e : E, ∑ b : Fin D,
          (cdim ^ 2 * (a e b) ^ 2 + 1) * w e b) =
        cdim ^ 2 * (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b) +
          ∑ e : E, ∑ b : Fin D, w e b := by
        simp_rw [add_mul, one_mul, Finset.sum_add_distrib]
        simp_rw [mul_assoc]
        congr 1
        calc
          (∑ e : E, ∑ b : Fin D,
              cdim ^ 2 * ((a e b) ^ 2 * w e b)) =
              ∑ e : E, cdim ^ 2 *
                (∑ b : Fin D, (a e b) ^ 2 * w e b) := by
            apply Finset.sum_congr rfl
            intro e he
            simpa using
              (Finset.mul_sum (Finset.univ : Finset (Fin D))
                (fun b ↦ (a e b) ^ 2 * w e b) (cdim ^ 2)).symm
          _ = cdim ^ 2 *
              (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b) := by
            simpa using
              (Finset.mul_sum (Finset.univ : Finset E)
                (fun e ↦ ∑ b : Fin D, (a e b) ^ 2 * w e b)
                (cdim ^ 2)).symm
      rw [hsplit, hweight]
      calc
        ccard *
            (cdim ^ 2 *
                (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b) +
              (Fintype.card E : ℝ)) =
            cdim ^ 2 *
                (ccard *
                  (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b)) +
              ccard * (Fintype.card E : ℝ) := by ring
        _ = cdim ^ 2 *
                (ccard *
                  (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b)) + 1 := by
              rw [hnormalize]

/-- Twice the worst-case Haar cubic-overlap bound is enough for the exact
constant-`13` score premise used by the shallow upper theorem. -/
theorem finiteUnitaryProjectiveScoreSecondMomentBoundThirteen_of_weightedOverlapSquare_le
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D))
    (hoverlap : finiteUnitaryProjectiveWeightedOverlapSquare U ρ u ≤
      12 / (((D + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ))) :
    FiniteUnitaryProjectiveScoreSecondMomentBoundThirteen U ρ u := by
  let d1 : ℝ := ((D + 1 : ℕ) : ℝ)
  let d2 : ℝ := ((D + 2 : ℕ) : ℝ)
  have hd1 : 0 < d1 := by
    dsimp [d1]
    positivity
  have hd2 : 0 < d2 := by
    dsimp [d2]
    positivity
  have hd12 : d1 ≤ d2 := by
    dsimp [d1, d2]
    exact_mod_cast (show D + 1 ≤ D + 2 by omega)
  have hcancel : d1 ^ 2 * (12 / (d1 * d2)) = 12 * (d1 / d2) := by
    field_simp
  have hratio : d1 / d2 ≤ 1 := (div_le_one hd2).2 hd12
  have hconstant : d1 ^ 2 * (12 / (d1 * d2)) + 1 ≤ 13 := by
    rw [hcancel]
    nlinarith
  have hscore :=
    finiteUnitaryProjectiveScoreSecondMoment_le_weightedOverlapSquare
      hD U ρ u
  have hscaled : d1 ^ 2 *
      finiteUnitaryProjectiveWeightedOverlapSquare U ρ u + 1 ≤
      d1 ^ 2 * (12 / (d1 * d2)) + 1 := by
    have hmul : d1 ^ 2 *
        finiteUnitaryProjectiveWeightedOverlapSquare U ρ u ≤
        d1 ^ 2 * (12 / (d1 * d2)) :=
      mul_le_mul_of_nonneg_left (by simpa [d1, d2] using hoverlap)
        (sq_nonneg d1)
    linarith
  unfold FiniteUnitaryProjectiveScoreSecondMomentBoundThirteen
  have hscore13 : finiteUnitaryProjectiveScoreSecondMoment U ρ u ≤ 13 := by
    exact hscore.trans (by simpa [d1] using hscaled.trans hconstant)
  nlinarith [sq_nonneg
    (channelQuadraticPrediction
      (finiteUnitaryCalibratedDensityChannel U) ρ u)]

end

end TomographyOracleCore
