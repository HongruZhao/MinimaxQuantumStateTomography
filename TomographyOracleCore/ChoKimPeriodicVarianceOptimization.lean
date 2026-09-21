import TomographyOracleCore.ChoKimPeriodicErrorOptimization

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators CStarAlgebra ComplexOrder ENNReal MatrixOrder
  Matrix.Norms.L2Operator

noncomputable section

/-!
# Optimized periodic Cho--Kim score variance

The earlier third-moment bridge bounded the score second moment by the
positive cubic overlap plus one.  Retaining the exact first-moment terms
shows that this `+1` cancels in the variance.  Combining that cancellation
with the optimized periodic error `epsilon ≤ 2/3` gives the reusable
one-copy variance constant `10` under exactly the original hypotheses.
-/

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- Exact expansion of the calibrated finite-projective score second
moment in terms of its positive cubic overlap and its first moment. -/
theorem finiteUnitaryProjectiveScoreSecondMoment_exact_expansion
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    finiteUnitaryProjectiveScoreSecondMoment U ρ u =
      ((D + 1 : ℕ) : ℝ) ^ 2 *
          finiteUnitaryProjectiveWeightedOverlapSquare U ρ u -
        2 * finiteUnitaryProjectiveScoreFirstMoment U ρ u - 1 := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let ccard : ℝ := ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal
  let cdim : ℝ := ((D + 1 : ℕ) : ℝ)
  let a : E → Fin D → ℝ := fun e b ↦
    (haarDirectionProjector u *
      finiteUnitaryMeasurementProjector (U e) b).trace.re
  let w : E → Fin D → ℝ := fun e b ↦
    (ρ.matrix * finiteUnitaryMeasurementProjector (U e) b).trace.re
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
    finiteUnitaryProjectiveScoreFirstMoment
    finiteUnitaryProjectiveScore haarCalibratedRankOneScore
  simp only [Fintype.card_fin, smul_eq_mul]
  change ccard *
      (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) ^ 2 * w e b) =
    cdim ^ 2 *
        (ccard * (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b)) -
      2 * (ccard *
        (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) * w e b)) - 1
  have hexpand :
      (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) ^ 2 * w e b) =
        cdim ^ 2 *
            (∑ e : E, ∑ b : Fin D, (a e b) ^ 2 * w e b) -
          2 *
            (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) * w e b) -
          (∑ e : E, ∑ b : Fin D, w e b) := by
    calc
      (∑ e : E, ∑ b : Fin D, (cdim * a e b - 1) ^ 2 * w e b) =
          ∑ e : E, ∑ b : Fin D,
            (cdim ^ 2 * ((a e b) ^ 2 * w e b) -
              2 * ((cdim * a e b - 1) * w e b) - w e b) := by
        apply Finset.sum_congr rfl
        intro e he
        apply Finset.sum_congr rfl
        intro b hb
        ring
      _ = _ := by
        simp_rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hexpand, hweight]
  nlinarith

/-- Exact first-moment cancellation removes the additive one from the old
score-second-moment bound. -/
theorem variance_finiteUnitaryProjectiveScore_le_scaled_weightedOverlapSquare
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) ≤
      ((D + 1 : ℕ) : ℝ) ^ 2 *
        finiteUnitaryProjectiveWeightedOverlapSquare U ρ u := by
  rw [variance_finiteUnitaryProjectiveScore_eq_finiteMoments]
  rw [finiteUnitaryProjectiveScoreSecondMoment_exact_expansion hD]
  nlinarith [sq_nonneg
    (finiteUnitaryProjectiveScoreFirstMoment U ρ u + 1)]

/-- A weighted cubic-overlap coefficient `10` implies the score variance
constant `10`. -/
theorem variance_finiteUnitaryProjectiveScore_le_ten_of_weightedOverlapSquare
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D))
    (hoverlap : finiteUnitaryProjectiveWeightedOverlapSquare U ρ u ≤
      10 / (((D + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ))) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) ≤ 10 := by
  have hv :=
    variance_finiteUnitaryProjectiveScore_le_scaled_weightedOverlapSquare
      hD U ρ u
  let d1 : ℝ := ((D + 1 : ℕ) : ℝ)
  let d2 : ℝ := ((D + 2 : ℕ) : ℝ)
  have hd2 : 0 < d2 := by positivity
  have hd12 : d1 ≤ d2 := by
    dsimp [d1, d2]
    exact_mod_cast (show D + 1 ≤ D + 2 by omega)
  have hs := mul_le_mul_of_nonneg_left
    (by simpa [d1, d2] using hoverlap) (sq_nonneg d1)
  have hratio : d1 ^ 2 * (10 / (d1 * d2)) ≤ 10 := by
    have hquot : d1 / d2 ≤ 1 := (div_le_one hd2).2 hd12
    rw [show d1 ^ 2 * (10 / (d1 * d2)) = 10 * (d1 / d2) by
      field_simp]
    nlinarith
  exact hv.trans (hs.trans (by simpa [d1, d2] using hratio))

/-- C-star-matrix relative third-moment comparison with error at most
`2/3` gives the optimized weighted-overlap coefficient `10`. -/
theorem finiteUnitaryProjectiveWeightedOverlapSquare_le_ten_of_relativeCP_cstarMatrix
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 2 / 3)
    (hrelative : RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin D))
        (TripleIndex (Fin D)) ℂ)
      epsilon
      (finiteUnitaryThirdTwirlLinearMap U)
      (unitaryHaarThirdTwirlLinearMap D)) :
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u ≤
      10 / (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hhaar_nonnegative :=
    cpTracePairingOn_unitaryHaarThirdTwirl_nonnegative hD rho u hu
  have hhaar_le :=
    cpTracePairingOn_unitaryHaarThirdTwirl_le_six hD rho u hu
  calc
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u =
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (finiteUnitaryThirdTwirlLinearMap U)
          (densityDirectionTensor rho u) :=
      finiteUnitaryProjectiveWeightedOverlapSquare_eq_cpTracePairingOn
        U rho u
    _ ≤ (1 + epsilon) *
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      hrelative.cpTracePairingOn_le_upper_cstarMatrix
        (densityDirectionTensor_posSemidef rho u)
        (computationalDiagonalTensorCube_posSemidef D)
    _ ≤ (5 / 3 : ℝ) *
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      mul_le_mul_of_nonneg_right (by nlinarith) hhaar_nonnegative
    _ ≤ (5 / 3 : ℝ) *
        (6 / (((D : ℝ) + 1) * ((D : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hhaar_le (by norm_num)
    _ = 10 / (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by ring

/-- Optimized cubic-overlap bound for the literal periodic Cho--Kim
finite-unitary ensemble. -/
theorem ChoKimBlockCondition.periodicWeightedOverlapSquare_le_ten
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    finiteUnitaryProjectiveWeightedOverlapSquare
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u ≤
      10 / ((((2 ^ n) + 1 : ℕ) : ℝ) *
        (((2 ^ n) + 2 : ℕ) : ℝ)) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    finiteUnitaryProjectiveWeightedOverlapSquare_le_ten_of_relativeCP_cstarMatrix
      (by positivity : 0 < 2 ^ n)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      rho u hu
      (choKimPeriodicThirdDesignError n K)
      (h.choKimPeriodicThirdDesignError_le_two_thirds hn)
      (h.relativeCPApproximation_periodicThirdDesign hn)

/-- Optimized one-copy variance bound for the literal periodic Cho--Kim
finite-unitary score. -/
theorem ChoKimBlockCondition.variance_periodicFiniteUnitaryProjectiveScore_le_ten
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM (2 ^ n) (by positivity)
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)).bornMeasure
            rho) ≤ 10 := by
  apply variance_finiteUnitaryProjectiveScore_le_ten_of_weightedOverlapSquare
  exact h.periodicWeightedOverlapSquare_le_ten hn rho u hu

end

end TomographyOracleCore
