import TomographyOracleCore.Revision.BornSecondMoment
import TomographyOracleCore.Revision.BornMomentHomogeneity

/-!
# The actual periodic Born law satisfies the covariance moment interface

The only intermediate premise in the final theorem is the uniform eighth
overlap estimate for the literal periodic ensemble. The lower second moment,
Born reweighting, mixed-state reduction, homogeneity, and quarter-phase
realification are proved here or in the imported modules.
-/

namespace TomographyOracleCore.Revision.BornCovarianceConditions

open MeasureTheory Candidate2FiniteBornVectorLaw Candidate2PhaseRandomizedLaw
open BornFourthMoment BornSecondMoment BornMomentHomogeneity
open scoped InnerProductSpace

noncomputable section

variable {D : ℕ}

local instance : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

/-- The exact coefficient before quarter-phase realification is 34 * 27. -/
theorem complex_sixth_le_918_second_cubed
    (mu : Measure (EuclideanSpace ℂ (Fin D)))
    (hsecond : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      1 / 3 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ∧
        (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ≤ 10 / 3)
    (hsixth : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu) ≤ 34)
    (u : EuclideanSpace ℂ (Fin D)) :
    (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu) ≤
      918 * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ^ 3 := by
  have h2 := (integral_inner_norm_pow_bounds_of_unit mu 2 (by decide)
    (1 / 3) (10 / 3) hsecond u).1
  have h6 := (integral_inner_norm_pow_bounds_of_unit mu 6 (by decide)
    0 34 (fun v hv => ⟨integral_nonneg (fun _ => by positivity), hsixth v hv⟩) u).2
  have h3 := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / 3 * ‖u‖ ^ 2) h2 3
  norm_num [mul_pow, ← pow_mul] at h3
  nlinarith

/-- The exact real sixth-to-second coefficient is four times 918. -/
theorem phase_sixth_le_3672_second_cubed
    (mu : Measure (EuclideanSpace ℂ (Fin D))) [IsProbabilityMeasure mu]
    (hmu2 : MemLp id 2 mu) (hmu6 : MemLp id 6 mu)
    (hsecond : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      1 / 3 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ∧
        (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ≤ 10 / 3)
    (hsixth : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu) ≤ 34)
    (u : EuclideanSpace ℂ (Fin D)) :
    (∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂phaseRandomizedLaw mu) ≤
      3672 * (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) ^ 3 := by
  have h2 : (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) =
      (2 : ℝ)⁻¹ * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) := by
    simp_rw [sq_abs]
    exact integral_real_inner_sq_phaseRandomizedLaw hmu2 u
  have h6 := integral_abs_real_inner_sixth_phaseRandomizedLaw_le hmu6 u
  have hc := complex_sixth_le_918_second_cubed mu hsecond hsixth u
  rw [h2]
  nlinarith

/-- A dimension-independent integer norm-ratio constant suffices. -/
theorem hasL6L2Marginals_phase_of_moments
    (mu : Measure (EuclideanSpace ℂ (Fin D))) [IsProbabilityMeasure mu]
    (hmu2 : MemLp id 2 mu) (hmu6 : MemLp id 6 mu)
    (hsecond : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      1 / 3 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ∧
        (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ≤ 10 / 3)
    (hsixth : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu) ≤ 34) :
    PeriodicForwardCovariance.HasL6L2Marginals (phaseRandomizedLaw mu) 4 := by
  intro u
  refine (phase_sixth_le_3672_second_cubed mu hmu2 hmu6 hsecond hsixth u).trans ?_
  apply mul_le_mul_of_nonneg_right (by norm_num)
  exact pow_nonneg (integral_nonneg (fun _ => by positivity)) 3

/-- All marginal hypotheses for covariance concentration follow from the
one remaining uniform eighth-overlap bound for the actual circuit. -/
theorem hasL6L2Marginals_periodic_of_uniform_eighth
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : MatrixReduction.DensityOperator (Fin (2 ^ n)))
    (hfourth : ∀ u : EuclideanSpace ℂ (Fin (2 ^ n)), ‖u‖ = 1 →
      finiteUnitaryUniformEighthMoment
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) u ≤
        34 / (((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) : ℝ) + 1) *
          (((2 ^ n : ℕ) : ℝ) + 2) * (((2 ^ n : ℕ) : ℝ) + 3))) :
    PeriodicForwardCovariance.HasL6L2Marginals
      (choKimPeriodicPhaseRandomizedBornVectorLaw h.block_dvd rho) 4 := by
  letI := choKimPeriodicBornVectorLaw_isProbability h.block_dvd rho
  exact hasL6L2Marginals_phase_of_moments
    (choKimPeriodicBornVectorLaw h.block_dvd rho)
    (memLp_id_finiteUnitaryBornVectorLaw (by positivity) _ rho 2)
    (memLp_id_finiteUnitaryBornVectorLaw (by positivity) _ rho 6)
    (integral_second_bounds_periodic h hn rho)
    (integral_sixth_le_thirtyFour_of_uniform_eighth (by positivity) _ rho hfourth)

end

end TomographyOracleCore.Revision.BornCovarianceConditions
