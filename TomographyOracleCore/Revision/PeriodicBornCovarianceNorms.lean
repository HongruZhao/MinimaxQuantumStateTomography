import TomographyOracleCore.Revision.PeriodicBornMoments

namespace TomographyOracleCore.Revision.PeriodicBornCovarianceNorms

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance Candidate2FiniteBornVectorLaw
open Candidate2PhaseRandomizedLaw BornSecondMoment BornMomentHomogeneity
open scoped InnerProductSpace RealInnerProductSpace
noncomputable section

theorem covariance_norm_le_of_quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu) {b : ℝ} (hb : 0 ≤ b)
    (hquad : ∀ u : E, (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ≤ b * ‖u‖ ^ 2) :
    ‖populationCovariance mu‖ ≤ b := by
  rw [ContinuousLinearMap.norm_eq_iSup_rayleighQuotient _ (populationCovariance_isSymmetric mu)]
  apply ciSup_le
  intro u
  change |⟪populationCovariance mu u, u⟫_ℝ / ‖u‖ ^ 2| ≤ b
  rw [inner_populationCovariance_apply_self_eq_integral_sq hmu]
  by_cases hu : u = 0
  · simpa only [hu, inner_zero_right, zero_pow (by decide : 2 ≠ 0), integral_zero,
      norm_zero, zero_div, abs_zero] using hb
  have hs : 0 < ‖u‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
  rw [abs_div, abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _), abs_of_pos hs]
  exact (div_le_iff₀ hs).2 (hquad u)

local instance {D : ℕ} : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

theorem periodic_real_second_bounds {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : MatrixReduction.DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) :
    (1 / 6) * ‖u‖ ^ 2 ≤
      (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho) ∧
      (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho) ≤
        (5 / 3) * ‖u‖ ^ 2 := by
  let mu := choKimPeriodicBornVectorLaw H.block_dvd rho
  letI : IsProbabilityMeasure mu := choKimPeriodicBornVectorLaw_isProbability H.block_dvd rho
  have hmu : MemLp id 2 mu := memLp_id_finiteUnitaryBornVectorLaw (by positivity) _ rho 2
  have hc := integral_inner_norm_pow_bounds_of_unit mu 2 (by decide) (1 / 3) (10 / 3)
    (integral_second_bounds_periodic H hn rho) u
  change (1 / 6) * ‖u‖ ^ 2 ≤ (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂phaseRandomizedLaw mu) ∧
    (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂phaseRandomizedLaw mu) ≤ (5 / 3) * ‖u‖ ^ 2
  rw [integral_real_inner_sq_phaseRandomizedLaw hmu]
  constructor <;> linarith [hc.1, hc.2]

/-- The real population covariance has a positive, dimension-independent
operator norm between one sixth and five thirds. -/
theorem periodic_real_covariance_norm_bounds {n K : ℕ} (H : ChoKimBlockCondition n K)
    (hn : 0 < n) (rho : MatrixReduction.DensityOperator (Fin (2 ^ n))) :
    1 / 6 ≤ ‖populationCovariance (choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho)‖ ∧
      ‖populationCovariance (choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho)‖ ≤ 5 / 3 := by
  let mu := choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  letI : IsProbabilityMeasure mu := choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability H.block_dvd rho
  have hfixed := ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  have hmu : MemLp id 2 mu := fixedNorm_memLp hfixed 2
  constructor
  · let b : Fin (2 ^ n) := ⟨0, by positivity⟩
    let u := EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ b
    have hu : ‖u‖ = 1 := (EuclideanSpace.basisFun (Fin (2 ^ n)) ℂ).orthonormal.norm_eq_one b
    have hl := (periodic_real_second_bounds H hn rho u).1
    rw [hu, one_pow, mul_one] at hl
    exact hl.trans (integral_sq_inner_le_populationCovariance_norm_of_norm_eq_one hmu u hu)
  · exact covariance_norm_le_of_quadratic hmu (by norm_num)
      (fun u => (periodic_real_second_bounds H hn rho u).2)

end
end TomographyOracleCore.Revision.PeriodicBornCovarianceNorms
