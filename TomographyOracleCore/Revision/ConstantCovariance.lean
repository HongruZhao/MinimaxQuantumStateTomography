import TomographyOracleCore.Revision.ConstantMoments
import TomographyOracleCore.Revision.PeriodicForwardConcentration
import TomographyOracleCore.Candidate2PhysicalFiniteSampleCovariance

namespace TomographyOracleCore.Revision.ConstantCovariance
open MeasureTheory ProbabilityTheory MatrixReduction PeriodicForwardCovariance
open Candidate2FiniteBornVectorLaw FixedNormBaiYinTransport PeriodicBornCovarianceNorms
open CovarianceIsometryTransport ConstantMoments PhysicalMinimax
open scoped RealInnerProductSpace InnerProductSpace BigOperators
noncomputable section

/-- Effective rank never exceeds the dimension of the real vector space. -/
theorem fixedNorm_le_dimension_mul_covarianceNorm
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    q ≤ (Module.finrank ℝ E : ℝ) * ‖populationCovariance mu‖ := by
  let b := stdOrthonormalBasis ℝ E
  rw [← trace_populationCovariance_eq_fixedNorm hfixed,
    LinearMap.trace_eq_sum_inner _ b]
  calc
    (∑ i, ⟪b i, populationCovariance mu (b i)⟫_ℝ) ≤ ∑ _i : Fin (Module.finrank ℝ E),
        ‖populationCovariance mu‖ := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        ⟪b i, populationCovariance mu (b i)⟫_ℝ ≤ ‖b i‖ * ‖populationCovariance mu (b i)‖ :=
          real_inner_le_norm _ _
        _ ≤ ‖b i‖ * (‖populationCovariance mu‖ * ‖b i‖) :=
          mul_le_mul_of_nonneg_left ((populationCovariance mu).le_opNorm _) (norm_nonneg _)
        _ = ‖populationCovariance mu‖ := by rw [b.norm_eq_one]; ring
    _ = _ := by simp

/-- Explicit coordinate transport of the proved fixed-norm covariance bound. -/
theorem fixedNorm_covariance_finiteDimensional_explicit
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (T : ℕ) (hT : 0 < T) (mu : Measure E) [IsProbabilityMeasure mu]
    (q kappa : ℝ) (hq : 0 < q) (hkappa : 1 ≤ kappa)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hL6 : HasL6L2Marginals mu kappa)
    (htrunc : q ≤ (T : ℝ) * ‖populationCovariance mu‖) :
    (∫ X : Fin T → E, ‖sampleCovariance X - populationCovariance mu‖
      ∂Measure.pi (fun _ : Fin T => mu)) ≤
      FixedNormBaiYinProof.covarianceConstant kappa * ‖populationCovariance mu‖ *
        Real.sqrt ((q / ‖populationCovariance mu‖) / (T : ℝ)) := by
  let e := (stdOrthonormalBasis ℝ E).repr
  let nu := mu.map e
  letI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  have hmu := fixedNorm_memLp hfixed 2
  have hnorm : ‖populationCovariance nu‖ = ‖populationCovariance mu‖ := by
    rw [show nu = mu.map e from rfl, populationCovariance_map e hmu, norm_conjugate]
  have hdim : 0 < Module.finrank ℝ E := Module.finrank_pos
  letI : Nonempty (Fin (Module.finrank ℝ E)) := ⟨⟨0, hdim⟩⟩
  have hbound := FixedNormBaiYinProof.expected_covariance_error_le hT
    (fixedNorm_map e hfixed) hq hkappa (hasL6L2_map e hL6)
    (by
      change q ≤ (T : ℝ) * ‖populationCovariance nu‖
      rw [hnorm]
      exact htrunc)
  rw [hnorm] at hbound
  change (∫ X : Fin T → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
    ‖sampleCovariance X - populationCovariance (mu.map e)‖
      ∂Measure.pi (fun _ : Fin T => mu.map e)) ≤ _ at hbound
  rwa [expected_covariance_error_map e mu hmu T] at hbound

local instance {D : ℕ} : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

theorem periodic_real_covariance_norm_le_sharp {n K : ℕ}
    (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n))) :
    ‖populationCovariance (choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho)‖ ≤
      80373 / 50000 := by
  letI := choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability H.block_dvd rho
  let mu := choKimPeriodicBornVectorLaw H.block_dvd rho
  letI := choKimPeriodicBornVectorLaw_isProbability H.block_dvd rho
  have hmu : MemLp id 2 mu := memLp_id_finiteUnitaryBornVectorLaw (by positivity) _ rho 2
  apply covariance_norm_le_of_quadratic
    (fixedNorm_memLp (ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho) 2)
    (by norm_num)
  intro u
  have hc := (BornMomentHomogeneity.integral_inner_norm_pow_bounds_of_unit mu 2 (by decide)
    (19627 / 50000) (80373 / 25000) (integral_second_bounds_periodic_sharp H hn rho) u).2
  change (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂Candidate2PhaseRandomizedLaw.phaseRandomizedLaw mu) ≤ _
  rw [Candidate2PhaseRandomizedLaw.integral_real_inner_sq_phaseRandomizedLaw hmu]
  linarith

theorem effective_rank_rate_scalar_sharp {d s t : ℝ}
    (hd : 65536 ≤ d) (hs : 0 < s) (hs2 : s ≤ 80373 / 50000) (ht : 0 < t) :
    s * Real.sqrt (((d + 1) / s) / t) ≤ (127 / 100 : ℝ) * Real.sqrt (d / t) := by
  have hid : s * Real.sqrt (((d + 1) / s) / t) = Real.sqrt (s * (d + 1) / t) := by
    nth_rw 1 [← Real.sqrt_sq hs.le]
    rw [← Real.sqrt_mul (sq_nonneg s)]
    congr 1
    field_simp
  rw [hid]
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [Real.sq_sqrt (by positivity : 0 ≤ s * (d + 1) / t), mul_pow,
    Real.sq_sqrt (by positivity : 0 ≤ d / t)]
  have hp : s * (d + 1) ≤ (127 / 100 : ℝ) ^ 2 * d := by nlinarith
  have hh := div_le_div_of_nonneg_right hp ht.le
  simpa only [mul_div_assoc] using hh

/-- Explicit improved physical covariance coefficient. -/
def sharpForwardCovarianceConstant : ℝ :=
  (127 / 50 : ℝ) * FixedNormBaiYinProof.covarianceConstant (29 / 8)

theorem sharpForwardCovarianceConstant_pos : 0 < sharpForwardCovarianceConstant := by
  exact mul_pos (by norm_num) (FixedNormBaiYinProof.covarianceConstant_pos (by norm_num))

/-- Relative to the coefficient 4*C(4) in the same general covariance proof, the new one is
about 42.8 percent, with the same underlying general covariance proof. -/
theorem sharpForwardCovarianceConstant_ratio :
    sharpForwardCovarianceConstant =
      ((127 / 200 : ℝ) * (29 / 32 : ℝ) ^ 4) *
        (4 * FixedNormBaiYinProof.covarianceConstant 4) := by
  unfold sharpForwardCovarianceConstant FixedNormBaiYinProof.covarianceConstant
  ring

/-- The raw physical average has its sharp-order bound already for T>=2d,
with an explicit coefficient and no covariance premise. -/
theorem periodic_expected_forward_covariance_sharp
    {n K T : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n) (hT : 0 < T)
    (hsize : 2 * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ))
    (rho : DensityOperator (Fin (2 ^ n))) :
    (∫ sample, periodicForwardError H rho sample ∂periodicSampleLaw H T rho) ≤
      sharpForwardCovarianceConstant * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) := by
  let mu := choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  letI := choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability H.block_dvd rho
  let d : ℝ := ((2 ^ n : ℕ) : ℝ)
  let s : ℝ := ‖populationCovariance mu‖
  have hfixed := ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  have htrace := fixedNorm_le_dimension_mul_covarianceNorm hfixed
  rw [Candidate2PhysicalFiniteSampleCovariance.finrank_real_complexEuclideanSpace] at htrace
  have htrunc : d + 1 ≤ (T : ℝ) * s := by
    simp only [Nat.cast_mul, Nat.cast_ofNat] at htrace
    change d + 1 ≤ (2 * d) * s at htrace
    exact htrace.trans (mul_le_mul_of_nonneg_right hsize (norm_nonneg _))
  have hcov := fixedNorm_covariance_finiteDimensional_explicit T hT mu (d + 1) (29 / 8)
    (by positivity) (by norm_num) hfixed (periodic_born_hasL6L2_sharp H hn rho) htrunc
  have hd : 65536 ≤ d := by
    dsimp only [d]
    exact_mod_cast H.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn
  have hs : 0 < s := FixedNormCovarianceBounds.norm_populationCovariance_pos hfixed (by positivity)
  have hs2 : s ≤ 80373 / 50000 := periodic_real_covariance_norm_le_sharp H hn rho
  have hr := effective_rank_rate_scalar_sharp hd hs hs2 (show 0 < (T : ℝ) by exact_mod_cast hT)
  have hC := (FixedNormBaiYinProof.covarianceConstant_pos (show (1 : ℝ) ≤ 29 / 8 by norm_num)).le
  have hreal : (∫ X : Fin T → EuclideanSpace ℂ (Fin (2 ^ n)),
      ‖sampleCovariance X - populationCovariance mu‖ ∂Measure.pi (fun _ : Fin T => mu)) ≤
      ((127 / 100 : ℝ) * FixedNormBaiYinProof.covarianceConstant (29 / 8)) * Real.sqrt (d / (T : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hr hC
    exact hcov.trans (by nlinarith [hh])
  have hf := PeriodicForwardConcentration.expected_forward_error_le_twice_real (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) rho hT
  have hh := mul_le_mul_of_nonneg_left hreal (by norm_num : (0 : ℝ) ≤ 2)
  change (∫ sample, periodicForwardError H rho sample ∂periodicSampleLaw H T rho) ≤
    2 * (∫ X : Fin T → EuclideanSpace ℂ (Fin (2 ^ n)),
      ‖sampleCovariance X - populationCovariance mu‖ ∂Measure.pi (fun _ : Fin T => mu)) at hf
  calc
    _ ≤ _ := hf
    _ ≤ 2 * (((127 / 100 : ℝ) * FixedNormBaiYinProof.covarianceConstant (29 / 8)) *
        Real.sqrt (d / (T : ℝ))) := hh
    _ = _ := by unfold sharpForwardCovarianceConstant; dsimp only [d]; ring

end
end TomographyOracleCore.Revision.ConstantCovariance
