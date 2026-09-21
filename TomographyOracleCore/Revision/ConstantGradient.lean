import TomographyOracleCore.Revision.ConstantCovariance
import TomographyOracleCore.Revision.ConstantSolver

namespace TomographyOracleCore.Revision.MatrixSolver
open MeasureTheory MatrixReduction FinitePrecision
open BornMatrixCovariance ComplexCovarianceSymmetrization Candidate2FiniteBornVectorLaw
open PeriodicForwardCovariance ConstantCovariance
open scoped ComplexOrder InnerProductSpace BigOperators Matrix.Norms.L2Operator
noncomputable section
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- The uncalibrated physical channel preserves positivity. -/
theorem finite_forward_density_posSemidef
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    (finiteUnitaryProjectiveDensityForward U rho).PosSemidef := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  unfold finiteUnitaryProjectiveDensityForward
  apply Matrix.PosSemidef.smul _ (by positivity)
  apply Matrix.posSemidef_sum
  intro e _
  apply Matrix.posSemidef_sum
  intro b _
  apply (finiteUnitaryMeasurementProjector_posSemidef (U e) b).smul
  exact trace_mul_re_nonnegative_of_posSemidef_on rho.matrix _ rho.posSemidef
    (finiteUnitaryMeasurementProjector_posSemidef (U e) b)

/-- The uncalibrated physical channel preserves trace one. -/
theorem finite_forward_density_trace
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    (finiteUnitaryProjectiveDensityForward U rho).trace = 1 := by
  unfold finiteUnitaryProjectiveDensityForward
  rw [Matrix.trace_smul, Matrix.trace_sum]
  simp_rw [Matrix.trace_sum, Matrix.trace_smul, finiteUnitaryMeasurementProjector_trace]
  simp_rw [← Finset.sum_smul]
  rw [sum_finiteUnitaryMeasurementProjector_ensemble_bornWeight, smul_smul]
  simp [ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.card_ne_zero]

local instance : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

/-- Conditioning of the existing periodic Born covariance bounds the actual
scaled forward channel on every density matrix. -/
theorem periodic_scaled_forward_operatorNorm_le
    {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n))) :
    matrixOperatorNorm (((((2 ^ n : ℕ) : ℝ)) + 1) •
      finiteUnitaryProjectiveDensityForward
        (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) rho) ≤ 80373 / 25000 := by
  let mu := choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  letI := choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability H.block_dvd rho
  have hfixed := ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  have hcov := periodic_real_covariance_norm_le_sharp H hn rho
  change ‖matrixOperatorIsometry (2 ^ n) _‖ ≤ _
  rw [← complexPopulationCovariance_phaseBorn (by positivity)]
  change ‖complexPopulationCovariance mu‖ ≤ _
  rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ),
    complexPopulationCovariance_restrict hfixed]
  have hnorm := norm_symmetrize_le (populationCovariance mu)
  change ‖populationCovariance mu‖ ≤ _ at hcov
  linarith

/-- The old dimension-squared gradient estimate improves to `C(d+1)`
whenever the scaled positive channel has operator norm at most `C`. -/
theorem forwardGradient_norm_sq_le_covariance
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ) (C : ℝ)
    (hC : ∀ rho : DensityOperator (Fin D),
      matrixOperatorNorm (((D : ℝ) + 1) • finiteUnitaryProjectiveDensityForward U rho) ≤ C)
    (v : EuclideanSpace ℂ (Fin D)) (hv : v ≠ 0) {s : ℝ} (hs : |s| ≤ 1) :
    ‖forwardGradient U v s‖ ^ 2 ≤ C * ((D : ℝ) + 1) := by
  let rho := normalizedProjectorDensity v hv
  let A := ((D : ℝ) + 1) • finiteUnitaryProjectiveDensityForward U rho
  have hA : A.PosSemidef := (finite_forward_density_posSemidef hD U rho).smul (by positivity)
  have ht : A.trace.re = (D : ℝ) + 1 := by
    dsimp [A]
    rw [Matrix.trace_smul, finite_forward_density_trace]
    simp
  have hAnorm : ‖encode A‖ ^ 2 ≤ C * ((D : ℝ) + 1) := by
    rw [norm_encode_sq_eq_trace, hA.isHermitian.eq]
    calc
      (A * A).trace.re ≤ ‖(A * A).trace‖ := Complex.re_le_norm _
      _ ≤ hermitianTraceNorm A hA.isHermitian * matrixOperatorNorm A :=
        norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm A A hA.isHermitian
      _ = ((D : ℝ) + 1) * matrixOperatorNorm A := by
        rw [hermitianTraceNorm_psd_eq_re_trace A hA, ht]
      _ ≤ ((D : ℝ) + 1) * C := mul_le_mul_of_nonneg_left (hC rho) (by positivity)
      _ = _ := mul_comm _ _
  have heq : forwardGradient U v s = (-s) • encode A := by
    rw [forwardGradient]
    change (-((D + 1 : ℕ) : ℝ) * s) • encode (finiteUnitaryProjectiveLinearChannel U rho.matrix) = _
    rw [finiteUnitaryProjectiveLinearChannel_density]
    dsimp [A]
    rw [smul_smul]
    congr 1
    push_cast
    ring
  rw [heq, norm_smul, Real.norm_eq_abs, abs_neg, mul_pow]
  have hs2 : |s| ^ 2 ≤ 1 := by nlinarith [abs_nonneg s]
  exact (mul_le_of_le_one_left (sq_nonneg _) hs2).trans hAnorm

/-- A simple dyadic budget is within 1.1 percent of the proved covariance
coefficient and removes one full power of dimension from the iteration bound. -/
def periodicGradientSquareBudget (D : ℕ) : ℝ := (13 / 4 : ℝ) * ((D : ℝ) + 1)

theorem periodic_forwardGradient_norm_le
    {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (v : EuclideanSpace ℂ (Fin (2 ^ n))) (hv : v ≠ 0)
    {s : ℝ} (hs : |s| ≤ 1) :
    ‖forwardGradient (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) v s‖ ≤
      Real.sqrt (periodicGradientSquareBudget (2 ^ n)) := by
  apply (Real.le_sqrt (norm_nonneg _) (by unfold periodicGradientSquareBudget; positivity)).mpr
  have hg := forwardGradient_norm_sq_le_covariance (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) (80373 / 25000)
    (periodic_scaled_forward_operatorNorm_le H hn) v hv hs
  unfold periodicGradientSquareBudget
  nlinarith [show (0 : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) by positivity]

end
end TomographyOracleCore.Revision.MatrixSolver
