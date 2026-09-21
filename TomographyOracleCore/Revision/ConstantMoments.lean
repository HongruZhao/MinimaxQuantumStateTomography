import TomographyOracleCore.Revision.PeriodicBornMoments
import TomographyOracleCore.ChoKimPeriodicNearExactVariance

namespace TomographyOracleCore.Revision.ConstantMoments
open MeasureTheory MatrixReduction Candidate2FiniteBornVectorLaw Candidate2PhaseRandomizedLaw
open Candidate2FiniteBornMomentBridge
open BornFourthMoment BornSecondMoment BornMomentHomogeneity PeriodicBornMoments
open scoped InnerProductSpace CStarAlgebra ComplexOrder
noncomputable section
variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]
local instance : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

theorem integral_second_bounds_of_relativeCP_sharp
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 30373 / 50000)
    (hrelative : RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ)
      epsilon (finiteUnitaryThirdTwirlLinearMap U) (unitaryHaarThirdTwirlLinearMap D)) :
    19627 / 50000 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂finiteUnitaryBornVectorLaw U rho) ∧
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂finiteUnitaryBornVectorLaw U rho) ≤ 80373 / 25000 := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hlow := lower_cpTracePairingOn_cstarMatrix hrelative
    (densityDirectionIdentityTensor_posSemidef rho u)
    (computationalDiagonalTensorCube_posSemidef D)
  have hhigh := hrelative.cpTracePairingOn_le_upper_cstarMatrix
    (densityDirectionIdentityTensor_posSemidef rho u)
    (computationalDiagonalTensorCube_posSemidef D)
  rw [cpTracePairingOn_haar_second_exact hD rho u hu,
    ← finiteUnitaryBornUnscaledSecondMarginal_eq_cpTracePairingOn] at hlow hhigh
  have hd : (0 : ℝ) < (D : ℝ) + 1 := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hd] at hlow
  rw [← mul_div_assoc, le_div_iff₀ hd] at hhigh
  have ho := density_haarDirectionProjector_overlap_bounds hD rho u hu
  have hl := mul_le_mul_of_nonneg_right
    (show (19627 / 50000 : ℝ) ≤ 1 - epsilon by linarith)
    (show 0 ≤ 1 + (rho.matrix * haarDirectionProjector u).trace.re by linarith [ho.1])
  have hh := mul_le_mul_of_nonneg_right
    (show 1 + epsilon ≤ (80373 / 50000 : ℝ) by linarith)
    (show 0 ≤ 1 + (rho.matrix * haarDirectionProjector u).trace.re by linarith [ho.1])
  rw [integral_finiteUnitaryBornVectorLaw_inner_sq hD]
  constructor <;> nlinarith [ho.1, ho.2]

/-- Unconditional covariance conditioning for the literal periodic ensemble. -/
theorem integral_second_bounds_periodic_sharp
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    19627 / 50000 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂choKimPeriodicBornVectorLaw h.block_dvd rho) ∧
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂choKimPeriodicBornVectorLaw h.block_dvd rho) ≤ 80373 / 25000 := by
  exact integral_second_bounds_of_relativeCP_sharp (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u hu
    (choKimPeriodicThirdDesignError n K)
    (by linarith [h.choKimPeriodicThirdDesignError_add_one_le_160746_div_100000 hn])
    (h.relativeCPApproximation_periodicThirdDesign hn)

/-- The sharper second moment permits the dyadic L6/L2 bound 29/8 instead of 4. -/
theorem hasL6L2Marginals_phase_sharp
    (mu : Measure (EuclideanSpace ℂ (Fin D))) [IsProbabilityMeasure mu]
    (hmu2 : MemLp id 2 mu) (hmu6 : MemLp id 6 mu)
    (hsecond : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      19627 / 50000 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ∧
        (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ≤ 80373 / 25000)
    (hsixth : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu) ≤ 34) :
    PeriodicForwardCovariance.HasL6L2Marginals (phaseRandomizedLaw mu) (29 / 8) := by
  intro u
  have h2 := (integral_inner_norm_pow_bounds_of_unit mu 2 (by decide)
    (19627 / 50000) (80373 / 25000) hsecond u).1
  have h6 := (integral_inner_norm_pow_bounds_of_unit mu 6 (by decide)
    0 34 (fun v hv => ⟨integral_nonneg (fun _ => by positivity), hsixth v hv⟩) u).2
  have h3 := pow_le_pow_left₀
    (by positivity : (0 : ℝ) ≤ (19627 / 50000 : ℝ) * ‖u‖ ^ 2) h2 3
  norm_num [mul_pow, ← pow_mul] at h3
  have hcomplex : (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu) ≤
      ((29 / 8 : ℝ) ^ 6 / 4) * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ^ 3 := by
    nlinarith [pow_nonneg (norm_nonneg u) 6]
  have hreal2 : (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) =
      (2 : ℝ)⁻¹ * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) := by
    simp_rw [sq_abs]
    exact integral_real_inner_sq_phaseRandomizedLaw hmu2 u
  have hreal6 := integral_abs_real_inner_sixth_phaseRandomizedLaw_le hmu6 u
  rw [hreal2]
  nlinarith

/-- No moment hypothesis remains at the literal periodic Born endpoint. -/
theorem periodic_born_hasL6L2_sharp {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n))) :
    PeriodicForwardCovariance.HasL6L2Marginals
      (choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho) (29 / 8) := by
  letI := choKimPeriodicBornVectorLaw_isProbability H.block_dvd rho
  exact hasL6L2Marginals_phase_sharp
    (choKimPeriodicBornVectorLaw H.block_dvd rho)
    (memLp_id_finiteUnitaryBornVectorLaw (by positivity) _ rho 2)
    (memLp_id_finiteUnitaryBornVectorLaw (by positivity) _ rho 6)
    (integral_second_bounds_periodic_sharp H hn rho)
    (periodic_born_sixth H hn rho)

end
end TomographyOracleCore.Revision.ConstantMoments
