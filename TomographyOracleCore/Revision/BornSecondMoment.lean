import TomographyOracleCore.Revision.BornFourthMoment
import TomographyOracleCore.ChoKimPeriodicErrorOptimization
import TomographyOracleCore.FiniteUnitaryProjectiveCStarRelativeThirdMoment

/-!
# Conditioning of the literal Born vector covariance

The third tensor slot is the identity, so testing the actual third twirl
computes a second-projector moment. The lower half of relative CP order is
retained, rather than adding a lower-variance assumption.
-/

namespace TomographyOracleCore.Revision.BornSecondMoment

open MeasureTheory MatrixReduction Candidate2FiniteBornVectorLaw
open Candidate2FiniteBornMomentBridge BornFourthMoment
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal
  MatrixOrder Matrix.Norms.L2Operator CStarAlgebra

noncomputable section

theorem lower_cpTracePairingOn_cstarMatrix
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {epsilon : ℝ}
    {ensemble haar : CStarMatrix ι ι ℂ →ₗ[ℂ] CStarMatrix ι ι ℂ}
    (h : RelativeCPApproximation (A := CStarMatrix ι ι ℂ) epsilon ensemble haar)
    {input test : Matrix ι ι ℂ}
    (hinput : input.PosSemidef) (htest : test.PosSemidef) :
    (1 - epsilon) * cpTracePairingOn test haar input ≤
      cpTracePairingOn test ensemble input := by
  have hmatrix := h.lower_apply_le (cstarMatrix_nonneg_of_posSemidef hinput)
  have hdiff_nonneg :
      0 ≤ (CStarMatrix.ofMatrix
        (ensemble input - (((1 - epsilon : ℝ) : ℂ) • haar) input) :
          CStarMatrix ι ι ℂ) := sub_nonneg.mpr hmatrix
  have hdiff := posSemidef_of_cstarMatrix_nonneg hdiff_nonneg
  have hnonneg := trace_mul_re_nonnegative_of_posSemidef_on test
    (ensemble input - (((1 - epsilon : ℝ) : ℂ) • haar) input) htest hdiff
  change 0 ≤ (test * (CStarMatrix.ofMatrix.symm (ensemble input) -
    ((1 - epsilon : ℝ) : ℂ) • CStarMatrix.ofMatrix.symm (haar input))).trace.re at hnonneg
  rw [Matrix.mul_sub, Matrix.trace_sub, Matrix.mul_smul, Matrix.trace_smul] at hnonneg
  simp only [Complex.sub_re, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at hnonneg
  exact sub_nonneg.mp hnonneg

variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]

def densityDirectionIdentityTensor
    (rho : DensityOperator (Fin D)) (u : EuclideanSpace ℂ (Fin D)) :
    FiniteUnitaryThirdSpace D :=
  matrixTensorThree rho.matrix (haarDirectionProjector u) 1

theorem densityDirectionIdentityTensor_posSemidef
    (rho : DensityOperator (Fin D)) (u : EuclideanSpace ℂ (Fin D)) :
    (densityDirectionIdentityTensor rho u).PosSemidef :=
  Matrix.PosSemidef.matrixTensorThree rho.posSemidef (haarDirectionProjector_posSemidef u)
    Matrix.PosSemidef.one

theorem computationalTensorCubeTerm_pairing_second
    (U : Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (b : Fin D) :
    (matrixTensorThree (finiteComputationalBasisProjector b)
        (finiteComputationalBasisProjector b) (finiteComputationalBasisProjector b) *
      unitaryThirdConjugationGeneral U (densityDirectionIdentityTensor rho u)).trace.re =
      finiteUnitaryBornWeight rho U b *
        ‖⟪finiteUnitaryMeasurementVector U b, u⟫_ℂ‖ ^ 2 := by
  unfold densityDirectionIdentityTensor
  rw [unitaryThirdConjugationGeneral_matrixTensorThree, matrixTensorThree_mul_trace]
  simp_rw [trace_mul_unitary_conjugation]
  change ((rho.matrix * finiteUnitaryMeasurementProjector U b).trace *
    (haarDirectionProjector u * finiteUnitaryMeasurementProjector U b).trace *
    ((1 : Matrix (Fin D) (Fin D) ℂ) * finiteUnitaryMeasurementProjector U b).trace).re = _
  rw [Matrix.one_mul, finiteUnitaryMeasurementProjector_trace, mul_one]
  rw [trace_mul_eq_re_of_isHermitian rho.matrix _ rho.isHermitian
      (finiteUnitaryMeasurementProjector_posSemidef U b).isHermitian,
    trace_mul_eq_re_of_isHermitian (haarDirectionProjector u) _
      (haarDirectionProjector_isHermitian u)
      (finiteUnitaryMeasurementProjector_posSemidef U b).isHermitian]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [trace_direction_projector_measurement_eq_inner_sq]
  rfl

theorem finiteUnitaryBornUnscaledSecondMarginal_eq_cpTracePairingOn
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    finiteUnitaryBornUnscaledSecondMarginal U rho u =
      cpTracePairingOn (computationalDiagonalTensorCube D)
        (finiteUnitaryThirdTwirlLinearMap U) (densityDirectionIdentityTensor rho u) := by
  unfold finiteUnitaryBornUnscaledSecondMarginal cpTracePairingOn
    computationalDiagonalTensorCube finiteUnitaryThirdTwirlLinearMap
  simp only [smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Matrix.mul_smul, Matrix.trace_smul]
  simp_rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  have hcoeffC : (Fintype.card A : ℂ)⁻¹ =
      (((Fintype.card A : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [hcoeffC]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.re_sum, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro e _
  exact (computationalTensorCubeTerm_pairing_second (U e) rho u b).symm

theorem cpTracePairingOn_haar_second_eq_integral
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D) (densityDirectionIdentityTensor rho u) =
      ∫ U : Matrix.unitaryGroup (Fin D) ℂ,
        ∑ b : Fin D, finiteUnitaryBornWeight rho U b *
          ‖⟪finiteUnitaryMeasurementVector U b, u⟫_ℂ‖ ^ 2
        ∂unitaryHaarProbability D := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let test := computationalDiagonalTensorCube D
  let input := densityDirectionIdentityTensor rho u
  let f : Matrix.unitaryGroup (Fin D) ℂ → FiniteUnitaryThirdSpace D :=
    fun U => unitaryThirdConjugationGeneral U input
  have hf : Integrable f (unitaryHaarProbability D) :=
    integrable_unitaryThirdConjugationGeneral D input
  have hscalar : Integrable (fun U => (test * f U).trace) (unitaryHaarProbability D) := by
    simpa only [matrixTraceMulCLM_apply] using (matrixTraceMulCLM test).integrable_comp hf
  unfold cpTracePairingOn unitaryHaarThirdTwirlLinearMap
  change (test * (∫ U, f U ∂unitaryHaarProbability D)).trace.re = _
  rw [trace_mul_integral test f (unitaryHaarProbability D) hf]
  have hre : (∫ U, (test * f U).trace ∂unitaryHaarProbability D).re =
      ∫ U, (test * f U).trace.re ∂unitaryHaarProbability D := by
    simpa only [RCLike.re_eq_complex_re] using (integral_re hscalar).symm
  rw [hre]
  apply integral_congr_ae
  filter_upwards [] with U
  dsimp only [test, f, input]
  unfold computationalDiagonalTensorCube
  rw [Matrix.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp_rw [computationalTensorCubeTerm_pairing_second]

def rankOneBornQuadraticIntegrand
    (rho : DensityOperator (Fin D)) (u : EuclideanSpace ℂ (Fin D))
    (P : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (rho.matrix * P).trace.re * (haarDirectionProjector u * P).trace.re

theorem continuous_rankOneBornQuadraticIntegrand
    (rho : DensityOperator (Fin D)) (u : EuclideanSpace ℂ (Fin D)) :
    Continuous (rankOneBornQuadraticIntegrand rho u) := by
  unfold rankOneBornQuadraticIntegrand
  fun_prop

theorem integrable_rankOneBornQuadraticIntegrand_projective
    (hD : 0 < D) (rho : DensityOperator (Fin D)) (u : EuclideanSpace ℂ (Fin D)) :
    Integrable (rankOneBornQuadraticIntegrand rho u) (complexProjectiveHaarLaw (Fin D)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hh := (integrable_complexProjectiveHaar_trace_mul_two
    (Fin D) rho.matrix (haarDirectionProjector u)).re
  apply hh.congr
  filter_upwards [complexProjectiveHaar_ae_posSemidef (Fin D)] with P hP
  rw [trace_mul_eq_re_of_isHermitian rho.matrix P rho.isHermitian hP.isHermitian,
    trace_mul_eq_re_of_isHermitian (haarDirectionProjector u) P
      (haarDirectionProjector_isHermitian u) hP.isHermitian]
  simp [rankOneBornQuadraticIntegrand]

theorem measurable_measurement_projector (b : Fin D) :
    Measurable (fun U : Matrix.unitaryGroup (Fin D) ℂ => finiteUnitaryMeasurementProjector U b) := by
  unfold finiteUnitaryMeasurementProjector
  fun_prop

theorem integrable_rankOneBornQuadraticIntegrand_measurement
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (b : Fin D) :
    Integrable (fun U : Matrix.unitaryGroup (Fin D) ℂ =>
      rankOneBornQuadraticIntegrand rho u (finiteUnitaryMeasurementProjector U b))
      (unitaryHaarProbability D) := by
  have hf := measurable_measurement_projector b
  have hg := (continuous_rankOneBornQuadraticIntegrand rho u).aestronglyMeasurable
    (μ := Measure.map (fun U : Matrix.unitaryGroup (Fin D) ℂ =>
      finiteUnitaryMeasurementProjector U b) (unitaryHaarProbability D))
  apply (integrable_map_measure hg hf.aemeasurable).1
  rw [map_finiteUnitaryMeasurementProjector_unitaryHaarProbability hD b]
  exact integrable_rankOneBornQuadraticIntegrand_projective hD rho u

theorem integral_rankOneBornQuadraticIntegrand_measurement
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (b : Fin D) :
    (∫ U : Matrix.unitaryGroup (Fin D) ℂ,
      rankOneBornQuadraticIntegrand rho u (finiteUnitaryMeasurementProjector U b)
      ∂unitaryHaarProbability D) =
      ∫ P, rankOneBornQuadraticIntegrand rho u P ∂complexProjectiveHaarLaw (Fin D) := by
  rw [← map_finiteUnitaryMeasurementProjector_unitaryHaarProbability hD b]
  exact (integral_map (measurable_measurement_projector b).aemeasurable
    (continuous_rankOneBornQuadraticIntegrand rho u).aestronglyMeasurable).symm

theorem cpTracePairingOn_haar_second_exact
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    cpTracePairingOn (computationalDiagonalTensorCube D)
        (unitaryHaarThirdTwirlLinearMap D) (densityDirectionIdentityTensor rho u) =
      (1 + (rho.matrix * haarDirectionProjector u).trace.re) / ((D : ℝ) + 1) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  rw [cpTracePairingOn_haar_second_eq_integral hD]
  simp_rw [← trace_direction_projector_measurement_eq_inner_sq,
    finiteUnitaryBornWeight]
  change (∫ U : Matrix.unitaryGroup (Fin D) ℂ,
    ∑ b : Fin D, rankOneBornQuadraticIntegrand rho u (finiteUnitaryMeasurementProjector U b)
    ∂unitaryHaarProbability D) = _
  rw [integral_finsetSum Finset.univ (fun b _ =>
    integrable_rankOneBornQuadraticIntegrand_measurement hD rho u b)]
  simp_rw [integral_rankOneBornQuadraticIntegrand_measurement hD rho u]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hm := card_mul_integral_complexProjectiveHaar_trace_mul_two_re_trace_one
    (Fin D) rho.matrix (haarDirectionProjector u) rho.isHermitian
    (haarDirectionProjector_isHermitian u) rho.trace_eq_one
    (haarDirectionProjector_trace_eq_one u hu)
  rw [Matrix.trace_mul_comm (haarDirectionProjector u) rho.matrix] at hm
  simpa only [Fintype.card_fin, rankOneBornQuadraticIntegrand] using hm

/-- The exact physical scaled second moment is bounded below and above by
universal constants whenever the relative third-design error is at most 2/3. -/
theorem integral_second_bounds_of_relativeCP
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hepsilon : epsilon ≤ 2 / 3)
    (hrelative : RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ)
      epsilon (finiteUnitaryThirdTwirlLinearMap U) (unitaryHaarThirdTwirlLinearMap D)) :
    1 / 3 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂finiteUnitaryBornVectorLaw U rho) ∧
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂finiteUnitaryBornVectorLaw U rho) ≤ 10 / 3 := by
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
    (show (1 / 3 : ℝ) ≤ 1 - epsilon by linarith)
    (show 0 ≤ 1 + (rho.matrix * haarDirectionProjector u).trace.re by linarith [ho.1])
  have hh := mul_le_mul_of_nonneg_right
    (show 1 + epsilon ≤ (5 / 3 : ℝ) by linarith)
    (show 0 ≤ 1 + (rho.matrix * haarDirectionProjector u).trace.re by linarith [ho.1])
  rw [integral_finiteUnitaryBornVectorLaw_inner_sq hD]
  constructor <;> nlinarith [ho.1, ho.2]

/-- Unconditional covariance conditioning for the literal periodic ensemble. -/
theorem integral_second_bounds_periodic
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    1 / 3 ≤ (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂choKimPeriodicBornVectorLaw h.block_dvd rho) ∧
      (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂choKimPeriodicBornVectorLaw h.block_dvd rho) ≤ 10 / 3 := by
  exact integral_second_bounds_of_relativeCP (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u hu
    (choKimPeriodicThirdDesignError n K)
    (h.choKimPeriodicThirdDesignError_le_two_thirds hn)
    (h.relativeCPApproximation_periodicThirdDesign hn)

end

end TomographyOracleCore.Revision.BornSecondMoment
