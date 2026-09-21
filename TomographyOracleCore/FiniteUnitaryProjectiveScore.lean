import TomographyOracleCore.FiniteUnitaryProjectivePOVM
import TomographyOracleCore.DirectionalScores
import TomographyOracleCore.ProjectiveHaarLargeScores

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ComplexOrder InnerProductSpace ENNReal

noncomputable section

/-!
# Scores for finite unitary projective measurements

This module specializes the calibrated rank-one score to the genuine finite
unitary POVM.  Since the Born law has finite support, measurability and all
finite moments are unconditional.  The mean and variance are exposed as
literal finite ensemble sums.
-/

section Score

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- The calibrated rank-one score in direction `u` for a finite unitary
projective measurement outcome. -/
noncomputable def finiteUnitaryProjectiveScore
    (u : EuclideanSpace ℂ (Fin D))
    (B : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  haarCalibratedRankOneScore (haarDirectionProjector u) B

theorem measurable_finiteUnitaryProjectiveScore
    (u : EuclideanSpace ℂ (Fin D)) :
    Measurable (finiteUnitaryProjectiveScore u) := by
  unfold finiteUnitaryProjectiveScore haarCalibratedRankOneScore
  fun_prop

/-! ## Pointwise support bound -/

/-- The unit vector whose rank-one projector is the outcome of measuring the
`b`th coordinate after applying `U`. -/
noncomputable def finiteUnitaryMeasurementVector
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    EuclideanSpace ℂ (Fin D) :=
  WithLp.toLp 2 (fun i ↦ star (U.1 b i))

theorem finiteUnitaryMeasurementVector_norm
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    ‖finiteUnitaryMeasurementVector U b‖ = 1 := by
  have hU : U.1 * U.1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.2)
  have hdiag := congrArg
    (fun M : Matrix (Fin D) (Fin D) ℂ ↦ M b b) hU
  have hsumNormSq :
      (∑ i : Fin D, Complex.normSq (U.1 b i)) = (1 : ℝ) := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      ← starRingEnd_apply, Complex.mul_conj, Matrix.one_apply] using
      congrArg Complex.re hdiag
  have hsum : (∑ i : Fin D, ‖U.1 b i‖ ^ 2) = (1 : ℝ) := by
    simpa [Complex.normSq_eq_norm_sq] using hsumNormSq
  have hsquare : ‖finiteUnitaryMeasurementVector U b‖ ^ 2 = (1 : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq]
    simpa [finiteUnitaryMeasurementVector] using hsum
  nlinarith [norm_nonneg (finiteUnitaryMeasurementVector U b)]

/-- A finite-unitary measurement outcome is literally the sphere projector
of the associated unit vector. -/
theorem finiteUnitaryMeasurementProjector_eq_complexSphereProjector
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    finiteUnitaryMeasurementProjector U b =
      complexSphereProjector
        ⟨finiteUnitaryMeasurementVector U b, by
          simpa [Metric.mem_sphere, dist_zero_right] using
            finiteUnitaryMeasurementVector_norm U b⟩ := by
  ext i j
  calc
    finiteUnitaryMeasurementProjector U b i j =
        (U.1.conjTranspose * finiteComputationalBasisProjector b) i b *
          U.1 b j := by
      unfold finiteUnitaryMeasurementProjector
        finiteComputationalBasisProjector
      rw [Matrix.mul_apply, Finset.sum_eq_single b]
      · intro x hx hxb
        rw [Matrix.mul_single_apply_of_ne (1 : ℂ) b b i x hxb
          U.1.conjTranspose]
        simp
      · simp
    _ = star (U.1 b i) * U.1 b j := by
      unfold finiteComputationalBasisProjector
      rw [Matrix.mul_single_apply_same (1 : ℂ) b b i U.1.conjTranspose]
      simp [Matrix.conjTranspose_apply]
    _ = complexSphereProjector
        ⟨finiteUnitaryMeasurementVector U b, by
          simpa [Metric.mem_sphere, dist_zero_right] using
            finiteUnitaryMeasurementVector_norm U b⟩ i j := by
      simp [finiteUnitaryMeasurementVector, complexSphereProjector,
        Matrix.vecMulVec_apply]

/-- Every projector in the finite-unitary experiment has calibrated score
bounded in absolute value by the Hilbert-space dimension. -/
theorem finiteUnitaryProjectiveScore_abs_le_dimension
    (hD : 0 < D) (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D)
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    |finiteUnitaryProjectiveScore u
      (finiteUnitaryMeasurementProjector U b)| ≤ (D : ℝ) := by
  rw [finiteUnitaryMeasurementProjector_eq_complexSphereProjector]
  exact haarDirectionScore_sphere_abs_le_dimension hD u hu _

/-- The dimension bound holds almost everywhere under every finite-unitary
Born law. -/
theorem finiteUnitaryProjectiveScore_born_ae_abs_le_dimension
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    ∀ᵐ B ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ,
      |finiteUnitaryProjectiveScore u B| ≤ (D : ℝ) := by
  have hbase :
      ∀ᵐ B ∂finiteUnitaryProjectivePOVMBase U,
        |finiteUnitaryProjectiveScore u B| ≤ (D : ℝ) := by
    have hPmeas : MeasurableSet
        {B | |finiteUnitaryProjectiveScore u B| ≤ (D : ℝ)} :=
      measurableSet_le
        (measurable_finiteUnitaryProjectiveScore u).abs measurable_const
    have hc : ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 := by
      simp [Fintype.card_ne_zero]
    unfold finiteUnitaryProjectivePOVMBase
    apply (Measure.ae_ennreal_smul_measure_iff (c :=
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹) hc).2
    simp only [ae_finsetSum_measure_iff, Finset.mem_univ,
      forall_const]
    intro e b
    rw [ae_dirac_iff hPmeas]
    exact finiteUnitaryProjectiveScore_abs_le_dimension hD (U e) b u hu
  have hac :
      (finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ ≪
        finiteUnitaryProjectivePOVMBase U := by
    change bornMeasureFrom (finiteUnitaryProjectivePOVMBase U)
        (finiteUnitaryProjectivePOVMEffect (D := D)) ρ ≪
      finiteUnitaryProjectivePOVMBase U
    unfold bornMeasureFrom
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le hbase

/-- Every real-valued function is integrable against the finite POVM base:
only its finitely many values at the ensemble projectors matter. -/
theorem integrable_finiteUnitaryProjectivePOVMBase_real
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (f : Matrix (Fin D) (Fin D) ℂ → ℝ) :
    Integrable f (finiteUnitaryProjectivePOVMBase U) := by
  unfold finiteUnitaryProjectivePOVMBase
  apply Integrable.smul_measure
  · refine (integrable_finsetSum_measure).2 ?_
    intro e he
    refine (integrable_finsetSum_measure).2 ?_
    intro b hb
    exact integrable_dirac (f := f) (by simp)
  · simp

/-- Every real-valued function is integrable against each finite Born law. -/
theorem integrable_finiteUnitaryProjectivePOVM_born_real
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (f : Matrix (Fin D) (Fin D) ℂ → ℝ) :
    Integrable f ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) := by
  change Integrable f
    (bornMeasureFrom (finiteUnitaryProjectivePOVMBase U)
      (finiteUnitaryProjectivePOVMEffect (D := D)) ρ)
  unfold bornMeasureFrom
  apply (integrable_withDensity_iff
    (measurable_finiteUnitaryProjectivePOVM_bornDensity ρ)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
  exact integrable_finiteUnitaryProjectivePOVMBase_real U
    (fun B ↦
      f B * (bornDensityFrom
        (finiteUnitaryProjectivePOVMEffect (D := D)) ρ B).toReal)

theorem memLp_finiteUnitaryProjectiveScore_two
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    MemLp (finiteUnitaryProjectiveScore u) 2
      ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) := by
  apply (memLp_two_iff_integrable_sq
    (measurable_finiteUnitaryProjectiveScore u).aestronglyMeasurable).2
  exact integrable_finiteUnitaryProjectivePOVM_born_real hD U ρ
    (fun B ↦ (finiteUnitaryProjectiveScore u B) ^ 2)

/-- Literal first moment of the calibrated score under the finite Born law. -/
noncomputable def finiteUnitaryProjectiveScoreFirstMoment
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : E, ∑ b : Fin D,
      finiteUnitaryProjectiveScore u
          (finiteUnitaryMeasurementProjector (U e) b) *
        (ρ.matrix *
          finiteUnitaryMeasurementProjector (U e) b).trace.re

/-- Literal second moment of the calibrated score under the finite Born law. -/
noncomputable def finiteUnitaryProjectiveScoreSecondMoment
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : E, ∑ b : Fin D,
      (finiteUnitaryProjectiveScore u
          (finiteUnitaryMeasurementProjector (U e) b)) ^ 2 *
        (ρ.matrix *
          finiteUnitaryMeasurementProjector (U e) b).trace.re

theorem integral_finiteUnitaryProjectiveScore_eq_firstMoment
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    (∫ B, finiteUnitaryProjectiveScore u B
        ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      finiteUnitaryProjectiveScoreFirstMoment U ρ u := by
  exact integral_finiteUnitaryProjectivePOVM_bornMeasure_real_eq_sum
    hD U ρ (finiteUnitaryProjectiveScore u)

theorem integral_finiteUnitaryProjectiveScore_sq_eq_secondMoment
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    (∫ B, (finiteUnitaryProjectiveScore u B) ^ 2
        ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      finiteUnitaryProjectiveScoreSecondMoment U ρ u := by
  exact integral_finiteUnitaryProjectivePOVM_bornMeasure_real_eq_sum
    hD U ρ (fun B ↦ (finiteUnitaryProjectiveScore u B) ^ 2)

/-- The variance is exactly the finite second moment minus the square of the
finite first moment. -/
theorem variance_finiteUnitaryProjectiveScore_eq_finiteMoments
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      finiteUnitaryProjectiveScoreSecondMoment U ρ u -
        (finiteUnitaryProjectiveScoreFirstMoment U ρ u) ^ 2 := by
  letI : IsProbabilityMeasure
      ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) :=
    (finiteUnitaryProjectivePOVM D hD U).born_probability ρ
  rw [variance_eq_sub (memLp_finiteUnitaryProjectiveScore_two hD U ρ u)]
  change
    (∫ B, (finiteUnitaryProjectiveScore u B) ^ 2
        ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) -
      (∫ B, finiteUnitaryProjectiveScore u B
        ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) ^ 2 = _
  rw [
    integral_finiteUnitaryProjectiveScore_sq_eq_secondMoment,
    integral_finiteUnitaryProjectiveScore_eq_firstMoment]

/-! ## Explicit finite-ensemble channel -/

/-- The uncalibrated finite measurement channel: average the observed
projector weighted by its Born probability in each selected basis. -/
noncomputable def finiteUnitaryProjectiveDensityForward
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) : Matrix (Fin D) (Fin D) ℂ :=
  ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : E, ∑ b : Fin D,
      (ρ.matrix *
        finiteUnitaryMeasurementProjector (U e) b).trace.re •
          finiteUnitaryMeasurementProjector (U e) b

/-- The finite Born-weighted overlap moment paired with a test matrix. -/
noncomputable def finiteUnitaryProjectiveOverlapMoment
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : E, ∑ b : Fin D,
      (O * finiteUnitaryMeasurementProjector (U e) b).trace.re *
        (ρ.matrix *
          finiteUnitaryMeasurementProjector (U e) b).trace.re

/-- Calibrated finite measurement channel corresponding to the score
`(D+1) tr(O B) - 1`. -/
noncomputable def finiteUnitaryCalibratedDensityChannel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) : Matrix (Fin D) (Fin D) ℂ :=
  (((D + 1 : ℕ) : ℝ) • finiteUnitaryProjectiveDensityForward U ρ) - 1

theorem finiteUnitaryProjectiveDensityForward_isHermitian
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    (finiteUnitaryProjectiveDensityForward U ρ).IsHermitian := by
  unfold finiteUnitaryProjectiveDensityForward
  apply Matrix.IsHermitian.smul
  · apply isSelfAdjoint_sum Finset.univ
    intro e he
    apply isSelfAdjoint_sum Finset.univ
    intro b hb
    apply IsSelfAdjoint.smul
    · exact isSelfAdjoint_iff.mpr (by simp)
    · exact (finiteUnitaryMeasurementProjector_posSemidef (U e) b).isHermitian
  · exact isSelfAdjoint_iff.mpr (by simp)

theorem finiteUnitaryCalibratedDensityChannel_isHermitian
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    (finiteUnitaryCalibratedDensityChannel U ρ).IsHermitian := by
  unfold finiteUnitaryCalibratedDensityChannel
  exact
    (finiteUnitaryProjectiveDensityForward_isHermitian U ρ).smul
      (isSelfAdjoint_iff.mpr (by simp)) |>.sub Matrix.isHermitian_one

/-- In a fixed unitary basis the real Born weights sum to one. -/
theorem sum_finiteUnitaryMeasurementProjector_bornWeight
    (U : Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    (∑ b : Fin D,
      (ρ.matrix * finiteUnitaryMeasurementProjector U b).trace.re) = 1 := by
  have hcomplex :
      (∑ b : Fin D,
        (ρ.matrix * finiteUnitaryMeasurementProjector U b).trace) = 1 := by
    calc
      (∑ b : Fin D,
          (ρ.matrix * finiteUnitaryMeasurementProjector U b).trace) =
          (ρ.matrix *
            ∑ b : Fin D, finiteUnitaryMeasurementProjector U b).trace := by
            rw [Matrix.mul_sum, Matrix.trace_sum]
      _ = 1 := by
        rw [sum_finiteUnitaryMeasurementProjector, mul_one, ρ.trace_eq_one]
  have hre := congrArg Complex.re hcomplex
  simpa using hre

/-- Across the whole ensemble, the real Born weights sum to `|E|`. -/
theorem sum_finiteUnitaryMeasurementProjector_ensemble_bornWeight
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    (∑ e : E, ∑ b : Fin D,
      (ρ.matrix *
        finiteUnitaryMeasurementProjector (U e) b).trace.re) =
      (Fintype.card E : ℝ) := by
  simp_rw [sum_finiteUnitaryMeasurementProjector_bornWeight]
  simp

/-- Matrix pairing with the explicit forward channel equals the literal
finite overlap moment. -/
theorem trace_finiteUnitaryProjectiveDensityForward_mul_re
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ) :
    (finiteUnitaryProjectiveDensityForward U ρ * O).trace.re =
      finiteUnitaryProjectiveOverlapMoment U ρ O := by
  unfold finiteUnitaryProjectiveDensityForward
    finiteUnitaryProjectiveOverlapMoment
  simp only [Matrix.smul_mul, Finset.sum_mul, Matrix.trace_smul,
    Matrix.trace_sum]
  simp_rw [Matrix.trace_mul_comm
    (finiteUnitaryMeasurementProjector _ _) O]
  simp [Complex.real_smul, smul_eq_mul, Finset.mul_sum,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Algebraic expansion of the calibrated score's finite first moment. -/
theorem finiteUnitaryProjectiveScoreFirstMoment_eq_calibratedOverlap
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    finiteUnitaryProjectiveScoreFirstMoment U ρ u =
      ((D + 1 : ℕ) : ℝ) *
          finiteUnitaryProjectiveOverlapMoment U ρ
            (haarDirectionProjector u) - 1 := by
  unfold finiteUnitaryProjectiveScoreFirstMoment
    finiteUnitaryProjectiveScore finiteUnitaryProjectiveOverlapMoment
    haarCalibratedRankOneScore
  simp only [Fintype.card_fin, smul_eq_mul]
  have hsplit :
      (∑ e : E, ∑ b : Fin D,
        (((D + 1 : ℕ) : ℝ) *
            (haarDirectionProjector u *
              finiteUnitaryMeasurementProjector (U e) b).trace.re - 1) *
          (ρ.matrix *
            finiteUnitaryMeasurementProjector (U e) b).trace.re) =
        ((D + 1 : ℕ) : ℝ) *
          (∑ e : E, ∑ b : Fin D,
            (haarDirectionProjector u *
              finiteUnitaryMeasurementProjector (U e) b).trace.re *
            (ρ.matrix *
              finiteUnitaryMeasurementProjector (U e) b).trace.re) -
        (∑ e : E, ∑ b : Fin D,
          (ρ.matrix *
            finiteUnitaryMeasurementProjector (U e) b).trace.re) := by
    calc
      _ = ∑ e : E,
          (((D + 1 : ℕ) : ℝ) *
              (∑ b : Fin D,
                (haarDirectionProjector u *
                  finiteUnitaryMeasurementProjector (U e) b).trace.re *
                (ρ.matrix *
                  finiteUnitaryMeasurementProjector (U e) b).trace.re) -
            ∑ b : Fin D,
              (ρ.matrix *
                finiteUnitaryMeasurementProjector (U e) b).trace.re) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro b hb
          ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsplit,
    sum_finiteUnitaryMeasurementProjector_ensemble_bornWeight U ρ]
  have hcard : (Fintype.card E : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc :
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal *
          (Fintype.card E : ℝ) = 1 := by
    simp [ENNReal.toReal_inv, Fintype.card_ne_zero, hcard]
  rw [mul_sub, hc]
  ring

/-- The explicit calibrated channel has the corresponding calibrated overlap
as its quadratic prediction along a unit direction. -/
theorem channelQuadraticPrediction_finiteUnitaryCalibratedDensityChannel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    channelQuadraticPrediction
        (finiteUnitaryCalibratedDensityChannel U) ρ u =
      ((D + 1 : ℕ) : ℝ) *
          finiteUnitaryProjectiveOverlapMoment U ρ
            (haarDirectionProjector u) - 1 := by
  unfold channelQuadraticPrediction
  rw [← trace_mul_haarDirectionProjector_re]
  unfold finiteUnitaryCalibratedDensityChannel
  rw [sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul,
    Matrix.one_mul, haarDirectionProjector_trace_eq_one u hu]
  simp only [Complex.real_smul, Complex.sub_re, Complex.one_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  rw [trace_finiteUnitaryProjectiveDensityForward_mul_re]

set_option maxHeartbeats 600000 in
/-- The exact Born mean is the quadratic prediction of the explicit finite
ensemble channel. -/
theorem finiteUnitaryProjectiveScoreFirstMoment_eq_channelPrediction
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    finiteUnitaryProjectiveScoreFirstMoment U ρ u =
      channelQuadraticPrediction
        (finiteUnitaryCalibratedDensityChannel U) ρ u := by
  rw [finiteUnitaryProjectiveScoreFirstMoment_eq_calibratedOverlap,
    channelQuadraticPrediction_finiteUnitaryCalibratedDensityChannel U ρ u hu]

theorem integral_finiteUnitaryProjectiveScore_eq_channelPrediction
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    (∫ B, finiteUnitaryProjectiveScore u B
        ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      channelQuadraticPrediction
        (finiteUnitaryCalibratedDensityChannel U) ρ u := by
  rw [integral_finiteUnitaryProjectiveScore_eq_firstMoment]
  exact finiteUnitaryProjectiveScoreFirstMoment_eq_channelPrediction U ρ u hu

/-- Fully explicit variance identity for a unit direction, with the mean
written as the quadratic prediction of the finite ensemble channel. -/
theorem variance_finiteUnitaryProjectiveScore_eq_secondMoment_sub_prediction_sq
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      finiteUnitaryProjectiveScoreSecondMoment U ρ u -
        (channelQuadraticPrediction
          (finiteUnitaryCalibratedDensityChannel U) ρ u) ^ 2 := by
  rw [variance_finiteUnitaryProjectiveScore_eq_finiteMoments,
    finiteUnitaryProjectiveScoreFirstMoment_eq_channelPrediction U ρ u hu]

/-- The sole design-dependent scalar obligation needed for the shallow
variance constant `13`: a deterministic upper bound on the explicit finite
second-moment sum.  All measure-theoretic and variance algebra surrounding
this inequality is proved in this module. -/
def FiniteUnitaryProjectiveScoreSecondMomentBoundThirteen
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : Prop :=
  finiteUnitaryProjectiveScoreSecondMoment U ρ u ≤
    13 +
      (channelQuadraticPrediction
        (finiteUnitaryCalibratedDensityChannel U) ρ u) ^ 2

/-- Once the deterministic finite second-moment inequality is supplied by
the relative third-design theorem, the required variance bound follows
without any further probabilistic assumptions. -/
theorem variance_finiteUnitaryProjectiveScore_le_thirteen
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (hmoment : FiniteUnitaryProjectiveScoreSecondMomentBoundThirteen U ρ u) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) ≤ 13 := by
  rw [variance_finiteUnitaryProjectiveScore_eq_secondMoment_sub_prediction_sq
    hD U ρ u hu]
  unfold FiniteUnitaryProjectiveScoreSecondMomentBoundThirteen at hmoment
  linarith

end Score

end

end TomographyOracleCore
