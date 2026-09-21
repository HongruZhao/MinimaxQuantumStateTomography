import TomographyOracleCore.ProjectiveHaarFirstMoment
import TomographyOracleCore.PhysicalPOVM

namespace TomographyOracleCore

open MeasureTheory
open MatrixReduction
open PhysicalPOVM
open scoped BigOperators ComplexOrder MatrixOrder ENNReal

noncomputable section

/-!
# The exact complex-projective Haar POVM

The outcome is a rank-one projector `B`.  Its scalar base measure is the
normalized projective Haar law multiplied by the Hilbert-space dimension,
and its effect density is `B` itself.
-/

section OutcomeSpace

/-- Coordinate flattening is a genuine equivalence from square matrices to
their family of entries. -/
def complexMatrixCoordinatesEquiv (ι : Type*) :
    Matrix ι ι ℂ ≃ (ι × ι → ℂ) where
  toFun := complexMatrixCoordinates ι
  invFun := fun f i j ↦ f (i, j)
  left_inv A := rfl
  right_inv f := by
    funext p
    rcases p with ⟨i, j⟩
    rfl

/-- The coordinatewise measurable matrix space is standard Borel.  We use
the Polish topology transported along coordinate flattening. -/
noncomputable instance complexMatrixStandardBorelSpace
    (ι : Type*) [Fintype ι] :
    StandardBorelSpace (Matrix ι ι ℂ) := by
  let e := complexMatrixCoordinatesEquiv ι
  let τ : TopologicalSpace (Matrix ι ι ℂ) :=
    TopologicalSpace.induced e inferInstance
  have hB : @BorelSpace (Matrix ι ι ℂ) τ inferInstance := by
    constructor
    change MeasurableSpace.comap (complexMatrixCoordinates ι) inferInstance =
      @borel (Matrix ι ι ℂ) τ
    rw [show @borel (Matrix ι ι ℂ) τ =
        MeasurableSpace.comap e (borel (ι × ι → ℂ)) from borel_comap]
    have htarget :
        (inferInstance : MeasurableSpace (ι × ι → ℂ)) =
          borel (ι × ι → ℂ) := BorelSpace.measurable_eq
    rw [← htarget]
    rfl
  have hP : @PolishSpace (Matrix ι ι ℂ) τ := e.polishSpace_induced
  exact ⟨⟨τ, hB, hP⟩⟩

end OutcomeSpace

section AnalyticFields

variable {D : ℕ} [Nonempty (Fin D)]

/-- Dimension-scaled projective Haar base measure. -/
noncomputable def projectiveHaarPOVMBase :
    Measure (Matrix (Fin D) (Fin D) ℂ) :=
  (D : ℝ≥0∞) • complexProjectiveHaarLaw (Fin D)

/-- The effect density is the sampled rank-one projector itself. -/
def projectiveHaarPOVMEffect
    (B : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  B

theorem projectiveHaarPOVMBase_finite :
    IsFiniteMeasure (projectiveHaarPOVMBase (D := D)) := by
  unfold projectiveHaarPOVMBase
  exact (complexProjectiveHaarLaw (Fin D)).smul_finite (by simp)

theorem projectiveHaarPOVMEffect_measurable (i j : Fin D) :
    Measurable fun B : Matrix (Fin D) (Fin D) ℂ ↦
      projectiveHaarPOVMEffect B i j := by
  exact measurable_complexMatrix_apply (Fin D) i j

theorem projectiveHaarPOVMEffect_integrable (i j : Fin D) :
    Integrable
      (fun B : Matrix (Fin D) (Fin D) ℂ ↦
        projectiveHaarPOVMEffect B i j)
      (projectiveHaarPOVMBase (D := D)) := by
  unfold projectiveHaarPOVMBase projectiveHaarPOVMEffect
  exact (integrable_complexProjectiveHaar_coordinate (Fin D) i j).smul_measure
    (by simp)

theorem projectiveHaarPOVM_ae_posSemidef (hD : 0 < D) :
    ∀ᵐ B ∂projectiveHaarPOVMBase (D := D),
      (projectiveHaarPOVMEffect B).PosSemidef := by
  unfold projectiveHaarPOVMBase projectiveHaarPOVMEffect
  apply (Measure.ae_ennreal_smul_measure_iff (c := (D : ℝ≥0∞)) ?_).2
  · exact complexProjectiveHaar_ae_posSemidef (Fin D)
  · simpa using (Nat.ne_of_gt hD)

theorem projectiveHaarPOVM_ae_trace_one (hD : 0 < D) :
    ∀ᵐ B ∂projectiveHaarPOVMBase (D := D),
      (projectiveHaarPOVMEffect B).trace = 1 := by
  unfold projectiveHaarPOVMBase projectiveHaarPOVMEffect
  apply (Measure.ae_ennreal_smul_measure_iff (c := (D : ℝ≥0∞)) ?_).2
  · exact complexProjectiveHaar_ae_trace_eq_one (Fin D)
  · simpa using (Nat.ne_of_gt hD)

/-- The scaled first moment of each matrix coordinate is the corresponding
identity-matrix coordinate. -/
theorem integral_projectiveHaarPOVMEffect_coordinate (i j : Fin D) :
    (∫ B, projectiveHaarPOVMEffect B i j
        ∂projectiveHaarPOVMBase (D := D)) =
      if i = j then 1 else 0 := by
  unfold projectiveHaarPOVMBase projectiveHaarPOVMEffect
  rw [integral_smul_measure]
  simpa [Complex.real_smul] using
    card_mul_integral_complexProjectiveHaar_coordinate (Fin D) i j

/-- The trace pairing of two positive-semidefinite complex matrices has
nonnegative real part. -/
theorem trace_mul_re_nonnegative_of_posSemidef
    (A B : Matrix (Fin D) (Fin D) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  obtain ⟨X, hX⟩ :=
    CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hX]
  have htrace :
      ((star X * X) * B).trace = (X * B * star X).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [htrace, Matrix.star_eq_conjTranspose]
  exact (Complex.nonneg_iff.mp (hB.mul_mul_conjTranspose_same X).trace_nonneg).1

/-- The complex Born trace is integrable under the scaled projective Haar
base measure. -/
theorem integrable_projectiveHaarPOVM_bornTrace
    (ρ : DensityOperator (Fin D)) :
    Integrable
      (fun B : Matrix (Fin D) (Fin D) ℂ ↦ (ρ.matrix * B).trace)
      (projectiveHaarPOVMBase (D := D)) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  exact (projectiveHaarPOVMEffect_integrable (D := D) j i).const_mul
    (ρ.matrix i j)

/-- The dimension-scaled projective first moment normalizes every density
operator's complex Born trace to one. -/
theorem integral_projectiveHaarPOVM_bornTrace_eq_one
    (ρ : DensityOperator (Fin D)) :
    (∫ B, (ρ.matrix * B).trace
        ∂projectiveHaarPOVMBase (D := D)) = 1 := by
  have hcoordinate (i j : Fin D) :
      (∫ B, B i j ∂projectiveHaarPOVMBase (D := D)) =
        if i = j then 1 else 0 := by
    simpa only [projectiveHaarPOVMEffect] using
      integral_projectiveHaarPOVMEffect_coordinate (D := D) i j
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∫ B, ∑ i, ∑ j, ρ.matrix i j * B j i
        ∂projectiveHaarPOVMBase (D := D)) =
        ∑ i, ∫ B, ∑ j, ρ.matrix i j * B j i
          ∂projectiveHaarPOVMBase (D := D) := by
      rw [integral_finsetSum]
      intro i hi
      apply integrable_finsetSum Finset.univ
      intro j hj
      exact (projectiveHaarPOVMEffect_integrable (D := D) j i).const_mul
        (ρ.matrix i j)
    _ = ∑ i, ∑ j, ∫ B, ρ.matrix i j * B j i
          ∂projectiveHaarPOVMBase (D := D) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      intro j hj
      exact (projectiveHaarPOVMEffect_integrable (D := D) j i).const_mul
        (ρ.matrix i j)
    _ = 1 := by
      simp_rw [integral_const_mul, hcoordinate]
      simpa [Matrix.trace, eq_comm] using ρ.trace_eq_one

theorem integrable_projectiveHaarPOVM_bornTrace_re
    (ρ : DensityOperator (Fin D)) :
    Integrable
      (fun B : Matrix (Fin D) (Fin D) ℂ ↦ (ρ.matrix * B).trace.re)
      (projectiveHaarPOVMBase (D := D)) :=
  (integrable_projectiveHaarPOVM_bornTrace (D := D) ρ).re

theorem integral_projectiveHaarPOVM_bornTrace_re_eq_one
    (ρ : DensityOperator (Fin D)) :
    (∫ B, (ρ.matrix * B).trace.re
        ∂projectiveHaarPOVMBase (D := D)) = 1 := by
  have h := integral_re
    (integrable_projectiveHaarPOVM_bornTrace (D := D) ρ)
  rw [integral_projectiveHaarPOVM_bornTrace_eq_one (D := D) ρ] at h
  simpa only [RCLike.re_eq_complex_re, Complex.one_re] using h

/-- The joint Born density is measurable in the density operator and Haar
projector outcome. -/
theorem measurable_projectiveHaarPOVM_bornDensity_uncurry :
    Measurable
      (Function.uncurry
        (bornDensityFrom
          (projectiveHaarPOVMEffect (D := D)))) := by
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Function.uncurry_apply_pair, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ (fun i _ ↦
    Finset.measurable_sum Finset.univ (fun j _ ↦
      ((measurable_densityOperator_apply D i j).comp measurable_fst).mul
        ((measurable_complexMatrix_apply (Fin D) j i).comp measurable_snd)))

theorem measurable_projectiveHaarPOVM_bornMeasure :
    Measurable
      (bornMeasureFrom
        (projectiveHaarPOVMBase (D := D))
        (projectiveHaarPOVMEffect (D := D))) := by
  unfold bornMeasureFrom
  letI : IsFiniteMeasure (projectiveHaarPOVMBase (D := D)) :=
    projectiveHaarPOVMBase_finite (D := D)
  exact measurable_withDensity
    (measurable_projectiveHaarPOVM_bornDensity_uncurry (D := D))

theorem projectiveHaarPOVM_bornDensity_ae_nonnegative
    (hD : 0 < D) (ρ : DensityOperator (Fin D)) :
    ∀ᵐ B ∂projectiveHaarPOVMBase (D := D),
      0 ≤ (ρ.matrix * projectiveHaarPOVMEffect B).trace.re := by
  filter_upwards [projectiveHaarPOVM_ae_posSemidef (D := D) hD] with B hB
  exact trace_mul_re_nonnegative_of_posSemidef ρ.matrix B ρ.posSemidef hB

theorem projectiveHaarPOVM_born_probability
    (hD : 0 < D) (ρ : DensityOperator (Fin D)) :
    IsProbabilityMeasure
      (bornMeasureFrom
        (projectiveHaarPOVMBase (D := D))
        (projectiveHaarPOVMEffect (D := D)) ρ) := by
  constructor
  rw [bornMeasureFrom, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  unfold bornDensityFrom projectiveHaarPOVMEffect
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_projectiveHaarPOVM_bornTrace_re (D := D) ρ)
    (projectiveHaarPOVM_bornDensity_ae_nonnegative (D := D) hD ρ)]
  rw [integral_projectiveHaarPOVM_bornTrace_re_eq_one (D := D) ρ]
  norm_num

end AnalyticFields

/-- Exact physical POVM obtained by sampling a complex-projective Haar
rank-one projector and weighting its law by the dimension. -/
noncomputable def projectiveHaarPOVM (D : ℕ) (hD : 0 < D) :
    DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  refine
    { dimension_pos := hD
      base := projectiveHaarPOVMBase (D := D)
      base_finite := projectiveHaarPOVMBase_finite (D := D)
      effect := projectiveHaarPOVMEffect (D := D)
      effect_measurable := projectiveHaarPOVMEffect_measurable (D := D)
      effect_integrable := projectiveHaarPOVMEffect_integrable (D := D)
      effect_ae_posSemidef := projectiveHaarPOVM_ae_posSemidef (D := D) hD
      effect_ae_trace_one := projectiveHaarPOVM_ae_trace_one (D := D) hD
      integral_effect_eq_one := integral_projectiveHaarPOVMEffect_coordinate (D := D)
      born_density_ae_nonnegative :=
        projectiveHaarPOVM_bornDensity_ae_nonnegative (D := D) hD
      born_measurable := measurable_projectiveHaarPOVM_bornMeasure (D := D)
      born_probability := projectiveHaarPOVM_born_probability (D := D) hD }

end

end TomographyOracleCore
