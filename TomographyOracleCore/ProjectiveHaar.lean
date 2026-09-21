import TomographyOracleCore.HaarChannel
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-!
# A genuine normalized complex-projective Haar law

Mathlib constructs a finite measure on the unit sphere of a finite-dimensional
real normed space from any additive Haar measure.  This file normalizes that
measure, specializes it to finite-dimensional complex Euclidean space, and
pushes it forward by `x ↦ |x><x|`.

The construction and its probability normalization are unconditional.  The
projective two-moment contraction is deliberately isolated at the end as an
unasserted proposition: Mathlib supplies the Haar-to-sphere measure but not
the normalized complex projective moment formula.
-/

section NormalizedSphere

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- Unit-sphere law obtained from an additive Haar measure and normalized to
total mass one. -/
noncomputable def normalizedHaarSphereLaw
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    Measure (sphere (0 : E) 1) :=
  (μ.toSphere univ)⁻¹ • μ.toSphere

/-- The normalized Haar-to-sphere construction is a probability measure. -/
noncomputable instance normalizedHaarSphereLaw_isProbabilityMeasure
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    IsProbabilityMeasure (normalizedHaarSphereLaw μ) := by
  letI : NeZero μ.toSphere := ⟨μ.toSphere_ne_zero⟩
  exact MeasureTheory.isProbabilityMeasureSMul

@[simp] theorem normalizedHaarSphereLaw_apply_univ
    (μ : Measure E) [μ.IsAddHaarMeasure] :
    normalizedHaarSphereLaw μ univ = 1 := by
  exact IsProbabilityMeasure.measure_univ

end NormalizedSphere

section ComplexSphere

variable (ι : Type*) [Fintype ι] [Nonempty ι]

/-- The actual normalized unit-sphere law on finite-dimensional complex
Euclidean space, constructed from Mathlib's additive Haar `volume`. -/
noncomputable def complexUnitSphereHaarLaw :
    Measure (sphere (0 : EuclideanSpace ℂ ι) 1) :=
  normalizedHaarSphereLaw
    (volume : Measure (EuclideanSpace ℂ ι))

noncomputable instance complexUnitSphereHaarLaw_isProbabilityMeasure :
    IsProbabilityMeasure (complexUnitSphereHaarLaw ι) := by
  unfold complexUnitSphereHaarLaw
  infer_instance

@[simp] theorem complexUnitSphereHaarLaw_apply_univ :
    complexUnitSphereHaarLaw ι univ = 1 := by
  exact IsProbabilityMeasure.measure_univ

end ComplexSphere

/-! ## Canonical coordinatewise measurable matrices -/

/-- Flatten a complex square matrix into its finite family of coordinates. -/
def complexMatrixCoordinates (ι : Type*)
    (A : Matrix ι ι ℂ) : ι × ι → ℂ :=
  fun p ↦ A p.1 p.2

/-- Coordinatewise measurable structure used for actual matrix-valued random
variables.  It is the direct matrix analogue of the density-operator
measurable structure in `PhysicalPOVM`. -/
noncomputable instance complexMatrixMeasurableSpace (ι : Type*) :
    MeasurableSpace (Matrix ι ι ℂ) :=
  MeasurableSpace.comap (complexMatrixCoordinates ι) inferInstance

theorem measurable_complexMatrixCoordinates (ι : Type*) :
    Measurable (complexMatrixCoordinates ι) :=
  measurable_iff_comap_le.mpr le_rfl

section ProjectorMap

variable {ι : Type*} [Fintype ι]

/-- Rank-one projector `|x><x|` associated with a complex unit vector. -/
noncomputable def complexSphereProjector
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (fun i ↦ x.1 i) (star fun i ↦ x.1 i)

@[simp] theorem complexSphereProjector_apply
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) (i j : ι) :
    complexSphereProjector x i j = x.1 i * star (x.1 j) := by
  rfl

/-- The rank-one-projector map is measurable for the coordinatewise matrix
sigma algebra. -/
theorem measurable_complexSphereProjector :
    Measurable (complexSphereProjector (ι := ι)) := by
  rw [measurable_iff_comap_le, complexMatrixMeasurableSpace,
    MeasurableSpace.comap_comp]
  apply Measurable.comap_le
  apply measurable_pi_lambda
  intro p
  change Measurable
    (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
      x.1 p.1 * star (x.1 p.2))
  fun_prop

theorem complexSphereProjector_posSemidef
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexSphereProjector x).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem complexSphereProjector_isHermitian
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexSphereProjector x).IsHermitian :=
  (complexSphereProjector_posSemidef x).isHermitian

theorem complexSphereProjector_rank_le_one
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexSphereProjector x).rank ≤ 1 := by
  exact Matrix.rank_vecMulVec_le _ _

/-- Every matrix in the image of the projective map has trace one. -/
theorem complexSphereProjector_trace_eq_one
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexSphereProjector x).trace = 1 := by
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [mem_sphere] using x.2
  have hsquares : ∑ i, ‖x.1 i‖ ^ 2 = (1 : ℝ) := by
    have h := EuclideanSpace.norm_sq_eq x.1
    rw [hxnorm] at h
    simpa using h.symm
  rw [complexSphereProjector, Matrix.trace_vecMulVec]
  simp only [dotProduct, Pi.star_apply, starRingEnd_apply]
  calc
    (∑ i, x.1 i * star (x.1 i)) =
        ∑ i, ((‖x.1 i‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i hi
      change x.1 i * (starRingEnd ℂ) (x.1 i) =
        ((‖x.1 i‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.mul_conj, ← Complex.sq_norm]
    _ = ((∑ i, ‖x.1 i‖ ^ 2 : ℝ) : ℂ) := by
      exact (Complex.ofReal_sum Finset.univ
        (fun i ↦ ‖x.1 i‖ ^ 2)).symm
    _ = 1 := by rw [hsquares]; norm_num

/-- The sampled projector, bundled as an actual density operator. -/
noncomputable def complexSpherePureState
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    MatrixReduction.DensityOperator ι where
  matrix := complexSphereProjector x
  posSemidef := complexSphereProjector_posSemidef x
  trace_eq_one := complexSphereProjector_trace_eq_one x

end ProjectorMap

section ProjectiveLaw

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Genuine complex-projective Haar probability law: normalize the
Haar-to-sphere measure and push it forward by `x ↦ |x><x|`. -/
noncomputable def complexProjectiveHaarLaw :
    Measure (Matrix ι ι ℂ) :=
  (complexUnitSphereHaarLaw ι).map
    (complexSphereProjector (ι := ι))

noncomputable instance complexProjectiveHaarLaw_isProbabilityMeasure :
    IsProbabilityMeasure (complexProjectiveHaarLaw ι) := by
  unfold complexProjectiveHaarLaw
  exact Measure.isProbabilityMeasure_map
    (measurable_complexSphereProjector (ι := ι)).aemeasurable

@[simp] theorem complexProjectiveHaarLaw_apply_univ :
    complexProjectiveHaarLaw ι univ = 1 := by
  exact IsProbabilityMeasure.measure_univ

/-- The precise first missing analytic theorem.  It is a proposition about
the concrete probability measure constructed above; no value of this
proposition is postulated here. -/
def ComplexProjectiveTwoMomentTheorem : Prop :=
  ProjectiveTwoMomentContraction (complexProjectiveHaarLaw ι)

/-- If the missing projective moment theorem is subsequently proved, the
concrete projective Haar forward channel is exactly the closed form. -/
theorem complexProjectiveHaarForward_eq_closedForm
    (hmoment : ComplexProjectiveTwoMomentTheorem (ι := ι))
    (A : Matrix ι ι ℂ) :
    projectiveBasisForward (complexProjectiveHaarLaw ι) A =
      haarBasisForwardClosedForm A := by
  exact projectiveBasisForward_eq_closedForm _ hmoment A

/-- Conditional calibrated identity for the now-concrete projective law.
The only remaining premise is the literal two-moment theorem above. -/
theorem calibrated_complexProjectiveHaarForward_eq
    (hmoment : ComplexProjectiveTwoMomentTheorem (ι := ι))
    (A : Matrix ι ι ℂ) :
    haarDimensionPlusOne (ι := ι) •
          projectiveBasisForward (complexProjectiveHaarLaw ι) A -
        A.trace • (1 : Matrix ι ι ℂ) = A := by
  exact calibrated_projectiveBasisForward_eq _ hmoment A

end ProjectiveLaw

end TomographyOracleCore
