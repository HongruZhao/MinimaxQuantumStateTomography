import TomographyOracleCore.ProjectiveHaar
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator Pointwise

/-!
# Unconditional invariance and coordinate consequences for projective Haar

The normalized sphere law in `ProjectiveHaar` is obtained from Mathlib's
`Measure.toSphere`.  Here we prove that this construction is invariant under
real linear isometries whenever the ambient Haar measure is invariant.  This
is the first analytic bridge required for a derivation of the complex
projective two-moment formula.

No projective moment formula is assumed or postulated in this file.
-/

section SphereInvariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [Nontrivial E]

/-- Action induced by a real linear isometry on the unit sphere. -/
noncomputable def unitSphereLinearIsometryAction
    (e : E ≃ₗᵢ[ℝ] E) : sphere (0 : E) 1 → sphere (0 : E) 1 :=
  fun x ↦ ⟨e x.1, by simpa [mem_sphere] using x.2⟩

@[simp] theorem unitSphereLinearIsometryAction_coe
    (e : E ≃ₗᵢ[ℝ] E) (x : sphere (0 : E) 1) :
    (unitSphereLinearIsometryAction e x : E) = e x.1 :=
  rfl

theorem measurable_unitSphereLinearIsometryAction
    (e : E ≃ₗᵢ[ℝ] E) :
    Measurable (unitSphereLinearIsometryAction e) := by
  unfold unitSphereLinearIsometryAction
  exact ((e.continuous.comp continuous_subtype_val).subtype_mk _).measurable

/-- A measurable subset of the unit sphere generates a measurable radial
sector in the ambient space. -/
theorem measurableSet_unitSphereSector
    {s : Set (sphere (0 : E) 1)} (hs : MeasurableSet s) :
    MeasurableSet (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
  let r : Ioi (0 : ℝ) := ⟨1, by simp⟩
  let h : ↑({0} : Set E)ᶜ ≃ₜ
      sphere (0 : E) 1 × Ioi (0 : ℝ) :=
    homeomorphUnitSphereProd E
  have hprod : MeasurableSet (s ×ˢ Iio r) :=
    hs.prod measurableSet_Iio
  have hemb : MeasurableEmbedding
      (Subtype.val ∘ h.symm :
        sphere (0 : E) 1 × Ioi (0 : ℝ) → E) :=
    (MeasurableEmbedding.subtype_coe
      (measurableSet_singleton (0 : E)).compl).comp
        (Homeomorph.measurableEmbedding h.symm)
  have himage : MeasurableSet
      ((Subtype.val ∘ h.symm) '' (s ×ˢ Iio r)) :=
    hemb.measurableSet_image' hprod
  have hset :
      Ioo (0 : ℝ) 1 • ((↑) '' s : Set E) =
        (Subtype.val ∘ h.symm) '' (s ×ˢ Iio r) := by
    change Ioo (0 : ℝ) (r : ℝ) • ((↑) '' s : Set E) =
      (Subtype.val ∘ h.symm) '' (s ×ˢ Iio r)
    rw [← image2_smul, image2_image_right,
      ← image_subtype_val_Ioi_Iio, image2_image_left,
      image2_swap, ← image_prod]
    rfl
  rw [hset]
  exact himage

/-- Radial sectors commute with a real linear isometry. -/
theorem unitSphereSector_preimage
    (e : E ≃ₗᵢ[ℝ] E) (s : Set (sphere (0 : E) 1)) :
    Ioo (0 : ℝ) 1 •
          ((↑) '' (unitSphereLinearIsometryAction e ⁻¹' s) : Set E) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)) := by
  ext y
  constructor
  · rintro ⟨r, hr, z, ⟨x, hx, rfl⟩, rfl⟩
    change e (r • x.1) ∈
      Ioo (0 : ℝ) 1 • ((↑) '' s : Set E)
    exact ⟨r, hr, e x.1, ⟨unitSphereLinearIsometryAction e x, hx, rfl⟩,
      by simp⟩
  · intro hy
    change e y ∈ Ioo (0 : ℝ) 1 • ((↑) '' s : Set E) at hy
    rcases hy with ⟨r, hr, z, ⟨x, hx, rfl⟩, hrey⟩
    let x' : sphere (0 : E) 1 := unitSphereLinearIsometryAction e.symm x
    refine ⟨r, hr, x'.1, ⟨x', ?_, rfl⟩, ?_⟩
    · change unitSphereLinearIsometryAction e x' ∈ s
      simpa [x', unitSphereLinearIsometryAction] using hx
    · apply e.injective
      simpa [x', unitSphereLinearIsometryAction] using hrey

/-- The unnormalized `toSphere` measure is invariant under any ambient
volume-preserving real linear isometry. -/
theorem toSphere_map_unitSphereLinearIsometryAction
    (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map (unitSphereLinearIsometryAction e)
        ((volume : Measure E).toSphere) =
      (volume : Measure E).toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply (measurable_unitSphereLinearIsometryAction e) hs,
    Measure.toSphere_apply' _ (hs.preimage
      (measurable_unitSphereLinearIsometryAction e)),
    Measure.toSphere_apply' _ hs,
    unitSphereSector_preimage]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving e).measure_preimage
    (measurableSet_unitSphereSector hs).nullMeasurableSet

/-- Consequently the normalized sphere probability law is invariant under
every real linear isometry. -/
theorem normalizedHaarSphereLaw_map_linearIsometry
    (e : E ≃ₗᵢ[ℝ] E) :
    Measure.map (unitSphereLinearIsometryAction e)
        (normalizedHaarSphereLaw (volume : Measure E)) =
      normalizedHaarSphereLaw (volume : Measure E) := by
  unfold normalizedHaarSphereLaw
  rw [Measure.map_smul, toSphere_map_unitSphereLinearIsometryAction]

end SphereInvariance

/-! ## The matrix sigma algebra is the finite-dimensional Borel algebra -/

section MatrixBorel

variable (ι : Type*) [Fintype ι]

theorem complexMatrixCoordinates_injective :
    Function.Injective (complexMatrixCoordinates ι) := by
  intro A B h
  ext i j
  exact congrFun h (i, j)

theorem complexMatrixCoordinates_surjective :
    Function.Surjective (complexMatrixCoordinates ι) := by
  intro f
  exact ⟨fun i j ↦ f (i, j), rfl⟩

theorem measurableEmbedding_complexMatrixCoordinates :
    MeasurableEmbedding (complexMatrixCoordinates ι) := by
  rw [MeasurableEmbedding.iff_comap_eq]
  refine ⟨complexMatrixCoordinates_injective ι, ?_, ?_⟩
  · rfl
  · rw [(complexMatrixCoordinates_surjective ι).range_eq]
    exact MeasurableSet.univ

theorem isInducing_complexMatrixCoordinates :
    Topology.IsInducing (complexMatrixCoordinates ι) := by
  let e : Matrix ι ι ℂ ≃ₗ[ℂ] (ι × ι → ℂ) :=
    (LinearEquiv.curry ℂ ℂ ι ι).symm
  change Topology.IsInducing
    (fun A : Matrix ι ι ℂ ↦ Function.uncurry A)
  have hind := e.toContinuousLinearEquiv.toHomeomorph.isInducing
  change Topology.IsInducing
    (e.toContinuousLinearEquiv : Matrix ι ι ℂ → (ι × ι → ℂ)) at hind
  have hfun :
      (e.toContinuousLinearEquiv : Matrix ι ι ℂ → (ι × ι → ℂ)) =
        (fun A : Matrix ι ι ℂ ↦ Function.uncurry A) := by
    funext A p
    rfl
  rwa [hfun] at hind

/-- The coordinatewise matrix measurable structure introduced in
`ProjectiveHaar` is exactly the Borel sigma algebra of the finite-dimensional
matrix norm topology. -/
noncomputable instance complexMatrixBorelSpace :
    BorelSpace (Matrix ι ι ℂ) :=
  (measurableEmbedding_complexMatrixCoordinates ι).borelSpace
    (isInducing_complexMatrixCoordinates ι)

theorem measurable_complexMatrix_apply (i j : ι) :
    Measurable (fun A : Matrix ι ι ℂ ↦ A i j) := by
  exact (measurable_pi_apply (i, j)).comp
    (measurable_complexMatrixCoordinates ι)

end MatrixBorel

/-! ## Concrete unitary-coordinate invariance -/

section ComplexSphereInvariance

variable (ι : Type*) [Fintype ι] [Nonempty ι]

/-- Independent coordinate phases, regarded as a real linear isometry of
complex Euclidean space. -/
noncomputable def complexCoordinatePhaseIsometry (u : ι → Circle) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun i ↦ rotation (u i))

@[simp] theorem complexCoordinatePhaseIsometry_apply
    (u : ι → Circle) (x : EuclideanSpace ℂ ι) (i : ι) :
    complexCoordinatePhaseIsometry ι u x i = (u i : ℂ) * x i := by
  rfl

/-- The actual normalized complex sphere law is invariant under every real
linear isometry, hence in particular under every unitary transformation. -/
theorem complexUnitSphereHaarLaw_map_linearIsometry
    (e : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι) :
    Measure.map (unitSphereLinearIsometryAction e)
        (complexUnitSphereHaarLaw ι) =
      complexUnitSphereHaarLaw ι := by
  unfold complexUnitSphereHaarLaw
  exact normalizedHaarSphereLaw_map_linearIsometry e

theorem complexUnitSphereHaarLaw_map_coordinatePhase (u : ι → Circle) :
    Measure.map
        (unitSphereLinearIsometryAction
          (complexCoordinatePhaseIsometry ι u))
        (complexUnitSphereHaarLaw ι) =
      complexUnitSphereHaarLaw ι :=
  complexUnitSphereHaarLaw_map_linearIsometry ι
    (complexCoordinatePhaseIsometry ι u)

/-- Integral form of complex-sphere invariance, for continuous scalar
observables. -/
theorem integral_comp_complexUnitSphereHaarLaw_linearIsometry
    (e : EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι)
    (f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ)
    (hf : Continuous f) :
    ∫ x, f (unitSphereLinearIsometryAction e x)
        ∂complexUnitSphereHaarLaw ι =
      ∫ x, f x ∂complexUnitSphereHaarLaw ι := by
  calc
    ∫ x, f (unitSphereLinearIsometryAction e x)
        ∂complexUnitSphereHaarLaw ι =
        ∫ y, f y ∂Measure.map
          (unitSphereLinearIsometryAction e)
          (complexUnitSphereHaarLaw ι) := by
      symm
      exact integral_map
        (measurable_unitSphereLinearIsometryAction e).aemeasurable
        hf.aestronglyMeasurable
    _ = ∫ x, f x ∂complexUnitSphereHaarLaw ι := by
      rw [complexUnitSphereHaarLaw_map_linearIsometry]

end ComplexSphereInvariance

/-! ## Coordinate permutations and a concrete two-coordinate unitary -/

section ComplexCoordinateMixing

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Reindexing coordinates is a real linear isometry of complex Euclidean
space. -/
noncomputable def complexCoordinatePermutationIsometry (e : ι ≃ ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℂ e

@[simp] theorem complexCoordinatePermutationIsometry_apply
    (e : ι ≃ ι) (x : EuclideanSpace ℂ ι) (i : ι) :
    complexCoordinatePermutationIsometry ι e x (e i) = x i := by
  simp [complexCoordinatePermutationIsometry,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- A complex linear isometry can be viewed as a real linear isometry without
changing its underlying function. -/
noncomputable def complexLinearIsometryEquivToReal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : E ≃ₗᵢ[ℂ] E) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
  norm_map' := e.norm_map

@[simp] theorem complexLinearIsometryEquivToReal_apply
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (e : E ≃ₗᵢ[ℂ] E) (x : E) :
    complexLinearIsometryEquivToReal e x = e x :=
  rfl

/-- Vector spanning a line whose reflection mixes two coordinates by the
rational orthogonal matrix `[[3/5,4/5],[4/5,-3/5]]`. -/
noncomputable def complexTwoCoordinateMixVector (i j : ι) :
    EuclideanSpace ℂ ι :=
  (2 : ℂ) • EuclideanSpace.single i (1 : ℂ) +
    EuclideanSpace.single j (1 : ℂ)

@[simp] theorem complexTwoCoordinateMixVector_apply_left
    (i j : ι) (hij : i ≠ j) :
    complexTwoCoordinateMixVector ι i j i = 2 := by
  simp [complexTwoCoordinateMixVector, hij]

@[simp] theorem complexTwoCoordinateMixVector_apply_right
    (i j : ι) (hij : i ≠ j) :
    complexTwoCoordinateMixVector ι i j j = 1 := by
  simp [complexTwoCoordinateMixVector, Ne.symm hij]

theorem complexTwoCoordinateMixVector_norm_sq
    (i j : ι) (hij : i ≠ j) :
    ‖complexTwoCoordinateMixVector ι i j‖ ^ 2 = 5 := by
  unfold complexTwoCoordinateMixVector
  rw [pow_two,
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)]
  · simp only [norm_smul, PiLp.norm_single, norm_one, mul_one]
    norm_num
  · rw [inner_smul_left, EuclideanSpace.inner_single_left]
    simp [hij]

theorem complexTwoCoordinateMixVector_inner
    (i j : ι) (x : EuclideanSpace ℂ ι) :
    inner ℂ (complexTwoCoordinateMixVector ι i j) x =
      2 * x i + x j := by
  simp [complexTwoCoordinateMixVector,
    EuclideanSpace.inner_single_left]
  ring

/-- The concrete two-coordinate complex-linear reflection. -/
noncomputable def complexTwoCoordinateMixIsometry (i j : ι) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  (ℂ ∙ complexTwoCoordinateMixVector ι i j).reflection

theorem complexTwoCoordinateMixIsometry_apply_left
    (i j : ι) (hij : i ≠ j) (x : EuclideanSpace ℂ ι) :
    complexTwoCoordinateMixIsometry ι i j x i =
      (3 / 5 : ℂ) * x i + (4 / 5 : ℂ) * x j := by
  rw [complexTwoCoordinateMixIsometry,
    Submodule.reflection_singleton_apply,
    complexTwoCoordinateMixVector_inner]
  simp only [PiLp.sub_apply, PiLp.smul_apply,
    complexTwoCoordinateMixVector_apply_left ι i j hij]
  rw [← RCLike.ofReal_pow (K := ℂ),
    complexTwoCoordinateMixVector_norm_sq ι i j hij]
  norm_num
  ring

theorem complexTwoCoordinateMixIsometry_apply_right
    (i j : ι) (hij : i ≠ j) (x : EuclideanSpace ℂ ι) :
    complexTwoCoordinateMixIsometry ι i j x j =
      (4 / 5 : ℂ) * x i - (3 / 5 : ℂ) * x j := by
  rw [complexTwoCoordinateMixIsometry,
    Submodule.reflection_singleton_apply,
    complexTwoCoordinateMixVector_inner]
  simp only [PiLp.sub_apply, PiLp.smul_apply,
    complexTwoCoordinateMixVector_apply_right ι i j hij]
  rw [← RCLike.ofReal_pow (K := ℂ),
    complexTwoCoordinateMixVector_norm_sq ι i j hij]
  norm_num
  ring

/-- Expansion of the left diagonal projector coordinate after the concrete
two-coordinate reflection. -/
theorem complexSphereProjector_mix_left_diagonal
    (i j : ι) (hij : i ≠ j)
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    complexSphereProjector
        (unitSphereLinearIsometryAction
          (complexLinearIsometryEquivToReal
            (complexTwoCoordinateMixIsometry ι i j)) x) i i =
      (9 / 25 : ℂ) * complexSphereProjector x i i +
      (16 / 25 : ℂ) * complexSphereProjector x j j +
      (12 / 25 : ℂ) *
        (complexSphereProjector x i j + complexSphereProjector x j i) := by
  simp only [complexSphereProjector_apply,
    unitSphereLinearIsometryAction_coe,
    complexLinearIsometryEquivToReal_apply,
    complexTwoCoordinateMixIsometry_apply_left ι i j hij]
  rw [star_add, star_mul, star_mul]
  norm_num
  ring

end ComplexCoordinateMixing

/-! ## Coordinate second moments and phase-selection rules -/

section CoordinateMoments

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem continuous_complexSphereProjector_apply (i j : ι) :
    Continuous (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
      complexSphereProjector x i j) := by
  change Continuous (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
    x.1 i * star (x.1 j))
  fun_prop

/-- The actual fourth-order coordinate moment of a complex unit vector,
written as a second moment of its rank-one projector. -/
noncomputable def complexSphereProjectorSecondMoment
    (i j k l : ι) : ℂ :=
  ∫ x, complexSphereProjector x i j * complexSphereProjector x k l
    ∂complexUnitSphereHaarLaw ι

/-- Every projector-coordinate product is integrable on the compact unit
sphere. -/
theorem integrable_complexSphereProjectorSecondMoment
    (i j k l : ι) :
    Integrable
      (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
        complexSphereProjector x i j * complexSphereProjector x k l)
      (complexUnitSphereHaarLaw ι) := by
  have hc := (continuous_complexSphereProjector_apply ι i j).mul
    (continuous_complexSphereProjector_apply ι k l)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

/-- Coordinate moments are invariant under simultaneous permutation of all
four indices. -/
theorem complexSphereProjectorSecondMoment_permute
    (e : ι ≃ ι) (i j k l : ι) :
    complexSphereProjectorSecondMoment ι (e i) (e j) (e k) (e l) =
      complexSphereProjectorSecondMoment ι i j k l := by
  let f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    complexSphereProjector x (e i) (e j) *
      complexSphereProjector x (e k) (e l)
  have hf : Continuous f :=
    (continuous_complexSphereProjector_apply ι (e i) (e j)).mul
      (continuous_complexSphereProjector_apply ι (e k) (e l))
  have hinv := integral_comp_complexUnitSphereHaarLaw_linearIsometry ι
    (complexCoordinatePermutationIsometry ι e) f hf
  have hfun :
      (fun x ↦ f (unitSphereLinearIsometryAction
        (complexCoordinatePermutationIsometry ι e) x)) =
      (fun x ↦ complexSphereProjector x i j *
        complexSphereProjector x k l) := by
    funext x
    simp [f, complexSphereProjector_apply,
      complexCoordinatePermutationIsometry]
  rw [hfun] at hinv
  exact hinv.symm

/-- All single-coordinate fourth moments are equal. -/
theorem complexSphereProjectorSecondMoment_diagonal_eq
    (i j : ι) :
    complexSphereProjectorSecondMoment ι i i i i =
      complexSphereProjectorSecondMoment ι j j j j := by
  have h := complexSphereProjectorSecondMoment_permute ι
    (Equiv.swap i j) i i i i
  simpa using h.symm

/-- For a rank-one projector, the off-diagonal swap product agrees
pointwise with the corresponding product of diagonal entries. -/
theorem complexSphereProjectorSecondMoment_offdiag_swap_eq_diagonal
    (i j : ι) :
    complexSphereProjectorSecondMoment ι i j j i =
      complexSphereProjectorSecondMoment ι i i j j := by
  unfold complexSphereProjectorSecondMoment
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [complexSphereProjector_apply]
  ring

/-- The same coordinate moment expressed directly under the pushed-forward
projective probability law. -/
theorem complexProjectiveHaar_coordinateSecondMoment_eq_sphere
    (i j k l : ι) :
    ∫ B, B i j * B k l ∂complexProjectiveHaarLaw ι =
      complexSphereProjectorSecondMoment ι i j k l := by
  have hf : Measurable (fun B : Matrix ι ι ℂ ↦ B i j * B k l) :=
    (measurable_complexMatrix_apply ι i j).mul
      (measurable_complexMatrix_apply ι k l)
  unfold complexProjectiveHaarLaw complexSphereProjectorSecondMoment
  exact integral_map
    (measurable_complexSphereProjector (ι := ι)).aemeasurable
    hf.aestronglyMeasurable

/-- Phase acquired by the `(i,j;k,l)` projector-coordinate second moment
under independent coordinate rotations. -/
noncomputable def projectorSecondMomentPhase
    (u : ι → Circle) (i j k l : ι) : ℂ :=
  (u i : ℂ) * star (u j : ℂ) *
    (u k : ℂ) * star (u l : ℂ)

/-- The sign rotation in one coordinate. -/
noncomputable def complexCoordinateSignPhase (q : ι) : ι → Circle :=
  fun r ↦ if r = q then (-1 : Circle) else 1

/-- Multiplication by `i` in one coordinate. -/
noncomputable def complexCoordinateIPhase (q : ι) : ι → Circle :=
  fun r ↦ if r = q then
    ⟨Complex.I, by change dist Complex.I 0 = 1; simp⟩
  else 1

/-- Pointwise covariance of a rank-one projector coordinate under independent
coordinate phases. -/
theorem complexSphereProjector_coordinatePhase_apply
    (u : ι → Circle)
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) (i j : ι) :
    complexSphereProjector
        (unitSphereLinearIsometryAction
          (complexCoordinatePhaseIsometry ι u) x) i j =
      ((u i : ℂ) * star (u j : ℂ)) *
        complexSphereProjector x i j := by
  simp only [complexSphereProjector_apply,
    unitSphereLinearIsometryAction_coe,
    complexCoordinatePhaseIsometry_apply]
  change (u i : ℂ) * x.1 i *
      (starRingEnd ℂ) ((u j : ℂ) * x.1 j) =
    (u i : ℂ) * (starRingEnd ℂ) (u j : ℂ) *
      (x.1 i * (starRingEnd ℂ) (x.1 j))
  rw [map_mul]
  ring

/-- Exact phase-selection equation for every fourth-order coordinate moment.
This is an unconditional consequence of the proved sphere invariance. -/
theorem complexSphereProjectorSecondMoment_phase_covariant
    (u : ι → Circle) (i j k l : ι) :
    projectorSecondMomentPhase ι u i j k l *
        complexSphereProjectorSecondMoment ι i j k l =
      complexSphereProjectorSecondMoment ι i j k l := by
  let f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ :=
    fun x ↦ complexSphereProjector x i j * complexSphereProjector x k l
  have hf : Continuous f :=
    (continuous_complexSphereProjector_apply ι i j).mul
      (continuous_complexSphereProjector_apply ι k l)
  have hinv := integral_comp_complexUnitSphereHaarLaw_linearIsometry ι
    (complexCoordinatePhaseIsometry ι u) f hf
  have hfun :
      (fun x ↦ f (unitSphereLinearIsometryAction
        (complexCoordinatePhaseIsometry ι u) x)) =
      (fun x ↦ projectorSecondMomentPhase ι u i j k l * f x) := by
    funext x
    simp only [f, complexSphereProjector_coordinatePhase_apply,
      projectorSecondMomentPhase]
    ring
  rw [hfun, integral_const_mul] at hinv
  simpa [complexSphereProjectorSecondMoment, f] using hinv

/-- Any coordinate moment carrying a nontrivial independent phase vanishes.
This single theorem discharges all index patterns for which one can exhibit
a coordinate phase with non-unit total weight. -/
theorem complexSphereProjectorSecondMoment_eq_zero_of_phase
    (u : ι → Circle) (i j k l : ι)
    (hphase : projectorSecondMomentPhase ι u i j k l ≠ 1) :
    complexSphereProjectorSecondMoment ι i j k l = 0 := by
  have hcov := complexSphereProjectorSecondMoment_phase_covariant
    ι u i j k l
  have hmul :
      (projectorSecondMomentPhase ι u i j k l - 1) *
          complexSphereProjectorSecondMoment ι i j k l = 0 := by
    calc
      _ = projectorSecondMomentPhase ι u i j k l *
            complexSphereProjectorSecondMoment ι i j k l -
          complexSphereProjectorSecondMoment ι i j k l := by ring
      _ = 0 := by rw [hcov]; ring
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hphase)

private theorem complex_I_ne_one : Complex.I ≠ (1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- Every non-balanced fourth coordinate moment vanishes.  The two balanced
patterns are exactly `(i = j, k = l)` and `(i = l, k = j)`. -/
theorem complexSphereProjectorSecondMoment_eq_zero_of_not_balanced
    (i j k l : ι)
    (hbad : ¬ ((i = j ∧ k = l) ∨ (i = l ∧ k = j))) :
    complexSphereProjectorSecondMoment ι i j k l = 0 := by
  by_cases hij : i = j
  · subst j
    have hkl : k ≠ l := by
      intro h
      exact hbad (Or.inl ⟨rfl, h⟩)
    apply complexSphereProjectorSecondMoment_eq_zero_of_phase
      ι (complexCoordinateIPhase ι k) i i k l
    by_cases hik : i = k
    · subst i
      simp [projectorSecondMomentPhase, complexCoordinateIPhase,
        Ne.symm hkl, complex_I_ne_one]
    · simp [projectorSecondMomentPhase, complexCoordinateIPhase,
        hik, Ne.symm hkl, complex_I_ne_one]
  · by_cases hil : i = l
    · subst l
      have hkj : k ≠ j := by
        intro h
        exact hbad (Or.inr ⟨rfl, h⟩)
      apply complexSphereProjectorSecondMoment_eq_zero_of_phase
        ι (complexCoordinateIPhase ι k) i j k i
      by_cases hik : i = k
      · subst i
        simp [projectorSecondMomentPhase, complexCoordinateIPhase,
          Ne.symm hkj, complex_I_ne_one]
      · simp [projectorSecondMomentPhase, complexCoordinateIPhase,
          hik, Ne.symm hkj, complex_I_ne_one]
    · apply complexSphereProjectorSecondMoment_eq_zero_of_phase
        ι (complexCoordinateIPhase ι i) i j k l
      by_cases hki : k = i
      · subst k
        simp [projectorSecondMomentPhase, complexCoordinateIPhase,
          Ne.symm hij, Ne.symm hil]
        norm_num
      · simp [projectorSecondMomentPhase, complexCoordinateIPhase,
          Ne.symm hij, Ne.symm hil, hki, complex_I_ne_one]

/-- A moment with one unmatched coordinate occurrence vanishes. -/
theorem complexSphereProjectorSecondMoment_three_one_eq_zero
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorSecondMoment ι i i i j = 0 := by
  apply complexSphereProjectorSecondMoment_eq_zero_of_phase ι
    (complexCoordinateSignPhase ι j)
  simp [projectorSecondMomentPhase, complexCoordinateSignPhase, hij]
  norm_num

/-- A moment containing the same off-diagonal projector coordinate twice
vanishes. -/
theorem complexSphereProjectorSecondMoment_offdiag_square_eq_zero
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorSecondMoment ι i j i j = 0 := by
  apply complexSphereProjectorSecondMoment_eq_zero_of_phase ι
    (complexCoordinateIPhase ι i)
  simp [projectorSecondMomentPhase, complexCoordinateIPhase, Ne.symm hij]
  norm_num [Complex.I_mul_I]

/-- Projective-law version of the phase-selection vanishing rule. -/
theorem complexProjectiveHaar_coordinateSecondMoment_eq_zero_of_phase
    (u : ι → Circle) (i j k l : ι)
    (hphase : projectorSecondMomentPhase ι u i j k l ≠ 1) :
    ∫ B, B i j * B k l ∂complexProjectiveHaarLaw ι = 0 := by
  rw [complexProjectiveHaar_coordinateSecondMoment_eq_sphere]
  exact complexSphereProjectorSecondMoment_eq_zero_of_phase
    ι u i j k l hphase

/-! ## Integrability and coordinate evaluation of the matrix observable -/

/-- The rank-one-projector map is continuous in the finite-dimensional
matrix norm topology. -/
theorem continuous_complexSphereProjector :
    Continuous (complexSphereProjector (ι := ι)) := by
  unfold complexSphereProjector
  fun_prop

/-- The trace-weighted matrix observable occurring in the forward channel is
continuous. -/
theorem continuous_trace_smul_matrix (A : Matrix ι ι ℂ) :
    Continuous (fun B : Matrix ι ι ℂ ↦ (A * B).trace • B) := by
  fun_prop

/-- On the compact unit sphere, the trace-weighted projector observable is
Bochner integrable for the normalized Haar-to-sphere law. -/
theorem integrable_complexSphere_trace_smul_projector
    (A : Matrix ι ι ℂ) :
    Integrable
      (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
        (A * complexSphereProjector x).trace • complexSphereProjector x)
      (complexUnitSphereHaarLaw ι) := by
  have hc := (continuous_trace_smul_matrix ι A).comp
    (continuous_complexSphereProjector ι)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

/-- The actual trace-weighted observable is integrable under the pushed-forward
projective Haar law. -/
theorem integrable_complexProjectiveHaar_trace_smul_matrix
    (A : Matrix ι ι ℂ) :
    Integrable (fun B : Matrix ι ι ℂ ↦ (A * B).trace • B)
      (complexProjectiveHaarLaw ι) := by
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure
    (continuous_trace_smul_matrix ι A).aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  change Integrable
    (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
      (A * complexSphereProjector x).trace • complexSphereProjector x)
    (complexUnitSphereHaarLaw ι)
  exact integrable_complexSphere_trace_smul_projector ι A

/-- Every coordinate product is integrable under the concrete projective
probability law. -/
theorem integrable_complexProjectiveHaar_coordinateSecondMoment
    (i j k l : ι) :
    Integrable (fun B : Matrix ι ι ℂ ↦ B i j * B k l)
      (complexProjectiveHaarLaw ι) := by
  have hg : Continuous (fun B : Matrix ι ι ℂ ↦ B i j * B k l) := by
    fun_prop
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  change Integrable
    (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
      complexSphereProjector x i j * complexSphereProjector x k l)
    (complexUnitSphereHaarLaw ι)
  have hc := hg.comp (continuous_complexSphereProjector ι)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

/-- Continuous linear evaluation of one matrix coordinate. -/
noncomputable def complexMatrixEntryCLM (i j : ι) :
    Matrix ι ι ℂ →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j : (ι → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.proj i : Matrix ι ι ℂ →L[ℂ] (ι → ℂ))

@[simp] theorem complexMatrixEntryCLM_apply
    (i j : ι) (A : Matrix ι ι ℂ) :
    complexMatrixEntryCLM ι i j A = A i j :=
  rfl

/-- Coordinate evaluation commutes with a Bochner integral of matrices. -/
theorem integral_matrix_apply
    {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → Matrix ι ι ℂ) (μ : Measure Ω)
    (hf : Integrable f μ) (i j : ι) :
    (∫ x, f x ∂μ) i j = ∫ x, f x i j ∂μ := by
  have h := (complexMatrixEntryCLM ι i j).integral_comp_comm hf
  simpa only [complexMatrixEntryCLM_apply] using h.symm

/-- Pointwise coordinate expansion of the trace-weighted matrix observable. -/
theorem trace_smul_matrix_apply_eq_sum
    (A B : Matrix ι ι ℂ) (i j : ι) :
    ((A * B).trace • B) i j =
      ∑ a : ι, ∑ b : ι, A a b * (B b a * B i j) := by
  change (∑ a : ι, ∑ b : ι, A a b * B b a) * B i j = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Exact unconditional reduction of one entry of the matrix observable's
integral to the finite tensor contraction of coordinate moments. -/
theorem integral_trace_smul_matrix_apply_eq_sum_moments
    (A : Matrix ι ι ℂ) (i j : ι) :
    ∫ B, ((A * B).trace • B) i j ∂complexProjectiveHaarLaw ι =
      ∑ a : ι, ∑ b : ι,
        A a b * complexSphereProjectorSecondMoment ι b a i j := by
  calc
    _ = ∫ B, ∑ a : ι, ∑ b : ι,
          A a b * (B b a * B i j) ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [] with B
      exact trace_smul_matrix_apply_eq_sum ι A B i j
    _ = ∑ a : ι, ∑ b : ι,
          ∫ B, A a b * (B b a * B i j)
            ∂complexProjectiveHaarLaw ι := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro a ha
        rw [integral_finsetSum]
        intro b hb
        exact
          (integrable_complexProjectiveHaar_coordinateSecondMoment
            ι b a i j).const_mul (A a b)
      · intro a ha
        apply integrable_finsetSum Finset.univ
        intro b hb
        exact
          (integrable_complexProjectiveHaar_coordinateSecondMoment
            ι b a i j).const_mul (A a b)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [integral_const_mul,
        complexProjectiveHaar_coordinateSecondMoment_eq_sphere]

/-! ## Exact coordinate formula and finite-sum reduction

The phase-selection theorem above removes all non-balanced index patterns.
The remaining analytic content is the value of the balanced moments.  We
record that content as a proposition about the already constructed measure,
then prove that it is *exactly sufficient* for the desired matrix-channel
contraction.  No value of the proposition is introduced here.
-/

/-- The normalization appearing in the complex projective two-design
identity, namely `D (D + 1)` in complex scalars. -/
noncomputable def complexProjectiveTwoMomentDenominator : ℂ :=
  (Fintype.card ι : ℂ) * ((Fintype.card ι + 1 : ℕ) : ℂ)

theorem complexProjectiveTwoMomentDenominator_ne_zero :
    complexProjectiveTwoMomentDenominator ι ≠ 0 := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsucc : ((Fintype.card ι + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (Fintype.card ι)
  exact mul_ne_zero hcard hsucc

/-- Literal coordinate form of the normalized complex-projective second
moment.  This is the first analytic statement not yet derived from Mathlib's
Haar-to-sphere construction; it is a proposition, not an axiom or an
inhabited structure. -/
def ComplexProjectiveCoordinateTwoMomentFormula : Prop :=
  ∀ i j k l : ι,
    complexSphereProjectorSecondMoment ι i j k l =
      (((if i = j then 1 else 0) * (if k = l then 1 else 0) +
          (if i = l then 1 else 0) * (if k = j then 1 else 0)) *
        (complexProjectiveTwoMomentDenominator ι)⁻¹)

/-- The sphere-coordinate formula is equivalent to the same literal formula
under the pushed-forward projective probability law. -/
theorem complexProjectiveCoordinateTwoMomentFormula_iff_integral :
    ComplexProjectiveCoordinateTwoMomentFormula ι ↔
      ∀ i j k l : ι,
        ∫ B, B i j * B k l ∂complexProjectiveHaarLaw ι =
          (((if i = j then 1 else 0) * (if k = l then 1 else 0) +
              (if i = l then 1 else 0) * (if k = j then 1 else 0)) *
            (complexProjectiveTwoMomentDenominator ι)⁻¹) := by
  constructor
  · intro h i j k l
    rw [complexProjectiveHaar_coordinateSecondMoment_eq_sphere]
    exact h i j k l
  · intro h i j k l
    rw [← complexProjectiveHaar_coordinateSecondMoment_eq_sphere]
    exact h i j k l

/-- Pure finite-sum algebra: the coordinate two-design tensor contracts to
`(tr(A) δᵢⱼ + Aᵢⱼ) / (D(D+1))`.  This theorem has no measure-theoretic
premise beyond the literal coordinate formula. -/
theorem complexProjectiveCoordinateTwoMoment_finiteSum
    (hformula : ComplexProjectiveCoordinateTwoMomentFormula ι)
    (A : Matrix ι ι ℂ) (i j : ι) :
    (∑ a : ι, ∑ b : ι,
        A a b * complexSphereProjectorSecondMoment ι b a i j) =
      ((A.trace * (if i = j then 1 else 0) + A i j) *
        (complexProjectiveTwoMomentDenominator ι)⁻¹) := by
  let X : ι → ι → ℂ := fun a b ↦
    A a b * ((if b = a then 1 else 0) * (if i = j then 1 else 0))
  let Y : ι → ι → ℂ := fun a b ↦
    A a b * ((if b = j then 1 else 0) * (if i = a then 1 else 0))
  have hpull (f : ι → ι → ℂ) (c : ℂ) :
      (∑ a, ∑ b, f a b * c) = (∑ a, ∑ b, f a b) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.sum_mul]
  have hreplace :
      (∑ a : ι, ∑ b : ι,
          A a b * complexSphereProjectorSecondMoment ι b a i j) =
        ∑ a : ι, ∑ b : ι,
          A a b *
            ((((if b = a then 1 else 0) * (if i = j then 1 else 0)) +
                ((if b = j then 1 else 0) * (if i = a then 1 else 0))) *
              (complexProjectiveTwoMomentDenominator ι)⁻¹) := by
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    rw [hformula b a i j]
  rw [hreplace]
  have hpoint (a b : ι) :
      A a b *
          ((((if b = a then 1 else 0) * (if i = j then 1 else 0)) +
              ((if b = j then 1 else 0) * (if i = a then 1 else 0))) *
            (complexProjectiveTwoMomentDenominator ι)⁻¹) =
        X a b * (complexProjectiveTwoMomentDenominator ι)⁻¹ +
          Y a b * (complexProjectiveTwoMomentDenominator ι)⁻¹ := by
    simp only [X, Y]
    ring
  calc
    _ = ∑ a : ι, ∑ b : ι,
          (X a b * (complexProjectiveTwoMomentDenominator ι)⁻¹ +
            Y a b * (complexProjectiveTwoMomentDenominator ι)⁻¹) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      exact hpoint a b
    _ = (∑ a : ι, ∑ b : ι,
          X a b * (complexProjectiveTwoMomentDenominator ι)⁻¹) +
        (∑ a : ι, ∑ b : ι,
          Y a b * (complexProjectiveTwoMomentDenominator ι)⁻¹) := by
      simp only [Finset.sum_add_distrib]
    _ = ((∑ a, ∑ b, X a b) + (∑ a, ∑ b, Y a b)) *
        (complexProjectiveTwoMomentDenominator ι)⁻¹ := by
      rw [hpull X, hpull Y]
      ring
    _ = _ := by
      have hx :
          (∑ a, ∑ b, X a b) =
            A.trace * (if i = j then 1 else 0) := by
        simp [X, Matrix.trace]
      have hy : (∑ a, ∑ b, Y a b) = A i j := by
        simp [Y]
      rw [hx, hy]

/-- After the factor `D` for the exchangeable columns of a random basis, the
finite coordinate contraction is exactly the closed-form Haar channel. -/
theorem complexProjectiveCoordinateTwoMoment_contracts
    (hformula : ComplexProjectiveCoordinateTwoMomentFormula ι)
    (A : Matrix ι ι ℂ) (i j : ι) :
    (Fintype.card ι : ℂ) *
        (∑ a : ι, ∑ b : ι,
          A a b * complexSphereProjectorSecondMoment ι b a i j) =
      haarBasisForwardClosedForm A i j := by
  rw [complexProjectiveCoordinateTwoMoment_finiteSum ι hformula A i j]
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hij : i = j
  · subst j
    simp [complexProjectiveTwoMomentDenominator,
      haarBasisForwardClosedForm, haarDimensionPlusOne]
    field_simp
    ring
  · simp [complexProjectiveTwoMomentDenominator,
      haarBasisForwardClosedForm, haarDimensionPlusOne, hij]
    field_simp

/-- The exact coordinate tensor formula implies the original matrix-valued
`ProjectiveTwoMomentContraction` for the concrete projective Haar law.  Thus
the coordinate values, not Bochner-integral bookkeeping, are the sole
remaining analytic bridge. -/
theorem complexProjectiveCoordinateTwoMomentFormula_implies_twoMomentTheorem
    (hformula : ComplexProjectiveCoordinateTwoMomentFormula ι) :
    ComplexProjectiveTwoMomentTheorem (ι := ι) := by
  intro A
  ext i j
  change
    (Fintype.card ι : ℂ) *
        (∫ B, (A * B).trace • B ∂complexProjectiveHaarLaw ι) i j =
      haarBasisForwardClosedForm A i j
  rw [integral_matrix_apply ι _ _
    (integrable_complexProjectiveHaar_trace_smul_matrix ι A) i j]
  rw [integral_trace_smul_matrix_apply_eq_sum_moments ι A i j]
  exact complexProjectiveCoordinateTwoMoment_contracts ι hformula A i j

end CoordinateMoments

end TomographyOracleCore
