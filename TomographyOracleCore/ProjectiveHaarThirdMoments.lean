import TomographyOracleCore.ProjectiveHaarMomentValues

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator Pointwise

noncomputable section

/-!
# Third coordinate moments of the concrete complex-projective Haar law

This module develops the order-three analogue of the coordinate machinery in
`ProjectiveHaarMoments`.  Everything below is a theorem about the normalized
Haar-to-sphere measure already constructed in `ProjectiveHaar`; no moment
identity is assumed.
-/

section CoordinateThirdMoments

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Sixth-order coordinate moment of a complex unit vector, written as a
third moment of its rank-one projector. -/
noncomputable def complexSphereProjectorThirdMoment
    (i j k l p q : ι) : ℂ :=
  ∫ x, complexSphereProjector x i j * complexSphereProjector x k l *
      complexSphereProjector x p q
    ∂complexUnitSphereHaarLaw ι

/-- Every product of three projector coordinates is integrable on the compact
unit sphere. -/
theorem integrable_complexSphereProjectorThirdMoment
    (i j k l p q : ι) :
    Integrable
      (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
        complexSphereProjector x i j * complexSphereProjector x k l *
          complexSphereProjector x p q)
      (complexUnitSphereHaarLaw ι) := by
  have hc := ((continuous_complexSphereProjector_apply ι i j).mul
    (continuous_complexSphereProjector_apply ι k l)).mul
      (continuous_complexSphereProjector_apply ι p q)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

/-- Integration against the normalized complex-sphere Haar law, bundled as a
complex-linear functional on continuous functions.  Compactness of the sphere
makes every function in the domain integrable. -/
noncomputable def complexSphereHaarIntegralLinearMap :
    C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∫ x, f x ∂complexUnitSphereHaarLaw ι
  map_add' f g := by
    have hf : Integrable (fun x ↦ f x) (complexUnitSphereHaarLaw ι) := by
      apply f.continuous.integrable_of_hasCompactSupport
      exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
    have hg : Integrable (fun x ↦ g x) (complexUnitSphereHaarLaw ι) := by
      apply g.continuous.integrable_of_hasCompactSupport
      exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
    simpa only [ContinuousMap.add_apply] using integral_add hf hg
  map_smul' c f := by
    change (∫ x, c * f x ∂complexUnitSphereHaarLaw ι) =
      c * ∫ x, f x ∂complexUnitSphereHaarLaw ι
    exact integral_const_mul c (fun x ↦ f x)
      (μ := complexUnitSphereHaarLaw ι)

/-- A projector coordinate as a continuous function on the unit sphere. -/
noncomputable def complexSphereProjectorContinuousMap (i j : ι) :
    C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) :=
  ⟨fun x ↦ complexSphereProjector x i j,
    continuous_complexSphereProjector_apply ι i j⟩

@[simp] theorem complexSphereProjectorContinuousMap_apply
    (i j : ι) (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    complexSphereProjectorContinuousMap ι i j x =
      complexSphereProjector x i j :=
  rfl

@[simp] theorem complexSphereHaarIntegralLinearMap_projector_mul_three
    (i j k l p q : ι) :
    complexSphereHaarIntegralLinearMap ι
        (complexSphereProjectorContinuousMap ι i j *
          complexSphereProjectorContinuousMap ι k l *
            complexSphereProjectorContinuousMap ι p q) =
      complexSphereProjectorThirdMoment ι i j k l p q :=
  rfl

/-- Third coordinate moments are invariant under simultaneous permutation of
all six indices. -/
theorem complexSphereProjectorThirdMoment_permute
    (e : ι ≃ ι) (i j k l p q : ι) :
    complexSphereProjectorThirdMoment ι
        (e i) (e j) (e k) (e l) (e p) (e q) =
      complexSphereProjectorThirdMoment ι i j k l p q := by
  let f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    complexSphereProjector x (e i) (e j) *
      complexSphereProjector x (e k) (e l) *
        complexSphereProjector x (e p) (e q)
  have hf : Continuous f := by
    dsimp [f]
    exact ((continuous_complexSphereProjector_apply ι (e i) (e j)).mul
      (continuous_complexSphereProjector_apply ι (e k) (e l))).mul
        (continuous_complexSphereProjector_apply ι (e p) (e q))
  have hinv := integral_comp_complexUnitSphereHaarLaw_linearIsometry ι
    (complexCoordinatePermutationIsometry ι e) f hf
  have hfun :
      (fun x ↦ f (unitSphereLinearIsometryAction
        (complexCoordinatePermutationIsometry ι e) x)) =
      (fun x ↦ complexSphereProjector x i j *
        complexSphereProjector x k l * complexSphereProjector x p q) := by
    funext x
    simp [f, complexSphereProjector_apply,
      complexCoordinatePermutationIsometry]
  rw [hfun] at hinv
  exact hinv.symm

/-- The same coordinate moment under the pushed-forward projective law. -/
theorem complexProjectiveHaar_coordinateThirdMoment_eq_sphere
    (i j k l p q : ι) :
    ∫ B, B i j * B k l * B p q ∂complexProjectiveHaarLaw ι =
      complexSphereProjectorThirdMoment ι i j k l p q := by
  have hf : Measurable (fun B : Matrix ι ι ℂ ↦
      B i j * B k l * B p q) := by
    fun_prop
  unfold complexProjectiveHaarLaw complexSphereProjectorThirdMoment
  exact integral_map
    (measurable_complexSphereProjector (ι := ι)).aemeasurable
    hf.aestronglyMeasurable

/-- Phase acquired by a third projector-coordinate moment under independent
coordinate rotations. -/
noncomputable def projectorThirdMomentPhase
    (u : ι → Circle) (i j k l p q : ι) : ℂ :=
  (u i : ℂ) * star (u j : ℂ) *
    (u k : ℂ) * star (u l : ℂ) *
      (u p : ℂ) * star (u q : ℂ)

/-- Exact phase covariance of every third projector-coordinate moment. -/
theorem complexSphereProjectorThirdMoment_phase_covariant
    (u : ι → Circle) (i j k l p q : ι) :
    projectorThirdMomentPhase ι u i j k l p q *
        complexSphereProjectorThirdMoment ι i j k l p q =
      complexSphereProjectorThirdMoment ι i j k l p q := by
  let f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    complexSphereProjector x i j * complexSphereProjector x k l *
      complexSphereProjector x p q
  have hf : Continuous f := by
    dsimp [f]
    exact ((continuous_complexSphereProjector_apply ι i j).mul
      (continuous_complexSphereProjector_apply ι k l)).mul
        (continuous_complexSphereProjector_apply ι p q)
  have hinv := integral_comp_complexUnitSphereHaarLaw_linearIsometry ι
    (complexCoordinatePhaseIsometry ι u) f hf
  have hfun :
      (fun x ↦ f (unitSphereLinearIsometryAction
        (complexCoordinatePhaseIsometry ι u) x)) =
      (fun x ↦ projectorThirdMomentPhase ι u i j k l p q * f x) := by
    funext x
    simp only [f, complexSphereProjector_coordinatePhase_apply,
      projectorThirdMomentPhase]
    ring
  rw [hfun, integral_const_mul] at hinv
  simpa [complexSphereProjectorThirdMoment, f] using hinv

/-- A third coordinate moment with a nontrivial phase is zero. -/
theorem complexSphereProjectorThirdMoment_eq_zero_of_phase
    (u : ι → Circle) (i j k l p q : ι)
    (hphase : projectorThirdMomentPhase ι u i j k l p q ≠ 1) :
    complexSphereProjectorThirdMoment ι i j k l p q = 0 := by
  have hcov := complexSphereProjectorThirdMoment_phase_covariant
    ι u i j k l p q
  have hmul :
      (projectorThirdMomentPhase ι u i j k l p q - 1) *
          complexSphereProjectorThirdMoment ι i j k l p q = 0 := by
    calc
      _ = projectorThirdMomentPhase ι u i j k l p q *
            complexSphereProjectorThirdMoment ι i j k l p q -
          complexSphereProjectorThirdMoment ι i j k l p q := by ring
      _ = 0 := by rw [hcov]; ring
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hphase)

private theorem complex_I_ne_one_third : Complex.I ≠ (1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

private theorem complex_neg_I_ne_one_third : -Complex.I ≠ (1 : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- Cubing one genuinely off-diagonal projector coordinate has zero Haar
integral. -/
theorem complexSphereProjectorThirdMoment_offdiag_cube_eq_zero
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorThirdMoment ι i j i j i j = 0 := by
  apply complexSphereProjectorThirdMoment_eq_zero_of_phase ι
    (complexCoordinateIPhase ι i)
  simp [projectorThirdMomentPhase, complexCoordinateIPhase,
    Ne.symm hij]
  norm_num [Complex.I_mul_I]
  exact complex_neg_I_ne_one_third

/-- Two copies of an off-diagonal coordinate and one diagonal coordinate
still carry a nontrivial phase. -/
theorem complexSphereProjectorThirdMoment_offdiag_sq_diagonal_eq_zero
    (i j a : ι) (hij : i ≠ j) :
    complexSphereProjectorThirdMoment ι i j i j a a = 0 := by
  apply complexSphereProjectorThirdMoment_eq_zero_of_phase ι
    (complexCoordinateIPhase ι i)
  by_cases hai : a = i
  · subst a
    simp [projectorThirdMomentPhase, complexCoordinateIPhase,
      Ne.symm hij]
    norm_num [Complex.I_mul_I]
  · simp [projectorThirdMomentPhase, complexCoordinateIPhase,
      Ne.symm hij, hai]
    norm_num [Complex.I_mul_I]

/-- Two copies of an off-diagonal coordinate followed by its reverse still
have one unmatched phase. -/
theorem complexSphereProjectorThirdMoment_offdiag_sq_reverse_eq_zero
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorThirdMoment ι i j i j j i = 0 := by
  apply complexSphereProjectorThirdMoment_eq_zero_of_phase ι
    (complexCoordinateIPhase ι i)
  simp [projectorThirdMomentPhase, complexCoordinateIPhase,
    Ne.symm hij]
  norm_num [Complex.I_mul_I]
  exact complex_I_ne_one_third

/-- Diagonal factors do not compensate a single off-diagonal coordinate. -/
theorem complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
    (a b i j : ι) (hij : i ≠ j) :
    complexSphereProjectorThirdMoment ι a a b b i j = 0 := by
  apply complexSphereProjectorThirdMoment_eq_zero_of_phase ι
    (complexCoordinateIPhase ι i)
  by_cases hai : a = i
  · subst a
    by_cases hbi : b = i
    · subst b
      simp [projectorThirdMomentPhase, complexCoordinateIPhase,
        Ne.symm hij, complex_I_ne_one_third]
    · simp [projectorThirdMomentPhase, complexCoordinateIPhase,
        Ne.symm hij, hbi, complex_I_ne_one_third]
  · by_cases hbi : b = i
    · subst b
      simp [projectorThirdMomentPhase, complexCoordinateIPhase,
        Ne.symm hij, hai, complex_I_ne_one_third]
    · simp [projectorThirdMomentPhase, complexCoordinateIPhase,
        Ne.symm hij, hai, hbi, complex_I_ne_one_third]

/-- All one-coordinate sixth moments agree. -/
theorem complexSphereProjectorThirdMoment_diagonal_eq
    (i j : ι) :
    complexSphereProjectorThirdMoment ι i i i i i i =
      complexSphereProjectorThirdMoment ι j j j j j j := by
  have h := complexSphereProjectorThirdMoment_permute ι
    (Equiv.swap i j) i i i i i i
  simpa using h.symm

/-- The two-one diagonal moment is unchanged when the two coordinates are
interchanged. -/
theorem complexSphereProjectorThirdMoment_two_one_swap
    (i j : ι) :
    complexSphereProjectorThirdMoment ι i i i i j j =
      complexSphereProjectorThirdMoment ι j j j j i i := by
  have h := complexSphereProjectorThirdMoment_permute ι
    (Equiv.swap i j) i i i i j j
  simpa using h.symm

/-- The first two projector-coordinate factors may be interchanged. -/
theorem complexSphereProjectorThirdMoment_swap_first_two
    (i j k l p q : ι) :
    complexSphereProjectorThirdMoment ι i j k l p q =
      complexSphereProjectorThirdMoment ι k l i j p q := by
  unfold complexSphereProjectorThirdMoment
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- The last two projector-coordinate factors may be interchanged. -/
theorem complexSphereProjectorThirdMoment_swap_last_two
    (i j k l p q : ι) :
    complexSphereProjectorThirdMoment ι i j k l p q =
      complexSphereProjectorThirdMoment ι i j p q k l := by
  unfold complexSphereProjectorThirdMoment
  apply integral_congr_ae
  filter_upwards [] with x
  ring

/-- A balanced off-diagonal pair cancels pointwise, leaving the corresponding
two-one diagonal moment. -/
theorem complexSphereProjectorThirdMoment_diagonal_offdiag_pair
    (i j : ι) :
    complexSphereProjectorThirdMoment ι i i i j j i =
      complexSphereProjectorThirdMoment ι i i i i j j := by
  unfold complexSphereProjectorThirdMoment
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [complexSphereProjector_apply]
  ring

/-- The analogous cancellation with the other diagonal coordinate. -/
theorem complexSphereProjectorThirdMoment_other_diagonal_offdiag_pair
    (i j : ι) :
    complexSphereProjectorThirdMoment ι j j i j j i =
      complexSphereProjectorThirdMoment ι j j j j i i := by
  unfold complexSphereProjectorThirdMoment
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [complexSphereProjector_apply]
  ring

/-- Pointwise rank-one cancellation turns a balanced two-cycle into diagonal
coordinates inside a third moment. -/
theorem complexSphereProjectorThirdMoment_swap_pair_diagonal
    (i j k : ι) :
    complexSphereProjectorThirdMoment ι i j j i k k =
      complexSphereProjectorThirdMoment ι i i j j k k := by
  unfold complexSphereProjectorThirdMoment
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [complexSphereProjector_apply]
  ring

/-- Summing the last diagonal coordinate uses `trace P = 1` and recovers the
already proved second coordinate moment. -/
theorem complexSphereProjectorThirdMoment_sum_last_diagonal
    (i j k l : ι) :
    (∑ p : ι, complexSphereProjectorThirdMoment ι i j k l p p) =
      complexSphereProjectorSecondMoment ι i j k l := by
  have hint (p : ι) :=
    integrable_complexSphereProjectorThirdMoment ι i j k l p p
  calc
    (∑ p : ι, complexSphereProjectorThirdMoment ι i j k l p p) =
        ∫ x, ∑ p : ι,
          complexSphereProjector x i j * complexSphereProjector x k l *
            complexSphereProjector x p p
          ∂complexUnitSphereHaarLaw ι := by
      symm
      exact integral_finsetSum Finset.univ (fun p _ ↦ hint p)
    _ = ∫ x,
          complexSphereProjector x i j * complexSphereProjector x k l
          ∂complexUnitSphereHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.mul_sum]
      change
        (complexSphereProjector x i j * complexSphereProjector x k l) *
            (complexSphereProjector x).trace = _
      rw [complexSphereProjector_trace_eq_one]
      ring
    _ = complexSphereProjectorSecondMoment ι i j k l := rfl

set_option maxHeartbeats 1200000 in
/-- For two distinct coordinates, the one-coordinate sixth moment is three
times the moment with multiplicities two and one.  This is forced by the same
explicit rational two-coordinate reflection used for the proved second
moment formula. -/
theorem complexSphereProjectorThirdMoment_diagonal_eq_three_pair
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorThirdMoment ι i i i i i i =
      3 * complexSphereProjectorThirdMoment ι i i i i j j := by
  let X : C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) :=
    complexSphereProjectorContinuousMap ι i i
  let Y : C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) :=
    complexSphereProjectorContinuousMap ι j j
  let C : C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) :=
    complexSphereProjectorContinuousMap ι i j
  let D : C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) :=
    complexSphereProjectorContinuousMap ι j i
  let Z : C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) := C + D
  let Q : C(sphere (0 : EuclideanSpace ℂ ι) 1, ℂ) :=
    (9 / 25 : ℂ) • X + (16 / 25 : ℂ) • Y + (12 / 25 : ℂ) • Z
  let L := complexSphereHaarIntegralLinearMap ι

  have hZ3 : L (Z * Z * Z) = 0 := by
    have hexpand :
        Z * Z * Z =
          C * C * C + (3 : ℂ) • (C * C * D) +
            (3 : ℂ) • (D * D * C) + D * D * D := by
      ext x
      dsimp [Z]
      ring
    rw [hexpand]
    simp only [map_add, map_smul, smul_eq_mul, L, C, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    rw [complexSphereProjectorThirdMoment_offdiag_cube_eq_zero ι i j hij,
      complexSphereProjectorThirdMoment_offdiag_sq_reverse_eq_zero ι i j hij,
      complexSphereProjectorThirdMoment_offdiag_sq_reverse_eq_zero ι j i
        (Ne.symm hij),
      complexSphereProjectorThirdMoment_offdiag_cube_eq_zero ι j i
        (Ne.symm hij)]
    ring

  have hX2Z : L (X * X * Z) = 0 := by
    have hexpand : X * X * Z = X * X * C + X * X * D := by
      ext x
      dsimp [Z]
      ring
    rw [hexpand]
    simp only [map_add, L, X, C, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    rw [complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
        ι i i i j hij,
      complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
        ι i i j i (Ne.symm hij)]
    ring

  have hY2Z : L (Y * Y * Z) = 0 := by
    have hexpand : Y * Y * Z = Y * Y * C + Y * Y * D := by
      ext x
      dsimp [Z]
      ring
    rw [hexpand]
    simp only [map_add, L, Y, C, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    rw [complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
        ι j j i j hij,
      complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
        ι j j j i (Ne.symm hij)]
    ring

  have hXYZ : L (X * Y * Z) = 0 := by
    have hexpand : X * Y * Z = X * Y * C + X * Y * D := by
      ext x
      dsimp [Z]
      ring
    rw [hexpand]
    simp only [map_add, L, X, Y, C, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    rw [complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
        ι i j i j hij,
      complexSphereProjectorThirdMoment_diagonals_offdiag_eq_zero
        ι i j j i (Ne.symm hij)]
    ring

  have hXCC :
      L (X * C * C) = 0 := by
    simp only [L, X, C,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    simpa [complexSphereProjectorThirdMoment, mul_comm, mul_left_comm,
      mul_assoc] using
      complexSphereProjectorThirdMoment_offdiag_sq_diagonal_eq_zero
        ι i j i hij
  have hXDD :
      L (X * D * D) = 0 := by
    simp only [L, X, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    simpa [complexSphereProjectorThirdMoment, mul_comm, mul_left_comm,
      mul_assoc] using
      complexSphereProjectorThirdMoment_offdiag_sq_diagonal_eq_zero
        ι j i i (Ne.symm hij)
  have hYCC :
      L (Y * C * C) = 0 := by
    simp only [L, Y, C,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    simpa [complexSphereProjectorThirdMoment, mul_comm, mul_left_comm,
      mul_assoc] using
      complexSphereProjectorThirdMoment_offdiag_sq_diagonal_eq_zero
        ι i j j hij
  have hYDD :
      L (Y * D * D) = 0 := by
    simp only [L, Y, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    simpa [complexSphereProjectorThirdMoment, mul_comm, mul_left_comm,
      mul_assoc] using
      complexSphereProjectorThirdMoment_offdiag_sq_diagonal_eq_zero
        ι j i j (Ne.symm hij)

  have hXZ2 :
      L (X * Z * Z) =
        2 * complexSphereProjectorThirdMoment ι i i i i j j := by
    have hexpand :
        X * Z * Z = X * C * C + (2 : ℂ) • (X * C * D) + X * D * D := by
      ext x
      dsimp [Z]
      ring
    rw [hexpand]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [hXCC, hXDD]
    simp only [L, X, C, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    rw [complexSphereProjectorThirdMoment_diagonal_offdiag_pair]
    ring

  have hYZ2 :
      L (Y * Z * Z) =
        2 * complexSphereProjectorThirdMoment ι i i i i j j := by
    have hexpand :
        Y * Z * Z = Y * C * C + (2 : ℂ) • (Y * C * D) + Y * D * D := by
      ext x
      dsimp [Z]
      ring
    rw [hexpand]
    simp only [map_add, map_smul, smul_eq_mul]
    rw [hYCC, hYDD]
    simp only [L, Y, C, D,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    rw [complexSphereProjectorThirdMoment_other_diagonal_offdiag_pair,
      ← complexSphereProjectorThirdMoment_two_one_swap ι i j]
    ring

  have hX3 :
      L (X * X * X) =
        complexSphereProjectorThirdMoment ι i i i i i i := by
    simp only [L, X,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
  have hY3 :
      L (Y * Y * Y) =
        complexSphereProjectorThirdMoment ι i i i i i i := by
    simp only [L, Y,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    exact complexSphereProjectorThirdMoment_diagonal_eq ι j i
  have hX2Y :
      L (X * X * Y) =
        complexSphereProjectorThirdMoment ι i i i i j j := by
    simp only [L, X, Y,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
  have hY2X :
      L (Y * Y * X) =
        complexSphereProjectorThirdMoment ι i i i i j j := by
    simp only [L, X, Y,
      complexSphereHaarIntegralLinearMap_projector_mul_three]
    exact (complexSphereProjectorThirdMoment_two_one_swap ι i j).symm

  let f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    complexSphereProjector x i i * complexSphereProjector x i i *
      complexSphereProjector x i i
  have hf : Continuous f := by
    dsimp [f]
    exact ((continuous_complexSphereProjector_apply ι i i).mul
      (continuous_complexSphereProjector_apply ι i i)).mul
        (continuous_complexSphereProjector_apply ι i i)
  have hinv := integral_comp_complexUnitSphereHaarLaw_linearIsometry ι
    (complexLinearIsometryEquivToReal
      (complexTwoCoordinateMixIsometry ι i j)) f hf
  have hcomp :
      (fun x ↦ f (unitSphereLinearIsometryAction
        (complexLinearIsometryEquivToReal
          (complexTwoCoordinateMixIsometry ι i j)) x)) =
      (fun x ↦ Q x * Q x * Q x) := by
    funext x
    dsimp [f, Q, X, Y, Z, C, D]
    rw [complexSphereProjector_mix_left_diagonal ι i j hij]
  rw [hcomp] at hinv
  have hinvL : L (Q * Q * Q) = L (X * X * X) := by
    change (∫ x, Q x * Q x * Q x ∂complexUnitSphereHaarLaw ι) =
      ∫ x, X x * X x * X x ∂complexUnitSphereHaarLaw ι
    simpa [f, X] using hinv

  have hQexpand :
      Q * Q * Q =
        (729 / 15625 : ℂ) • (X * X * X) +
        (4096 / 15625 : ℂ) • (Y * Y * Y) +
        (1728 / 15625 : ℂ) • (Z * Z * Z) +
        (3888 / 15625 : ℂ) • (X * X * Y) +
        (2916 / 15625 : ℂ) • (X * X * Z) +
        (6912 / 15625 : ℂ) • (Y * Y * X) +
        (9216 / 15625 : ℂ) • (Y * Y * Z) +
        (3888 / 15625 : ℂ) • (X * Z * Z) +
        (6912 / 15625 : ℂ) • (Y * Z * Z) +
        (10368 / 15625 : ℂ) • (X * Y * Z) := by
    ext x
    dsimp [Q]
    ring
  rw [hQexpand] at hinvL
  simp only [map_add, map_smul, smul_eq_mul] at hinvL
  rw [hX3, hY3, hZ3, hX2Y, hX2Z, hY2X, hY2Z, hXZ2, hYZ2,
    hXYZ] at hinvL
  ring_nf at hinvL
  linear_combination (-625 / 432 : ℂ) * hinvL

/-- Normalization for the order-three complex-projective tensor. -/
noncomputable def complexProjectiveThirdMomentDenominator : ℂ :=
  (Fintype.card ι : ℂ) * ((Fintype.card ι + 1 : ℕ) : ℂ) *
    ((Fintype.card ι + 2 : ℕ) : ℂ)

theorem complexProjectiveThirdMomentDenominator_ne_zero :
    complexProjectiveThirdMomentDenominator ι ≠ 0 := by
  unfold complexProjectiveThirdMomentDenominator
  have h0 : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have h1 : ((Fintype.card ι + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (Fintype.card ι)
  have h2 : ((Fintype.card ι + 2 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (show Fintype.card ι + 2 ≠ 0 by omega)
  exact mul_ne_zero (mul_ne_zero h0 h1) h2

/-- Exact balanced third moment with coordinate multiplicities two and one. -/
theorem complexSphereProjectorThirdMoment_two_one_value
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorThirdMoment ι i i i i j j =
      2 * (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
  let b : ℂ := complexSphereProjectorThirdMoment ι i i i i j j
  have hterm (p : ι) :
      complexSphereProjectorThirdMoment ι i i i i p p =
        b + if p = i then 2 * b else 0 := by
    by_cases hpi : p = i
    · subst p
      simp only [if_pos rfl]
      dsimp [b]
      have hr := complexSphereProjectorThirdMoment_diagonal_eq_three_pair
        ι i j hij
      linear_combination hr
    · simp only [if_neg hpi, add_zero]
      dsimp [b]
      have hp := complexSphereProjectorThirdMoment_diagonal_eq_three_pair
        ι i p (Ne.symm hpi)
      have hj := complexSphereProjectorThirdMoment_diagonal_eq_three_pair
        ι i j hij
      linear_combination (-1 / 3 : ℂ) * hp + (1 / 3 : ℂ) * hj
  have hnorm := complexSphereProjectorThirdMoment_sum_last_diagonal
    ι i i i i
  rw [complexSphereProjectorSecondMoment_diagonal_value i] at hnorm
  simp_rw [hterm] at hnorm
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ] at hnorm
  have hdiag :
      (∑ p : ι, if p = i then 2 * b else 0) = 2 * b := by
    simp
  rw [hdiag] at hnorm
  simp only [nsmul_eq_mul] at hnorm
  have hden := complexProjectiveThirdMomentDenominator_ne_zero (ι := ι)
  have hden2 := complexProjectiveTwoMomentDenominator_ne_zero (ι := ι)
  rw [complexProjectiveTwoMomentDenominator] at hnorm hden2
  rw [complexProjectiveThirdMomentDenominator]
  rw [complexProjectiveThirdMomentDenominator] at hden
  field_simp [hden]
  field_simp [hden2] at hnorm
  push_cast at hnorm ⊢
  dsimp [b] at hnorm
  linear_combination hnorm

/-- Exact one-coordinate sixth moment. -/
theorem complexSphereProjectorThirdMoment_diagonal_value
    (i : ι) :
    complexSphereProjectorThirdMoment ι i i i i i i =
      6 * (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
  classical
  by_cases hnt : Nontrivial ι
  · letI : Nontrivial ι := hnt
    obtain ⟨j, hji⟩ := exists_ne i
    have hij : i ≠ j := Ne.symm hji
    rw [complexSphereProjectorThirdMoment_diagonal_eq_three_pair ι i j hij,
      complexSphereProjectorThirdMoment_two_one_value ι i j hij]
    ring
  · letI : Subsingleton ι := by
      constructor
      intro a b
      by_contra hab
      exact hnt ⟨a, b, hab⟩
    have hcard : Fintype.card ι = 1 := Fintype.card_eq_one_iff.mpr
      ⟨i, fun a ↦ Subsingleton.elim a i⟩
    have hnorm := complexSphereProjectorThirdMoment_sum_last_diagonal
      ι i i i i
    rw [complexSphereProjectorSecondMoment_diagonal_value i] at hnorm
    have hconst :
        (∑ p : ι, complexSphereProjectorThirdMoment ι i i i i p p) =
          Fintype.card ι •
            complexSphereProjectorThirdMoment ι i i i i i i := by
      calc
        _ = ∑ _p : ι,
            complexSphereProjectorThirdMoment ι i i i i i i := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [Subsingleton.elim p i]
        _ = _ := by simp
    rw [hconst] at hnorm
    simp only [nsmul_eq_mul, hcard, Nat.cast_one, one_mul] at hnorm
    norm_num [complexProjectiveTwoMomentDenominator, hcard] at hnorm
    norm_num [complexProjectiveThirdMomentDenominator, hcard]
    exact hnorm

/-- Exact third moment of three pairwise-distinct diagonal coordinates. -/
theorem complexSphereProjectorThirdMoment_three_distinct_value
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    complexSphereProjectorThirdMoment ι i i j j k k =
      (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
  let b : ℂ := complexSphereProjectorThirdMoment ι i i i i j j
  let c : ℂ := complexSphereProjectorThirdMoment ι i i j j k k
  have hterm (p : ι) :
      complexSphereProjectorThirdMoment ι i i j j p p =
        c + (if p = i then b - c else 0) +
          (if p = j then b - c else 0) := by
    by_cases hpi : p = i
    · subst p
      simp [hij]
      dsimp [b, c]
      rw [complexSphereProjectorThirdMoment_swap_last_two]
    · by_cases hpj : p = j
      · subst p
        simp [Ne.symm hij]
        dsimp [b, c]
        simpa [complexSphereProjectorThirdMoment, mul_comm, mul_left_comm,
          mul_assoc] using
          (complexSphereProjectorThirdMoment_two_one_swap ι i j).symm
      · simp only [if_neg hpi, if_neg hpj, add_zero]
        dsimp [c]
        by_cases hpk : p = k
        · subst p
          rfl
        · have hperm := complexSphereProjectorThirdMoment_permute ι
            (Equiv.swap p k) i i j j p p
          have hfixi : Equiv.swap p k i = i :=
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hpi) hik
          have hfixj : Equiv.swap p k j = j :=
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hpj) hjk
          rw [hfixi, hfixj, Equiv.swap_apply_left] at hperm
          exact hperm.symm
  have hnorm := complexSphereProjectorThirdMoment_sum_last_diagonal
    ι i i j j
  rw [complexSphereProjectorSecondMoment_distinct_diagonal_pair_value
    i j hij] at hnorm
  simp_rw [hterm] at hnorm
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ] at hnorm
  have hdiagi :
      (∑ p : ι, if p = i then b - c else 0) = b - c := by
    simp
  have hdiagj :
      (∑ p : ι, if p = j then b - c else 0) = b - c := by
    simp
  rw [hdiagi, hdiagj] at hnorm
  simp only [nsmul_eq_mul] at hnorm
  have hb : b = 2 * (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
    dsimp [b]
    exact complexSphereProjectorThirdMoment_two_one_value ι i j hij
  rw [hb] at hnorm

  have hcard : 3 ≤ Fintype.card ι := by
    have hsubset : ({i, j, k} : Finset ι) ⊆ Finset.univ :=
      Finset.subset_univ _
    have hle := Finset.card_le_card hsubset
    have hthree : ({i, j, k} : Finset ι).card = 3 := by
      simp [hij, hik, hjk, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
    rw [hthree] at hle
    simpa using hle
  have hncard : Fintype.card ι ≠ 2 := by omega
  have hn2 : (Fintype.card ι : ℂ) - 2 ≠ 0 :=
    sub_ne_zero.mpr (by exact_mod_cast hncard)
  have hrel :
      ((Fintype.card ι : ℂ) - 2) *
          (c - (complexProjectiveThirdMomentDenominator ι)⁻¹) = 0 := by
    have hden := complexProjectiveThirdMomentDenominator_ne_zero (ι := ι)
    have hden2 := complexProjectiveTwoMomentDenominator_ne_zero (ι := ι)
    rw [complexProjectiveThirdMomentDenominator] at hden
    rw [complexProjectiveTwoMomentDenominator] at hden2
    rw [complexProjectiveThirdMomentDenominator]
    rw [complexProjectiveThirdMomentDenominator,
      complexProjectiveTwoMomentDenominator] at hnorm
    field_simp [hden]
    field_simp [hden, hden2] at hnorm
    push_cast at hnorm ⊢
    linear_combination hnorm
  have hc : c = (complexProjectiveThirdMomentDenominator ι)⁻¹ :=
    sub_eq_zero.mp ((mul_eq_zero.mp hrel).resolve_left hn2)
  exact hc

/-- Equality of two unordered pairs, in an explicit form convenient for the
order-three coordinate calculation. -/
theorem multiset_pair_eq_iff_two_matchings
    (a b c d : ι) :
    a ::ₘ b ::ₘ 0 = c ::ₘ d ::ₘ 0 ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      have hm : a ∈ c ::ₘ d ::ₘ 0 := by
        rw [← h]
        simp
      simpa using hm
    rcases ha with hac | had
    · subst c
      left
      refine ⟨rfl, ?_⟩
      have ht : b ::ₘ 0 = d ::ₘ 0 :=
        (Multiset.cons_inj_right a).mp h
      exact (Multiset.cons_inj_left (0 : Multiset ι)).mp ht
    · subst d
      right
      refine ⟨rfl, ?_⟩
      have h' : a ::ₘ b ::ₘ 0 = a ::ₘ c ::ₘ 0 := by
        calc
          _ = c ::ₘ a ::ₘ 0 := h
          _ = a ::ₘ c ::ₘ 0 := Multiset.cons_swap c a 0
      have ht : b ::ₘ 0 = c ::ₘ 0 :=
        (Multiset.cons_inj_right a).mp h'
      exact (Multiset.cons_inj_left (0 : Multiset ι)).mp ht
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Multiset.cons_swap _ _ _

/-- Equality of two unordered triples is exactly the disjunction of the six
possible matchings. -/
theorem multiset_triple_eq_iff_six_matchings
    (i k p j l q : ι) :
    i ::ₘ k ::ₘ p ::ₘ 0 = j ::ₘ l ::ₘ q ::ₘ 0 ↔
      (i = j ∧ k = l ∧ p = q) ∨
      (i = j ∧ k = q ∧ p = l) ∨
      (i = l ∧ k = j ∧ p = q) ∨
      (i = l ∧ k = q ∧ p = j) ∨
      (i = q ∧ k = j ∧ p = l) ∨
      (i = q ∧ k = l ∧ p = j) := by
  constructor
  · intro h
    have hi : i = j ∨ i = l ∨ i = q := by
      have hm : i ∈ j ::ₘ l ::ₘ q ::ₘ 0 := by
        rw [← h]
        simp
      simpa [or_assoc] using hm
    rcases hi with hij | hil | hiq
    · subst j
      have ht : k ::ₘ p ::ₘ 0 = l ::ₘ q ::ₘ 0 :=
        (Multiset.cons_inj_right i).mp h
      rcases (multiset_pair_eq_iff_two_matchings ι k p l q).mp ht with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl, rfl⟩
      · exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)
    · subst l
      have h' : i ::ₘ k ::ₘ p ::ₘ 0 = i ::ₘ j ::ₘ q ::ₘ 0 := by
        calc
          _ = j ::ₘ i ::ₘ q ::ₘ 0 := h
          _ = i ::ₘ j ::ₘ q ::ₘ 0 := Multiset.cons_swap j i _
      have ht : k ::ₘ p ::ₘ 0 = j ::ₘ q ::ₘ 0 :=
        (Multiset.cons_inj_right i).mp h'
      rcases (multiset_pair_eq_iff_two_matchings ι k p j q).mp ht with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
    · subst q
      have h' : i ::ₘ k ::ₘ p ::ₘ 0 = i ::ₘ j ::ₘ l ::ₘ 0 := by
        calc
          _ = j ::ₘ l ::ₘ i ::ₘ 0 := h
          _ = j ::ₘ i ::ₘ l ::ₘ 0 := by
            rw [Multiset.cons_swap l i]
          _ = i ::ₘ j ::ₘ l ::ₘ 0 := Multiset.cons_swap j i _
      have ht : k ::ₘ p ::ₘ 0 = j ::ₘ l ::ₘ 0 :=
        (Multiset.cons_inj_right i).mp h'
      rcases (multiset_pair_eq_iff_two_matchings ι k p j l).mp ht with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))))
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    all_goals
      apply Multiset.ext.mpr
      intro a
      simp only [Multiset.count_cons, Multiset.count_zero] <;> omega

/-- If the left and right coordinate multisets differ, independent phase
invariance forces the third projector-coordinate moment to vanish. -/
theorem complexSphereProjectorThirdMoment_eq_zero_of_not_multiset_balanced
    (i j k l p q : ι)
    (hbad : i ::ₘ k ::ₘ p ::ₘ 0 ≠ j ::ₘ l ::ₘ q ::ₘ 0) :
    complexSphereProjectorThirdMoment ι i j k l p q = 0 := by
  have hdiff : ∃ r : ι,
      Multiset.count r (i ::ₘ k ::ₘ p ::ₘ 0) ≠
        Multiset.count r (j ::ₘ l ::ₘ q ::ₘ 0) := by
    by_contra h
    push_neg at h
    exact hbad (Multiset.ext.mpr h)
  obtain ⟨r, hr⟩ := hdiff
  apply complexSphereProjectorThirdMoment_eq_zero_of_phase ι
    (complexCoordinateIPhase ι r)
  by_cases hir : i = r <;>
  by_cases hjr : j = r <;>
  by_cases hkr : k = r <;>
  by_cases hlr : l = r <;>
  by_cases hpr : p = r <;>
  by_cases hqr : q = r
  all_goals simp [Multiset.count_cons, Multiset.count_zero, eq_comm,
    hir, hjr, hkr, hlr, hpr, hqr] at hr
  all_goals simp [projectorThirdMomentPhase, complexCoordinateIPhase, eq_comm,
    hir, hjr, hkr, hlr, hpr, hqr,
    complex_I_ne_one_third, complex_neg_I_ne_one_third] <;>
      norm_num [Complex.I_mul_I]

/-- Once the left and right index multisets agree, rank-one cancellation
reduces the coordinate product to three diagonal projector entries. -/
theorem complexSphereProjectorThirdMoment_eq_diagonal_of_multiset_balanced
    (i j k l p q : ι)
    (hbal : i ::ₘ k ::ₘ p ::ₘ 0 = j ::ₘ l ::ₘ q ::ₘ 0) :
    complexSphereProjectorThirdMoment ι i j k l p q =
      complexSphereProjectorThirdMoment ι i i k k p p := by
  rcases (multiset_triple_eq_iff_six_matchings ι i k p j l q).mp hbal with
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals
    unfold complexSphereProjectorThirdMoment
    apply integral_congr_ae
    filter_upwards [] with x
    simp only [complexSphereProjector_apply] <;> ring

/-- The six Kronecker matchings in the order-three complex-projective
symmetrizer. -/
noncomputable def complexProjectiveThirdMomentKernel
    (i j k l p q : ι) : ℂ :=
  (if i = j ∧ k = l ∧ p = q then 1 else 0) +
  (if i = j ∧ k = q ∧ p = l then 1 else 0) +
  (if i = l ∧ k = j ∧ p = q then 1 else 0) +
  (if i = l ∧ k = q ∧ p = j then 1 else 0) +
  (if i = q ∧ k = j ∧ p = l then 1 else 0) +
  (if i = q ∧ k = l ∧ p = j then 1 else 0)

/-- Concrete order-three coordinate identity for the pushed-forward
complex-projective Haar law. -/
theorem complexProjectiveHaar_coordinateThirdMoment_formula
    (i j k l p q : ι) :
    (∫ B, B i j * B k l * B p q ∂complexProjectiveHaarLaw ι) =
      complexProjectiveThirdMomentKernel ι i j k l p q *
        (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
  rw [complexProjectiveHaar_coordinateThirdMoment_eq_sphere]
  by_cases hbal : i ::ₘ k ::ₘ p ::ₘ 0 = j ::ₘ l ::ₘ q ::ₘ 0
  · rw [complexSphereProjectorThirdMoment_eq_diagonal_of_multiset_balanced
      ι i j k l p q hbal]
    rcases (multiset_triple_eq_iff_six_matchings ι i k p j l q).mp hbal with
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals
      dsimp [complexProjectiveThirdMomentKernel]
      by_cases hik : i = k
      · subst k
        by_cases hip : i = p
        · subst p
          rw [complexSphereProjectorThirdMoment_diagonal_value]
          norm_num
        · rw [complexSphereProjectorThirdMoment_two_one_value ι i p hip]
          simp [hip, Ne.symm hip]
          ring_nf <;> simp
      · by_cases hip : i = p
        · subst p
          have hv :
              complexSphereProjectorThirdMoment ι i i k k i i =
                2 * (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
            rw [complexSphereProjectorThirdMoment_swap_last_two]
            exact complexSphereProjectorThirdMoment_two_one_value ι i k hik
          rw [hv]
          simp [hik, Ne.symm hik]
          ring_nf <;> simp
        · by_cases hkp : k = p
          · subst p
            have hv :
                complexSphereProjectorThirdMoment ι i i k k k k =
                  2 * (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
              simpa [complexSphereProjectorThirdMoment, mul_comm,
                mul_left_comm, mul_assoc] using
                complexSphereProjectorThirdMoment_two_one_value
                  ι k i (Ne.symm hik)
            rw [hv]
            simp [hik, Ne.symm hik]
            ring_nf <;> simp
          · rw [complexSphereProjectorThirdMoment_three_distinct_value
              ι i k p hik hip hkp]
            simp [hik, hip, hkp, Ne.symm hik, Ne.symm hip, Ne.symm hkp]
  · rw [complexSphereProjectorThirdMoment_eq_zero_of_not_multiset_balanced
      ι i j k l p q hbal]
    have hsix := multiset_triple_eq_iff_six_matchings ι i k p j l q
    have h1 : ¬(i = j ∧ k = l ∧ p = q) := by
      intro h
      exact hbal (hsix.mpr (Or.inl h))
    have h2 : ¬(i = j ∧ k = q ∧ p = l) := by
      intro h
      exact hbal (hsix.mpr (Or.inr (Or.inl h)))
    have h3 : ¬(i = l ∧ k = j ∧ p = q) := by
      intro h
      exact hbal (hsix.mpr (Or.inr (Or.inr (Or.inl h))))
    have h4 : ¬(i = l ∧ k = q ∧ p = j) := by
      intro h
      exact hbal (hsix.mpr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    have h5 : ¬(i = q ∧ k = j ∧ p = l) := by
      intro h
      exact hbal (hsix.mpr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    have h6 : ¬(i = q ∧ k = l ∧ p = j) := by
      intro h
      exact hbal (hsix.mpr
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))
    simp [complexProjectiveThirdMomentKernel, h1, h2, h3, h4, h5, h6]

/-- Exact order-three coordinate formula.  This proposition is a local proof
target, not an axiom or an assumed theorem. -/
def ComplexProjectiveCoordinateThirdMomentFormula : Prop :=
  ∀ i j : Fin 3 → ι,
    (∫ B, ∏ a : Fin 3, B (i a) (j a) ∂complexProjectiveHaarLaw ι) =
      (∑ π : Equiv.Perm (Fin 3),
          ∏ a : Fin 3, if i a = j (π a) then (1 : ℂ) else 0) *
        (complexProjectiveThirdMomentDenominator ι)⁻¹

/-- The cycle `0 ↦ 2 ↦ 1 ↦ 0` on three coordinates. -/
def finThreeCycleBackward : Equiv.Perm (Fin 3) :=
  (Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2)

/-- The cycle `0 ↦ 1 ↦ 2 ↦ 0` on three coordinates. -/
def finThreeCycleForward : Equiv.Perm (Fin 3) :=
  (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1)

@[simp] theorem finThreeCycleBackward_apply_zero :
    finThreeCycleBackward 0 = 2 := by decide

@[simp] theorem finThreeCycleBackward_apply_one :
    finThreeCycleBackward 1 = 0 := by decide

@[simp] theorem finThreeCycleBackward_apply_two :
    finThreeCycleBackward 2 = 1 := by decide

@[simp] theorem finThreeCycleForward_apply_zero :
    finThreeCycleForward 0 = 1 := by decide

@[simp] theorem finThreeCycleForward_apply_one :
    finThreeCycleForward 1 = 2 := by decide

@[simp] theorem finThreeCycleForward_apply_two :
    finThreeCycleForward 2 = 0 := by decide

@[simp] theorem finThreePermOne_apply (a : Fin 3) :
    (1 : Equiv.Perm (Fin 3)) a = a :=
  rfl

@[simp] theorem finThreeSwapOneTwo_apply_zero :
    Equiv.swap (1 : Fin 3) 2 0 = 0 := by decide

@[simp] theorem finThreeSwapOneTwo_apply_one :
    Equiv.swap (1 : Fin 3) 2 1 = 2 := by decide

@[simp] theorem finThreeSwapOneTwo_apply_two :
    Equiv.swap (1 : Fin 3) 2 2 = 1 := by decide

@[simp] theorem finThreeSwapZeroOne_apply_zero :
    Equiv.swap (0 : Fin 3) 1 0 = 1 := by decide

@[simp] theorem finThreeSwapZeroOne_apply_one :
    Equiv.swap (0 : Fin 3) 1 1 = 0 := by decide

@[simp] theorem finThreeSwapZeroOne_apply_two :
    Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide

@[simp] theorem finThreeSwapZeroTwo_apply_zero :
    Equiv.swap (0 : Fin 3) 2 0 = 2 := by decide

@[simp] theorem finThreeSwapZeroTwo_apply_one :
    Equiv.swap (0 : Fin 3) 2 1 = 1 := by decide

@[simp] theorem finThreeSwapZeroTwo_apply_two :
    Equiv.swap (0 : Fin 3) 2 2 = 0 := by decide

/-- There are exactly the displayed six permutations of `Fin 3`. -/
theorem finThreePerm_univ_explicit :
    (Finset.univ : Finset (Equiv.Perm (Fin 3))) =
      {1, Equiv.swap 1 2, Equiv.swap 0 1, finThreeCycleForward,
        finThreeCycleBackward, Equiv.swap 0 2} := by
  decide

/-- Multiplication of complex-valued truth indicators is conjunction. -/
@[simp] theorem complex_truthIndicator_mul (P Q : Prop)
    [Decidable P] [Decidable Q] :
    (if P then (1 : ℂ) else 0) * (if Q then (1 : ℂ) else 0) =
      if P ∧ Q then (1 : ℂ) else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- A complex-valued equality indicator.  Keeping it bundled while normalizing
the six concrete permutations avoids transporting implementation-level
`Decidable` witnesses inside nested `if` expressions. -/
noncomputable def complexEqIndicator (x y : ι) : ℂ :=
  if x = y then 1 else 0

set_option maxHeartbeats 1200000 in
/-- The abstract permutation sum on `Fin 3` is the explicit six-term
Kronecker kernel above. -/
theorem finThreePerm_indicator_sum_eq_thirdMomentKernel
    (u v : Fin 3 → ι) :
    (∑ π : Equiv.Perm (Fin 3),
        ∏ a : Fin 3, if u a = v (π a) then (1 : ℂ) else 0) =
      complexProjectiveThirdMomentKernel ι
        (u 0) (v 0) (u 1) (v 1) (u 2) (v 2) := by
  change
    (∑ π : Equiv.Perm (Fin 3),
        ∏ a : Fin 3, complexEqIndicator ι (u a) (v (π a))) =
      complexProjectiveThirdMomentKernel ι
        (u 0) (v 0) (u 1) (v 1) (u 2) (v 2)
  rw [finThreePerm_univ_explicit]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  simp only [Finset.sum_singleton]
  simp [Fin.prod_univ_succ, finThreeCycleForward, finThreeCycleBackward,
    Equiv.swap_apply_def]
  dsimp [complexProjectiveThirdMomentKernel]
  simp only [complexEqIndicator, complex_truthIndicator_mul]
  ring

/-- The concrete normalized complex-projective Haar law satisfies the full
order-three coordinate tensor formula, with no axioms or project-specific
premises. -/
theorem complexProjectiveCoordinateThirdMomentFormula_proved :
    ComplexProjectiveCoordinateThirdMomentFormula ι := by
  intro u v
  have hleft :
      (∫ B, ∏ a : Fin 3, B (u a) (v a) ∂complexProjectiveHaarLaw ι) =
        ∫ B, B (u 0) (v 0) * B (u 1) (v 1) * B (u 2) (v 2)
          ∂complexProjectiveHaarLaw ι := by
    apply integral_congr_ae
    filter_upwards [] with B
    simp [Fin.prod_univ_succ, mul_assoc]
  rw [hleft, complexProjectiveHaar_coordinateThirdMoment_formula,
    finThreePerm_indicator_sum_eq_thirdMomentKernel]

end CoordinateThirdMoments

end

end TomographyOracleCore
