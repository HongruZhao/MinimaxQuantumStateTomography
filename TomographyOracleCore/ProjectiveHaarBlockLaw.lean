import TomographyOracleCore.ProjectiveHaarBlockBeta
import TomographyOracleCore.PortedFixedSubspaceGaussian
import TomographyOracleCore.PortedGaussianSphereDirection
import TomographyOracleCore.PortedGaussianSubspace
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

/-!
# Exact two-complex-dimensional block law for the Haar sphere

This module closes the geometric pushforward proposition isolated in
`ProjectiveHaarBlockBeta`.  The proof uses only the self-contained port of
the Gaussian polar decomposition, the fixed-subspace Gaussian theorem, and
the scalar Gamma-to-Beta change of variables.
-/

/-- The first two complex coordinates, regarded as a complex subspace of
`ℂ^(2+k)`. -/
def complexHaarHeadComplexSubspace (k : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (2 + k))) where
  carrier := {x | ∀ j : Fin k, x (Fin.natAdd 2 j) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    simp [hx j, hy j]
  smul_mem' := by
    intro c x hx j
    simp [hx j]

/-- The same head space over the real scalars used by `stdGaussian`. -/
def complexHaarHeadRealSubspace (k : ℕ) :
    Submodule ℝ (EuclideanSpace ℂ (Fin (2 + k))) :=
  (complexHaarHeadComplexSubspace k).restrictScalars ℝ

/-- Extract the first two coordinates from the head subspace. -/
def complexHaarHeadCoord (k : ℕ)
    (x : complexHaarHeadComplexSubspace k) :
    EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (fun i ↦ x.1 (Fin.castAdd k i))

/-- Embed a two-coordinate vector into the head of `ℂ^(2+k)`. -/
def complexHaarHeadEmbed (k : ℕ)
    (x : EuclideanSpace ℂ (Fin 2)) :
    complexHaarHeadComplexSubspace k :=
  ⟨WithLp.toLp 2 (fun q ↦
      Sum.elim (fun i ↦ x i) (fun _ ↦ 0) (finSumFinEquiv.symm q)), by
    intro j
    simp⟩

@[simp] theorem complexHaarHeadCoord_apply (k : ℕ)
    (x : complexHaarHeadComplexSubspace k) (i : Fin 2) :
    complexHaarHeadCoord k x i = x.1 (Fin.castAdd k i) := rfl

@[simp] theorem complexHaarHeadEmbed_apply_castAdd (k : ℕ)
    (x : EuclideanSpace ℂ (Fin 2)) (i : Fin 2) :
    (complexHaarHeadEmbed k x).1 (Fin.castAdd k i) = x i := by
  simp [complexHaarHeadEmbed]

@[simp] theorem complexHaarHeadEmbed_apply_natAdd (k : ℕ)
    (x : EuclideanSpace ℂ (Fin 2)) (j : Fin k) :
    (complexHaarHeadEmbed k x).1 (Fin.natAdd 2 j) = 0 := by
  simp [complexHaarHeadEmbed]

/-- Complex-linear equivalence between the head subspace and `ℂ²`. -/
def complexHaarHeadLinearEquiv (k : ℕ) :
    complexHaarHeadComplexSubspace k ≃ₗ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun := complexHaarHeadCoord k
  invFun := complexHaarHeadEmbed k
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl
  left_inv x := by
    apply Subtype.ext
    ext q
    generalize hq : finSumFinEquiv.symm q = z
    cases z with
    | inl i =>
        have hqi : q = Fin.castAdd k i := by
          simpa using congrArg finSumFinEquiv hq
        subst q
        simp
    | inr j =>
        have hqj : q = Fin.natAdd 2 j := by
          simpa using congrArg finSumFinEquiv hq
        subst q
        simp [x.2 j]
  right_inv x := by
    ext i
    simp [complexHaarHeadCoord]

theorem complexHaarHeadLinearEquiv_inner (k : ℕ)
    (x y : complexHaarHeadComplexSubspace k) :
    ⟪complexHaarHeadLinearEquiv k x,
      complexHaarHeadLinearEquiv k y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [complexHaarHeadLinearEquiv, complexHaarHeadCoord,
    PiLp.inner_apply, RCLike.inner_apply, Submodule.coe_inner]
  rw [Fin.sum_univ_add]
  rw [show (∑ i : Fin k,
      y.1 (Fin.natAdd 2 i) * starRingEnd ℂ (x.1 (Fin.natAdd 2 i))) = 0 by
    apply Finset.sum_eq_zero
    intro i hi
    rw [x.2 i, y.2 i]
    simp]
  simp

/-- Isometric form of the complex head-coordinate equivalence. -/
def complexHaarHeadIsometryEquiv (k : ℕ) :
    complexHaarHeadComplexSubspace k ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearEquiv.isometryOfInner (𝕜 := ℂ) (complexHaarHeadLinearEquiv k)
    (fun x y ↦ complexHaarHeadLinearEquiv_inner k x y)

/-- The same isometry over real scalars. -/
def complexHaarHeadRealIsometryEquiv (k : ℕ) :
    complexHaarHeadRealSubspace k ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun x := complexHaarHeadIsometryEquiv k ⟨x.1, x.2⟩
  invFun y :=
    ⟨(complexHaarHeadIsometryEquiv k).symm y,
      (complexHaarHeadIsometryEquiv k).symm y |>.property⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg Subtype.val
      ((complexHaarHeadIsometryEquiv k).symm_apply_apply ⟨x.1, x.2⟩)
  right_inv y := (complexHaarHeadIsometryEquiv k).apply_symm_apply y
  map_add' x y := by
    exact map_add (complexHaarHeadIsometryEquiv k) ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  map_smul' c x := by
    change complexHaarHeadIsometryEquiv k
        ⟨((c : ℂ) • x.1), ?_⟩ =
      c • complexHaarHeadIsometryEquiv k ⟨x.1, x.2⟩
    exact map_smul (complexHaarHeadIsometryEquiv k) (c : ℂ) ⟨x.1, x.2⟩
  norm_map' x := by
    exact (complexHaarHeadIsometryEquiv k).norm_map ⟨x.1, x.2⟩

theorem finrank_complexHaarHeadRealSubspace (k : ℕ) :
    Module.finrank ℝ (complexHaarHeadRealSubspace k) = 4 := by
  have h := LinearEquiv.finrank_eq
    (complexHaarHeadRealIsometryEquiv k).toLinearEquiv
  rw [finrank_real_of_complex] at h
  simpa using h

theorem finrank_complexEuclideanSpace_real_headBlock (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [finrank_real_of_complex]
  simp

theorem finrank_complexHaarHeadRealSubspace_orthogonal (k : ℕ) :
    Module.finrank ℝ (complexHaarHeadRealSubspace k).orthogonal = 2 * k := by
  have h := (complexHaarHeadRealSubspace k).finrank_add_finrank_orthogonal
  rw [finrank_complexHaarHeadRealSubspace,
    finrank_complexEuclideanSpace_real_headBlock (2 + k)] at h
  omega

/-! ## Coordinate identification of the orthogonal projection -/

/-- Ambient vector retaining exactly the first two complex coordinates. -/
def complexHaarHeadPart (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    EuclideanSpace ℂ (Fin (2 + k)) :=
  (complexHaarHeadEmbed k (WithLp.toLp 2
    (fun i : Fin 2 ↦ x (Fin.castAdd k i)))).1

@[simp] theorem complexHaarHeadPart_apply_castAdd (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) (i : Fin 2) :
    complexHaarHeadPart k x (Fin.castAdd k i) = x (Fin.castAdd k i) := by
  simp [complexHaarHeadPart]

@[simp] theorem complexHaarHeadPart_apply_natAdd (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) (j : Fin k) :
    complexHaarHeadPart k x (Fin.natAdd 2 j) = 0 := by
  simp [complexHaarHeadPart]

theorem complexHaarHeadPart_mem (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    complexHaarHeadPart k x ∈ complexHaarHeadRealSubspace k := by
  intro j
  simp

theorem complexHaarHeadPart_is_projection (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    (complexHaarHeadRealSubspace k).starProjection x =
      complexHaarHeadPart k x := by
  apply (complexHaarHeadRealSubspace k).eq_starProjection_of_mem_of_inner_eq_zero
  · exact complexHaarHeadPart_mem k x
  · intro w hw
    simp only [PiLp.inner_apply]
    rw [Fin.sum_univ_add]
    simp only [PiLp.sub_apply]
    have hhead : (∑ i : Fin 2,
        ⟪x (Fin.castAdd k i) - complexHaarHeadPart k x (Fin.castAdd k i),
          w (Fin.castAdd k i)⟫_ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp
    have htail : (∑ j : Fin k,
        ⟪x (Fin.natAdd 2 j) - complexHaarHeadPart k x (Fin.natAdd 2 j),
          w (Fin.natAdd 2 j)⟫_ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hwj : w (Fin.natAdd 2 j) = 0 := hw j
      rw [hwj]
      simp
    rw [hhead, htail, add_zero]

theorem complexHaarHeadPart_norm_sq (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    ‖complexHaarHeadPart k x‖ ^ 2 =
      ∑ i : Fin 2, Complex.normSq (x (Fin.castAdd k i)) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_add]
  simp [Complex.normSq_eq_norm_sq]

/-- Coordinate head mass is exactly the squared norm of the fixed-subspace
orthogonal projection. -/
theorem complexHaarHeadMass_eq_projection_norm_sq (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    complexHaarHeadMass k x =
      ‖(complexHaarHeadRealSubspace k).orthogonalProjectionOnto x.1‖ ^ 2 := by
  change (∑ i : Fin 2, Complex.normSq (x.1 (Fin.castAdd k i))) = _
  rw [show ‖(complexHaarHeadRealSubspace k).orthogonalProjectionOnto x.1‖ =
      ‖complexHaarHeadPart k x.1‖ by
    change ‖((complexHaarHeadRealSubspace k).starProjection x.1)‖ = _
    rw [complexHaarHeadPart_is_projection]]
  exact (complexHaarHeadPart_norm_sq k x.1).symm

/-! ## Gaussian ratio law and polar transfer -/

/-- Ambient fraction of energy contained in the two-complex-dimensional
head subspace. -/
def complexHaarAmbientHeadFraction (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) : ℝ :=
  ‖(complexHaarHeadRealSubspace k).orthogonalProjectionOnto x‖ ^ 2 /
    ‖x‖ ^ 2

theorem measurable_complexHaarAmbientHeadFraction (k : ℕ) :
    Measurable (complexHaarAmbientHeadFraction k) := by
  unfold complexHaarAmbientHeadFraction
  fun_prop

/-- Under the literal ambient standard Gaussian, the head-energy fraction is
exactly `Beta(2,k)`. -/
theorem map_complexHaarAmbientHeadFraction_stdGaussian
    (k : ℕ) (hk : 1 ≤ k) :
    Measure.map (complexHaarAmbientHeadFraction k)
        (stdGaussian (EuclideanSpace ℂ (Fin (2 + k)))) =
      betaMeasure 2 (k : ℝ) := by
  let K := complexHaarHeadRealSubspace k
  letI : Nontrivial K :=
    Module.nontrivial_of_finrank_pos (by
      rw [show Module.finrank ℝ K = 4 by
        exact finrank_complexHaarHeadRealSubspace k]
      norm_num)
  letI : Nontrivial K.orthogonal :=
    Module.nontrivial_of_finrank_pos (by
      rw [show Module.finrank ℝ K.orthogonal = 2 * k by
        exact finrank_complexHaarHeadRealSubspace_orthogonal k]
      omega)
  have h := (LogdetLean.hasLaw_orthogonalProjection_normSq_ratio_beta K).map_eq
  change Measure.map (complexHaarAmbientHeadFraction k)
      (stdGaussian (EuclideanSpace ℂ (Fin (2 + k)))) = _
  change Measure.map
      (fun x => ‖(complexHaarHeadRealSubspace k).starProjection x‖ ^ 2 /
        ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℂ (Fin (2 + k)))) = betaMeasure 2 (k : ℝ)
  convert h using 1 <;>
    simp [K, finrank_complexHaarHeadRealSubspace,
      finrank_complexHaarHeadRealSubspace_orthogonal] <;> norm_num

/-- The ambient head-energy fraction is unchanged by normalization to unit
direction away from the Gaussian-null origin. -/
theorem complexHaarAmbientHeadFraction_unitDirection
    (k : ℕ) (x : EuclideanSpace ℂ (Fin (2 + k))) (hx : x ≠ 0) :
    complexHaarAmbientHeadFraction k (LogdetLean.unitDirection x) =
      complexHaarAmbientHeadFraction k x := by
  unfold complexHaarAmbientHeadFraction LogdetLean.unitDirection
  rw [if_neg hx]
  simp only [map_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-- On the unit sphere, the ambient fraction agrees with the coordinate head
mass. -/
theorem complexHaarAmbientHeadFraction_coe_sphere (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    complexHaarAmbientHeadFraction k x.1 = complexHaarHeadMass k x := by
  rw [complexHaarHeadMass_eq_projection_norm_sq]
  unfold complexHaarAmbientHeadFraction
  have hxnorm : ‖x.1‖ = 1 := by
    simpa [mem_sphere] using x.2
  rw [hxnorm]
  norm_num

/-- The first two complex coordinate masses of a normalized Haar unit vector
have the exact `Beta(2,k)` law. -/
theorem complexHaarHeadMass_betaLaw (k : ℕ) (hk : 1 ≤ k) :
    ComplexHaarHeadMassBetaLaw k := by
  let E := EuclideanSpace ℂ (Fin (2 + k))
  let sphereVal : sphere (0 : E) 1 → E := Subtype.val
  let sphereLaw : Measure (sphere (0 : E) 1) :=
    complexUnitSphereHaarLaw (Fin (2 + k))
  have hdir :=
    LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure
      (E := E)
  have hsphere : LogdetLean.uniformSphereSurfaceMeasure (E := E) =
      sphereLaw := by
    rfl
  rw [hsphere] at hdir
  have hzero : ∀ᵐ x ∂(stdGaussian E), x ≠ 0 := by
    simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton (E := E)
  have hinvariant :
      (complexHaarAmbientHeadFraction k ∘ LogdetLean.unitDirection) =ᵐ[
        stdGaussian E] complexHaarAmbientHeadFraction k := by
    filter_upwards [hzero] with x hx
    exact complexHaarAmbientHeadFraction_unitDirection k x hx
  have hspherefun :
      complexHaarAmbientHeadFraction k ∘ sphereVal =
        complexHaarHeadMass k := by
    funext x
    exact complexHaarAmbientHeadFraction_coe_sphere k x
  unfold ComplexHaarHeadMassBetaLaw
  calc
    Measure.map (complexHaarHeadMass k) sphereLaw =
        Measure.map (complexHaarAmbientHeadFraction k)
          (Measure.map sphereVal sphereLaw) := by
      rw [Measure.map_map (measurable_complexHaarAmbientHeadFraction k)
        measurable_subtype_coe]
      rw [hspherefun]
    _ = Measure.map (complexHaarAmbientHeadFraction k)
          (Measure.map LogdetLean.unitDirection (stdGaussian E)) := by
      rw [hdir]
    _ = Measure.map
          (complexHaarAmbientHeadFraction k ∘ LogdetLean.unitDirection)
          (stdGaussian E) := by
      rw [Measure.map_map (measurable_complexHaarAmbientHeadFraction k)
        LogdetLean.measurable_unitDirection]
    _ = Measure.map (complexHaarAmbientHeadFraction k)
          (stdGaussian E) := Measure.map_congr hinvariant
    _ = betaMeasure 2 (k : ℝ) :=
      map_complexHaarAmbientHeadFraction_stdGaussian k hk

/-- Exact, unconditional Haar inverse information moment. -/
theorem integral_complexHaarHeadMass_information_unconditional
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1,
        (1 - complexHaarHeadMass k x) ^ 2 / complexHaarHeadMass k x
      ∂complexUnitSphereHaarLaw (Fin (2 + k)) =
      (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) :=
  integral_complexHaarHeadMass_information k hk
    (complexHaarHeadMass_betaLaw k hk)

end

end TomographyOracleCore
