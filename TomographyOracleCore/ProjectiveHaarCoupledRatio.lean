import TomographyOracleCore.ProjectiveHaarTailCoupling
import Mathlib.Probability.Independence.Integration

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder

noncomputable section

/-!
# The exact coupled head/tail Haar ratio

This file combines the independent complex-Gaussian head fraction and
normalized tail direction.  It proves the singular rank-one kernel needed by
the arbitrary-outcome one-copy POVM calculation, with its exact `1 / (k+2)`
constant.
-/

/-- The scalar singular weight attached to the two-coordinate head block. -/
def complexHaarHeadInformationAmbient (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) : ℝ :=
  (1 - complexHaarAmbientHeadFraction k x) ^ 2 /
    complexHaarAmbientHeadFraction k x

theorem measurable_complexHaarHeadInformationAmbient (k : ℕ) :
    Measurable (complexHaarHeadInformationAmbient k) := by
  unfold complexHaarHeadInformationAmbient
  exact (((measurable_const.sub
    (measurable_complexHaarAmbientHeadFraction k)).pow_const 2).div
      (measurable_complexHaarAmbientHeadFraction k))

/-- Squared centered tail quadratic form evaluated at totalized tail
direction. -/
def complexHaarTailDirectionQuadraticSq (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) : ℝ :=
  (hermitianQuadraticValue A
    (LogdetLean.unitDirection (complexHaarTailCoordAmbient k x))) ^ 2

theorem measurable_complexHaarTailDirectionQuadraticSq (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    Measurable (complexHaarTailDirectionQuadraticSq k A) := by
  unfold complexHaarTailDirectionQuadraticSq
  have htail : Measurable (complexHaarTailCoordAmbient k) := by
    unfold complexHaarTailCoordAmbient
    fun_prop
  have hdir := LogdetLean.measurable_unitDirection.comp htail
  unfold hermitianQuadraticValue
  fun_prop

/-- Exact singular Beta moment of the head block. -/
theorem integral_complexHaarHeadInformationAmbient_stdGaussian
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ x, complexHaarHeadInformationAmbient k x
      ∂stdGaussian (EuclideanSpace ℂ (Fin (2 + k))) =
      (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
  let E := EuclideanSpace ℂ (Fin (2 + k))
  let g : ℝ → ℝ := fun s ↦ (1 - s) ^ 2 / s
  have hg : AEStronglyMeasurable g
      (Measure.map (complexHaarAmbientHeadFraction k) (stdGaussian E)) :=
    (by fun_prop : Measurable g).aestronglyMeasurable
  calc
    (∫ x, complexHaarHeadInformationAmbient k x ∂stdGaussian E) =
        ∫ x, g (complexHaarAmbientHeadFraction k x) ∂stdGaussian E := by
      rfl
    _ = ∫ s, g s ∂Measure.map (complexHaarAmbientHeadFraction k)
          (stdGaussian E) := by
      symm
      exact integral_map
        (measurable_complexHaarAmbientHeadFraction k).aemeasurable hg
    _ = ∫ s, (1 - s) ^ 2 / s ∂betaMeasure 2 (k : ℝ) := by
      rw [map_complexHaarAmbientHeadFraction_stdGaussian k hk]
    _ = (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) :=
      integral_one_sub_sq_div_betaMeasure_two k hk

/-- The projective trace pairing equals the vector quadratic form. -/
theorem trace_mul_complexSphereProjector_re_eq_quadratic
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin k)) 1) :
    (A * complexSphereProjector x).trace.re =
      hermitianQuadraticValue A x.1 := by
  simp only [complexSphereProjector, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, hermitianQuadraticValue,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin]
  rfl

/-- Exact centered Hermitian quadratic second moment on the complex unit
sphere. -/
theorem integral_complexUnitSphereHaar_quadratic_sq
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    (∫ x : sphere (0 : EuclideanSpace ℂ (Fin k)) 1,
        (hermitianQuadraticValue A x.1) ^ 2
        ∂complexUnitSphereHaarLaw (Fin k)) =
      (A * A).trace.re / ((k : ℝ) * ((k : ℝ) + 1)) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  let f : Matrix (Fin k) (Fin k) ℂ → ℝ :=
    fun P ↦ ((A * P).trace.re) ^ 2
  have hfint : Integrable f (complexProjectiveHaarLaw (Fin k)) := by
    have hc :=
      (integrable_complexProjectiveHaar_trace_mul_two (Fin k) A A).re
    apply hc.congr
    filter_upwards [complexProjectiveHaar_ae_posSemidef (Fin k)] with P hP
    rw [trace_mul_eq_re_of_isHermitian A P hA hP.isHermitian]
    simp [f, pow_two]
  calc
    (∫ x : sphere (0 : EuclideanSpace ℂ (Fin k)) 1,
        (hermitianQuadraticValue A x.1) ^ 2
        ∂complexUnitSphereHaarLaw (Fin k)) =
        ∫ x, f (complexSphereProjector x)
          ∂complexUnitSphereHaarLaw (Fin k) := by
      apply integral_congr_ae
      filter_upwards [] with x
      change (hermitianQuadraticValue A x.1) ^ 2 =
        ((A * complexSphereProjector x).trace.re) ^ 2
      rw [trace_mul_complexSphereProjector_re_eq_quadratic]
    _ = ∫ P, f P ∂complexProjectiveHaarLaw (Fin k) := by
      unfold complexProjectiveHaarLaw
      exact (integral_map
        (measurable_complexSphereProjector (ι := Fin k)).aemeasurable
        hfint.aestronglyMeasurable).symm
    _ = (A * A).trace.re / ((k : ℝ) * ((k : ℝ) + 1)) :=
      integral_complexProjectiveHaar_centered_quadratic_sq
        k hk A hA htrace

/-- The normalized Gaussian tail has the same exact quadratic moment as a
complex Haar unit vector. -/
theorem integral_tailDirectionQuadraticSq_stdGaussian
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    ∫ x, complexHaarTailDirectionQuadraticSq k A x
      ∂stdGaussian (EuclideanSpace ℂ (Fin (2 + k))) =
      (A * A).trace.re / ((k : ℝ) * ((k : ℝ) + 1)) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  let E := EuclideanSpace ℂ (Fin k)
  let EA := EuclideanSpace ℂ (Fin (2 + k))
  let q : E → ℝ := fun u ↦ (hermitianQuadraticValue A u) ^ 2
  have hq : Measurable q := by
    unfold q hermitianQuadraticValue
    fun_prop
  have htail := hasLaw_complexHaarTailCoordAmbient_stdGaussian k
  have hdir :=
    LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure
      (E := E)
  have hsphere : LogdetLean.uniformSphereSurfaceMeasure (E := E) =
      complexUnitSphereHaarLaw (Fin k) := by
    rfl
  rw [hsphere] at hdir
  calc
    (∫ x, complexHaarTailDirectionQuadraticSq k A x ∂stdGaussian EA) =
        ∫ x, q (LogdetLean.unitDirection
          (complexHaarTailCoordAmbient k x)) ∂stdGaussian EA := by
      rfl
    _ = ∫ y, q (LogdetLean.unitDirection y)
          ∂Measure.map (complexHaarTailCoordAmbient k) (stdGaussian EA) := by
      symm
      exact integral_map
        (by fun_prop : AEMeasurable (complexHaarTailCoordAmbient k)
          (stdGaussian EA))
        (hq.comp LogdetLean.measurable_unitDirection).aestronglyMeasurable
    _ = ∫ y, q (LogdetLean.unitDirection y) ∂stdGaussian E := by
      rw [htail.map_eq]
    _ = ∫ u, q u ∂Measure.map LogdetLean.unitDirection
          (stdGaussian E) := by
      symm
      exact integral_map LogdetLean.measurable_unitDirection.aemeasurable
        hq.aestronglyMeasurable
    _ = ∫ u, q u ∂Measure.map
        (Subtype.val : sphere (0 : E) 1 → E)
        (complexUnitSphereHaarLaw (Fin k)) := by
      rw [hdir]
    _ = ∫ x : sphere (0 : E) 1, q x.1
          ∂complexUnitSphereHaarLaw (Fin k) := by
      exact integral_map measurable_subtype_coe.aemeasurable
        hq.aestronglyMeasurable
    _ = (A * A).trace.re / ((k : ℝ) * ((k : ℝ) + 1)) :=
      integral_complexUnitSphereHaar_quadratic_sq k hk A hA htrace

/-- The two independent factors combine to the exact Gaussian coupled
kernel. -/
theorem integral_complexHaarCoupledProduct_stdGaussian
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    ∫ x, complexHaarHeadInformationAmbient k x *
        complexHaarTailDirectionQuadraticSq k A x
      ∂stdGaussian (EuclideanSpace ℂ (Fin (2 + k))) =
      (A * A).trace.re / ((k : ℝ) + 2) := by
  let E := EuclideanSpace ℂ (Fin (2 + k))
  let headTransform : ℝ → ℝ := fun s ↦ (1 - s) ^ 2 / s
  let tailTransform : EuclideanSpace ℂ (Fin k) → ℝ :=
    fun u ↦ (hermitianQuadraticValue A u) ^ 2
  have hind0 :=
    indepFun_complexHaarAmbientHeadFraction_tailDirection_stdGaussian k hk
  have hind : IndepFun (complexHaarHeadInformationAmbient k)
      (complexHaarTailDirectionQuadraticSq k A) (stdGaussian E) := by
    have hcomp := hind0.comp
      (φ := headTransform) (ψ := tailTransform)
      (by unfold headTransform; fun_prop)
      (by unfold tailTransform hermitianQuadraticValue; fun_prop)
    change IndepFun
      (fun x : E ↦ (1 - complexHaarAmbientHeadFraction k x) ^ 2 /
        complexHaarAmbientHeadFraction k x)
      (fun x : E ↦ (hermitianQuadraticValue A
        (LogdetLean.unitDirection (complexHaarTailCoordAmbient k x))) ^ 2)
      (stdGaussian E)
    simpa [Function.comp_def, headTransform, tailTransform] using hcomp
  have hfactor := hind.integral_mul_eq_mul_integral
    (measurable_complexHaarHeadInformationAmbient k).aestronglyMeasurable
    (measurable_complexHaarTailDirectionQuadraticSq k A).aestronglyMeasurable
  change (∫ x : E, complexHaarHeadInformationAmbient k x *
      complexHaarTailDirectionQuadraticSq k A x ∂stdGaussian E) = _ at hfactor
  rw [hfactor]
  rw [integral_complexHaarHeadInformationAmbient_stdGaussian k hk]
  rw [integral_tailDirectionQuadraticSq_stdGaussian k hk A hA htrace]
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : k ≠ 0)
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- Totalized unit direction is unchanged by multiplication by a positive
real scalar. -/
theorem unitDirection_real_smul_of_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (hc : 0 < c) (x : E) :
    LogdetLean.unitDirection (c • x) =
      LogdetLean.unitDirection x := by
  by_cases hx : x = 0
  · subst x
    simp [LogdetLean.unitDirection]
  · have hc0 : c ≠ 0 := ne_of_gt hc
    have hcx : c • x ≠ 0 := smul_ne_zero hc0 hx
    simp only [LogdetLean.unitDirection, if_neg hx, if_neg hcx]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
    simp only [smul_smul]
    congr 1
    field_simp [hc0, norm_ne_zero_iff.mpr hx]

/-- Literal tail-coordinate extraction is real-linear. -/
theorem complexHaarTailCoordAmbient_real_smul (k : ℕ)
    (c : ℝ) (x : EuclideanSpace ℂ (Fin (2 + k))) :
    complexHaarTailCoordAmbient k (c • x) =
      c • complexHaarTailCoordAmbient k x := by
  ext j
  rfl

/-- The head-information weight is scale invariant under totalized unit
direction away from zero. -/
theorem complexHaarHeadInformationAmbient_unitDirection
    (k : ℕ) (x : EuclideanSpace ℂ (Fin (2 + k))) (hx : x ≠ 0) :
    complexHaarHeadInformationAmbient k (LogdetLean.unitDirection x) =
      complexHaarHeadInformationAmbient k x := by
  unfold complexHaarHeadInformationAmbient
  rw [complexHaarAmbientHeadFraction_unitDirection k x hx]

/-- The normalized tail quadratic factor is scale invariant under ambient
normalization away from zero. -/
theorem complexHaarTailDirectionQuadraticSq_unitDirection
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) (hx : x ≠ 0) :
    complexHaarTailDirectionQuadraticSq k A
        (LogdetLean.unitDirection x) =
      complexHaarTailDirectionQuadraticSq k A x := by
  have hinv : 0 < ‖x‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr hx)
  have htail : complexHaarTailCoordAmbient k
      (LogdetLean.unitDirection x) =
      ‖x‖⁻¹ • complexHaarTailCoordAmbient k x := by
    rw [show LogdetLean.unitDirection x = ‖x‖⁻¹ • x by
      simp [LogdetLean.unitDirection, hx]]
    exact complexHaarTailCoordAmbient_real_smul k ‖x‖⁻¹ x
  unfold complexHaarTailDirectionQuadraticSq
  rw [htail]
  rw [unitDirection_real_smul_of_pos ‖x‖⁻¹ hinv]

/-- Exact coupled singular moment on the complex unit sphere:

`E[(tail* A tail)^2 / headMass] = tr(A^2)/(k+2)`.
-/
theorem integral_complexHaarTailQuadratic_sq_div_headMass
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    (∫ x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1,
        (hermitianQuadraticValue A (complexHaarTailVector k x)) ^ 2 /
          complexHaarHeadMass k x
        ∂complexUnitSphereHaarLaw (Fin (2 + k))) =
      (A * A).trace.re / ((k : ℝ) + 2) := by
  let E := EuclideanSpace ℂ (Fin (2 + k))
  let sphereLaw : Measure (sphere (0 : E) 1) :=
    complexUnitSphereHaarLaw (Fin (2 + k))
  let ambientObservable : E → ℝ := fun x ↦
    complexHaarHeadInformationAmbient k x *
      complexHaarTailDirectionQuadraticSq k A x
  have hambientMeas : Measurable ambientObservable := by
    unfold ambientObservable
    exact (measurable_complexHaarHeadInformationAmbient k).mul
      (measurable_complexHaarTailDirectionQuadraticSq k A)
  have hspherePoint (x : sphere (0 : E) 1) :
      (hermitianQuadraticValue A (complexHaarTailVector k x)) ^ 2 /
          complexHaarHeadMass k x = ambientObservable x.1 := by
    rw [complexHaarTailRatio_factor]
    unfold ambientObservable complexHaarHeadInformationAmbient
    rw [complexHaarAmbientHeadFraction_coe_sphere]
    rfl
  have hdir :=
    LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure
      (E := E)
  have hsphere : LogdetLean.uniformSphereSurfaceMeasure (E := E) =
      sphereLaw := by
    rfl
  rw [hsphere] at hdir
  have hzero : ∀ᵐ x ∂(stdGaussian E), x ≠ 0 := by
    simpa [ae_iff] using LogdetLean.stdGaussian_zero_singleton (E := E)
  calc
    (∫ x : sphere (0 : E) 1,
        (hermitianQuadraticValue A (complexHaarTailVector k x)) ^ 2 /
          complexHaarHeadMass k x ∂sphereLaw) =
        ∫ x : sphere (0 : E) 1, ambientObservable x.1 ∂sphereLaw := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hspherePoint x
    _ = ∫ y, ambientObservable y
          ∂Measure.map (Subtype.val : sphere (0 : E) 1 → E) sphereLaw := by
      exact (integral_map measurable_subtype_coe.aemeasurable
        hambientMeas.aestronglyMeasurable).symm
    _ = ∫ y, ambientObservable y
          ∂Measure.map LogdetLean.unitDirection (stdGaussian E) := by
      rw [hdir]
    _ = ∫ x, ambientObservable (LogdetLean.unitDirection x)
          ∂stdGaussian E := by
      exact integral_map LogdetLean.measurable_unitDirection.aemeasurable
        hambientMeas.aestronglyMeasurable
    _ = ∫ x, ambientObservable x ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards [hzero] with x hx
      unfold ambientObservable
      rw [complexHaarHeadInformationAmbient_unitDirection k x hx,
        complexHaarTailDirectionQuadraticSq_unitDirection k A x hx]
    _ = (A * A).trace.re / ((k : ℝ) + 2) :=
      integral_complexHaarCoupledProduct_stdGaussian k hk A hA htrace

end

end TomographyOracleCore
