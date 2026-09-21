import TomographyOracleCore.GammaLaplace
import TomographyOracleCore.GaussianRadialDirectionIndependence
import TomographyOracleCore.PortedFixedSubspaceGaussian
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic

/-!
# Pure-sphere fixed-subspace Laplace bound

This module proves the Gaussian-radial comparison used in the
Hayden--Leung--Winter Grassmann concentration argument.  The only scalar
input is the exact integer-shape Gamma Laplace transform proved in
`GammaLaplace`.
-/

namespace TomographyOracleCore

noncomputable section

open MeasureTheory ProbabilityTheory Real Metric Set
open scoped InnerProductSpace RealInnerProductSpace

/-- A Gamma random variable is strictly positive almost surely. -/
theorem gammaMeasure_ae_pos (a r : ℝ) :
    ∀ᵐ x ∂gammaMeasure a r, 0 < x := by
  rw [gammaMeasure]
  refine (ae_withDensity_iff
    (measurable_gammaPDFReal a r).ennreal_ofReal).2 ?_
  have hzero : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hzero] with x hx0
  intro hpdf
  by_contra hx
  apply hpdf
  have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
  rw [gammaPDFReal, if_neg (not_le.mpr hxneg), ENNReal.ofReal_zero]

/-- Jensen comparison between a deterministic radial mean and the exact
Gamma radial law. -/
theorem exp_neg_nat_div_three_le_gammaLaplace
    {N : ℕ} (hN : 0 < N) {z : ℝ} (hz : 0 ≤ z) :
    Real.exp (-((N : ℝ) / 3) * z) ≤
      ∫ r : ℝ, Real.exp (-(z / 6) * r)
        ∂gammaMeasure (N : ℝ) (1 / 2) := by
  have hshape : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  letI : IsProbabilityMeasure (gammaMeasure (N : ℝ) (1 / 2)) :=
    isProbabilityMeasure_gammaMeasure hshape (by norm_num)
  let f : ℝ → ℝ := fun r ↦ -(z / 6) * r
  have hid : Integrable (fun r : ℝ ↦ r)
      (gammaMeasure (N : ℝ) (1 / 2)) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_id_gammaMeasure_nat_half hN]
    positivity
  have hf : Integrable f (gammaMeasure (N : ℝ) (1 / 2)) := by
    simpa only [f] using hid.const_mul (-(z / 6))
  have hexp : Integrable (fun r ↦ Real.exp (f r))
      (gammaMeasure (N : ℝ) (1 / 2)) := by
    apply Integrable.of_integral_ne_zero
    change (∫ r : ℝ, Real.exp (-(z / 6) * r)
      ∂gammaMeasure (N : ℝ) (1 / 2)) ≠ 0
    rw [integral_exp_neg_mul_gammaMeasure_nat_half hN (by positivity)]
    positivity
  have hmean : (∫ r, f r ∂gammaMeasure (N : ℝ) (1 / 2)) =
      -((N : ℝ) / 3) * z := by
    dsimp only [f]
    rw [integral_const_mul, integral_id_gammaMeasure_nat_half hN]
    ring
  have hJensen :=
    convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (by simp) hf hexp
  rw [hmean] at hJensen
  simpa only [Function.comp_apply, f] using hJensen

/-- Multiplying the projected energy of the unit direction by the original
radial energy recovers the projected Gaussian energy exactly. -/
theorem normSq_mul_projection_unitDirection_normSq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : Submodule ℝ E) (x : E) :
    ‖x‖ ^ 2 * ‖K.orthogonalProjectionOnto (LogdetLean.unitDirection x)‖ ^ 2 =
      ‖K.orthogonalProjectionOnto x‖ ^ 2 := by
  by_cases hx : x = 0
  · subst x
    simp [LogdetLean.unitDirection]
  · simp only [LogdetLean.unitDirection, if_neg hx, map_smul,
      norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
    have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    field_simp

section ProjectionLaplace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [Nontrivial E]

/-- After Jensen in the independent radial coordinate, the directional
Laplace integral is bounded by the corresponding product-law integral. -/
theorem direction_projection_laplace_le_product
    (K : Submodule ℝ E) {N : ℕ} (hN : 0 < N) :
    let ν := Measure.map LogdetLean.unitDirection (stdGaussian E)
    let γ := gammaMeasure (N : ℝ) (1 / 2)
    (∫ v : E, Real.exp
        (-((N : ℝ) / 3) * ‖K.orthogonalProjectionOnto v‖ ^ 2) ∂ν) ≤
      ∫ p : E × ℝ, Real.exp
        (-(‖K.orthogonalProjectionOnto p.1‖ ^ 2 / 6) * p.2) ∂ν.prod γ := by
  dsimp only
  let ν : Measure E :=
    Measure.map LogdetLean.unitDirection (stdGaussian E)
  let γ : Measure ℝ := gammaMeasure (N : ℝ) (1 / 2)
  let z : E → ℝ := fun v ↦ ‖K.orthogonalProjectionOnto v‖ ^ 2
  let F : E × ℝ → ℝ := fun p ↦ Real.exp (-(z p.1 / 6) * p.2)
  have hshape : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map
      LogdetLean.measurable_unitDirection.aemeasurable
  letI : IsProbabilityMeasure γ :=
    isProbabilityMeasure_gammaMeasure hshape (by norm_num)
  have hFmeas : Measurable F := by
    dsimp only [F, z]
    fun_prop
  have hpos : ∀ᵐ p ∂ν.prod γ, 0 < p.2 := by
    refine (Measure.ae_prod_iff_ae_ae
      (measurableSet_lt measurable_const measurable_snd)).2 ?_
    filter_upwards with v
    exact gammaMeasure_ae_pos (N : ℝ) (1 / 2)
  have hFint : Integrable F (ν.prod γ) := by
    apply Integrable.of_bound hFmeas.aestronglyMeasurable 1
    filter_upwards [hpos] with p hp
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    dsimp only [F, z]
    have hz0 : 0 ≤ ‖K.orthogonalProjectionOnto p.1‖ ^ 2 := sq_nonneg _
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg hz0 (by norm_num))) hp.le
  have hleft : Integrable
      (fun v : E ↦ Real.exp (-((N : ℝ) / 3) * z v)) ν := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards with v
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    have hz0 : 0 ≤ z v := by exact sq_nonneg _
    exact mul_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (div_nonneg hshape.le (by norm_num))) hz0
  have hright : Integrable (fun v ↦ ∫ r, F (v, r) ∂γ) ν :=
    hFint.integral_prod_left
  have hpoint (v : E) :
      Real.exp (-((N : ℝ) / 3) * z v) ≤ ∫ r, F (v, r) ∂γ := by
    simpa only [F, z, γ] using
      exp_neg_nat_div_three_le_gammaLaplace hN (sq_nonneg _)
  have hmono := integral_mono hleft hright hpoint
  change (∫ v : E, Real.exp
      (-((N : ℝ) / 3) * ‖K.orthogonalProjectionOnto v‖ ^ 2) ∂ν) ≤
    ∫ p : E × ℝ, Real.exp
      (-(‖K.orthogonalProjectionOnto p.1‖ ^ 2 / 6) * p.2) ∂ν.prod γ
  rw [integral_prod F hFint]
  exact hmono

/-- The product-law integral is exactly the projected-Gaussian Gamma
Laplace transform. -/
theorem product_projection_laplace_eq_three_quarters_pow
    (K : Submodule ℝ E) [Nontrivial K]
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hE : Module.finrank ℝ E = 2 * N)
    (hK : Module.finrank ℝ K = 2 * q) :
    let ν := Measure.map LogdetLean.unitDirection (stdGaussian E)
    let γ := gammaMeasure (N : ℝ) (1 / 2)
    (∫ p : E × ℝ, Real.exp
        (-(‖K.orthogonalProjectionOnto p.1‖ ^ 2 / 6) * p.2) ∂ν.prod γ) =
      (3 / 4 : ℝ) ^ q := by
  dsimp only
  let ν : Measure E :=
    Measure.map LogdetLean.unitDirection (stdGaussian E)
  let γ : Measure ℝ := gammaMeasure (N : ℝ) (1 / 2)
  let joint : E → E × ℝ := fun x ↦
    (LogdetLean.unitDirection x, ‖x‖ ^ 2)
  let F : E × ℝ → ℝ := fun p ↦ Real.exp
    (-(‖K.orthogonalProjectionOnto p.1‖ ^ 2 / 6) * p.2)
  have hrad : Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E) = γ := by
    change LogdetLean.stdGaussianNormSqMeasure E = γ
    rw [LogdetLean.stdGaussianNormSqMeasure_eq_gamma E, hE]
    simp only [γ]
    congr 2
    norm_num
  have hjoint : Measure.map joint (stdGaussian E) = ν.prod γ := by
    have h := map_gaussianDirectionEnergy_stdGaussian_eq_prod (E := E)
    rw [hrad] at h
    exact h
  have hFmeas : Measurable F := by
    dsimp only [F]
    fun_prop
  have hjointmeas : Measurable joint := by
    dsimp only [joint]
    exact LogdetLean.measurable_unitDirection.prodMk
      (measurable_id.norm.pow_const 2)
  have hmap :
      (∫ p, F p ∂ν.prod γ) = ∫ x, F (joint x) ∂stdGaussian E := by
    rw [← hjoint]
    exact integral_map hjointmeas.aemeasurable hFmeas.aestronglyMeasurable
  have hpoint (x : E) :
      F (joint x) = Real.exp
        (-(1 / 6 : ℝ) * ‖K.orthogonalProjectionOnto x‖ ^ 2) := by
    dsimp only [F, joint]
    congr 1
    rw [show
      -(‖K.orthogonalProjectionOnto (LogdetLean.unitDirection x)‖ ^ 2 / 6) *
          ‖x‖ ^ 2 =
        -(1 / 6 : ℝ) *
          (‖x‖ ^ 2 *
            ‖K.orthogonalProjectionOnto (LogdetLean.unitDirection x)‖ ^ 2) by ring]
    rw [normSq_mul_projection_unitDirection_normSq K x]
  have hproj : HasLaw
      (fun x : E ↦ ‖K.orthogonalProjectionOnto x‖ ^ 2)
      (gammaMeasure (q : ℝ) (1 / 2)) (stdGaussian E) := by
    convert LogdetLean.hasLaw_normSq_orthogonalProjection_gamma K using 1
    rw [hK]
    norm_num
  calc
    (∫ p : E × ℝ, Real.exp
        (-(‖K.orthogonalProjectionOnto p.1‖ ^ 2 / 6) * p.2) ∂ν.prod γ) =
        ∫ x, F (joint x) ∂stdGaussian E := hmap
    _ = ∫ x : E, Real.exp
        (-(1 / 6 : ℝ) * ‖K.orthogonalProjectionOnto x‖ ^ 2)
          ∂stdGaussian E := by
      apply integral_congr_ae
      filter_upwards with x
      exact hpoint x
    _ = ∫ s : ℝ, Real.exp (-(1 / 6 : ℝ) * s)
          ∂gammaMeasure (q : ℝ) (1 / 2) := by
      simpa only [Function.comp_apply] using
        hproj.integral_comp
          (f := fun s : ℝ ↦ Real.exp (-(1 / 6 : ℝ) * s)) (by fun_prop)
    _ = (1 / (1 + 2 * (1 / 6 : ℝ))) ^ q := by
      exact integral_exp_neg_mul_gammaMeasure_nat_half hq (by norm_num)
    _ = (3 / 4 : ℝ) ^ q := by norm_num

/-- Laplace bound for the normalized direction of a standard Gaussian. -/
theorem gaussianDirectionProjection_laplace_le
    (K : Submodule ℝ E) [Nontrivial K]
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hE : Module.finrank ℝ E = 2 * N)
    (hK : Module.finrank ℝ K = 2 * q) :
    (∫ v : E, Real.exp
        (-((N : ℝ) / 3) * ‖K.orthogonalProjectionOnto v‖ ^ 2)
      ∂Measure.map LogdetLean.unitDirection (stdGaussian E)) ≤
      (3 / 4 : ℝ) ^ q := by
  exact (direction_projection_laplace_le_product K hN).trans_eq
    (product_projection_laplace_eq_three_quarters_pow K hN hq hE hK)

/-- The fixed-subspace Laplace bound for Haar-uniform points on a real unit
sphere.  In real ambient dimension `2N` and real subspace dimension `2q`,
the constant is exactly `(3/4)^q`. -/
theorem pureSphereProjection_laplace_le
    (K : Submodule ℝ E) [Nontrivial K]
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q)
    (hE : Module.finrank ℝ E = 2 * N)
    (hK : Module.finrank ℝ K = 2 * q) :
    (∫ u : sphere (0 : E) 1, Real.exp
        (-((N : ℝ) / 3) *
          ‖K.orthogonalProjectionOnto (u : E)‖ ^ 2)
      ∂LogdetLean.uniformSphereSurfaceMeasure (E := E)) ≤
      (3 / 4 : ℝ) ^ q := by
  let f : E → ℝ := fun v ↦ Real.exp
    (-((N : ℝ) / 3) * ‖K.orthogonalProjectionOnto v‖ ^ 2)
  have hf : Measurable f := by
    dsimp only [f]
    fun_prop
  have hdir := gaussianDirectionProjection_laplace_le K hN hq hE hK
  rw [LogdetLean.map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure]
    at hdir
  calc
    (∫ u : sphere (0 : E) 1, Real.exp
        (-((N : ℝ) / 3) *
          ‖K.orthogonalProjectionOnto (u : E)‖ ^ 2)
      ∂LogdetLean.uniformSphereSurfaceMeasure (E := E)) =
        ∫ v : E, f v
          ∂Measure.map (Subtype.val : sphere (0 : E) 1 → E)
            (LogdetLean.uniformSphereSurfaceMeasure (E := E)) := by
      symm
      exact integral_map measurable_subtype_coe.aemeasurable
        hf.aestronglyMeasurable
    _ ≤ (3 / 4 : ℝ) ^ q := hdir

end ProjectionLaplace

end

end TomographyOracleCore
