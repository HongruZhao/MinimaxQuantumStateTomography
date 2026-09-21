import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic

/-!
# The direction of a standard Gaussian is surface-uniform

This module supplies the polar-measure bridge needed for the matrix-spherical
corollary.  It identifies the normalized direction of a finite-dimensional
standard Gaussian with normalized Haar surface measure on the unit sphere.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A measure-preserving map continues to preserve measure after both sides
are tilted by the same measurable density. -/
theorem measurePreserving_map_withDensity_comp
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {mu : Measure X} {nu : Measure Y} {e : X → Y}
    (he : MeasurePreserving e mu nu) (f : Y → ℝ≥0∞) (hf : Measurable f) :
    Measure.map e (mu.withDensity (f ∘ e)) = nu.withDensity f := by
  apply Measure.ext_of_lintegral
  intro g hg
  rw [lintegral_map' hg.aemeasurable he.measurable.aemeasurable]
  change (∫⁻ x, (g ∘ e) x ∂mu.withDensity (f ∘ e)) =
    ∫⁻ y, g y ∂nu.withDensity f
  rw [lintegral_withDensity_eq_lintegral_mul _ (hf.comp he.measurable)
      (hg.comp he.measurable),
    lintegral_withDensity_eq_lintegral_mul _ hf hg]
  simpa only [Function.comp_apply, Pi.mul_apply] using
    he.lintegral_comp (hf.fun_mul hg)

/-- The usual standard-Gaussian density, written in radial form. -/
def standardGaussianRadialDensity (x : E) : ℝ :=
  Real.exp (-‖x‖ ^ 2 / 2) /
    (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2)

omit [FiniteDimensional ℝ E] in
theorem measurable_standardGaussianRadialDensity :
    Measurable (standardGaussianRadialDensity : E → ℝ) := by
  unfold standardGaussianRadialDensity
  fun_prop

private theorem integrable_standardGaussianRadialDensity_real :
    Integrable (standardGaussianRadialDensity : E → ℝ) := by
  unfold standardGaussianRadialDensity
  have hcomplex := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (1 / 2 : ℂ)) (c := 0) (w := (0 : E)) (by norm_num)
  have hreal : Integrable (fun x : E ↦ Real.exp (-‖x‖ ^ 2 / 2)) := by
    apply hcomplex.norm.congr
    filter_upwards [] with x
    simp [Complex.norm_exp, div_eq_mul_inv]
    norm_cast
    ring
  exact hreal.div_const _

private instance isFiniteMeasure_radialStandardGaussian :
    IsFiniteMeasure
      (volume.withDensity fun x : E ↦ ENNReal.ofReal (standardGaussianRadialDensity x)) :=
  isFiniteMeasure_withDensity_ofReal
    integrable_standardGaussianRadialDensity_real.hasFiniteIntegral

theorem radialStandardGaussian_eq_stdGaussian :
    volume.withDensity (fun x : E ↦ ENNReal.ofReal (standardGaussianRadialDensity x)) =
      stdGaussian E := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply, integral_withDensity_eq_integral_toReal_smul
    measurable_standardGaussianRadialDensity.ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  have hdens_nonneg (x : E) : 0 ≤ standardGaussianRadialDensity x := by
    unfold standardGaussianRadialDensity
    positivity
  simp_rw [ENNReal.toReal_ofReal (hdens_nonneg _)]
  rw [charFun_stdGaussian]
  unfold standardGaussianRadialDensity
  simp only [Complex.real_smul]
  simp_rw [Complex.ofReal_div, div_mul_eq_mul_div]
  rw [integral_div]
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (V := E) (b := (1 / 2 : ℂ)) (c := Complex.I) (w := t) (by norm_num)
  have hint :
      (∫ x : E, (Real.exp (-‖x‖ ^ 2 / 2) : ℂ) *
          Complex.exp (⟪x, t⟫ * Complex.I)) =
        ∫ x : E, Complex.exp (-(1 / 2 : ℂ) * ‖x‖ ^ 2 +
          Complex.I * ⟪t, x⟫) := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    simp only [Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_pow, Complex.ofReal_ofNat]
    congr 1
    rw [real_inner_comm]
    ring
  rw [hint, h]
  have hbase :
      (Real.pi : ℂ) / (1 / 2) = ((2 * Real.pi : ℝ) : ℂ) := by
    norm_num
    ring
  rw [hbase]
  have hpow :
      ((2 * Real.pi : ℝ) : ℂ) ^
          ((Module.finrank ℝ E : ℂ) / 2) =
        (((2 * Real.pi : ℝ) ^
          ((Module.finrank ℝ E : ℝ) / 2) : ℝ) : ℂ) := by
    symm
    convert Complex.ofReal_cpow (show 0 ≤ (2 * Real.pi : ℝ) by positivity)
      ((Module.finrank ℝ E : ℝ) / 2) using 1
    all_goals norm_num
  rw [hpow]
  have hnormalizer :
      ((2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2) : ℝ) ≠ 0 := by
    positivity
  field_simp [hnormalizer]
  congr 1
  rw [Complex.I_sq]
  ring

/-! ## Polar factorization and the uniform direction -/

/-- Totalized unit direction.  The value at zero is irrelevant for Gaussian
measure, but makes this an everywhere-defined measurable map. -/
def unitDirection (x : E) : E :=
  by
    classical
    exact if x = 0 then 0 else ‖x‖⁻¹ • x

theorem measurable_unitDirection : Measurable (unitDirection : E → E) := by
  classical
  unfold unitDirection
  apply Measurable.ite
  · exact measurable_id (measurableSet_singleton 0)
  · exact measurable_const
  · exact measurable_id.norm.inv.smul measurable_id

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem unitDirection_subtype_nonzero (x : ({0}ᶜ : Set E)) :
    unitDirection (x : E) =
      ((homeomorphUnitSphereProd E x).1 : E) := by
  classical
  unfold unitDirection
  have hx : (x : E) ≠ 0 := by
    intro h
    exact x.2 (by simp [h])
  rw [if_neg hx, homeomorphUnitSphereProd_apply_fst_coe]

/-- The one-dimensional radial density appearing after polar coordinates. -/
def standardGaussianRayDensity (r : Ioi (0 : ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal
    (Real.exp (-r.1 ^ 2 / 2) /
      (2 * Real.pi) ^ ((Module.finrank ℝ E : ℝ) / 2))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem measurable_standardGaussianRayDensity :
    Measurable (standardGaussianRayDensity (E := E)) := by
  unfold standardGaussianRayDensity
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem standardGaussian_density_polar (x : ({0}ᶜ : Set E)) :
    ENNReal.ofReal (standardGaussianRadialDensity (x : E)) =
      standardGaussianRayDensity (E := E) (homeomorphUnitSphereProd E x).2 := by
  unfold standardGaussianRadialDensity standardGaussianRayDensity
  congr 2
  rw [homeomorphUnitSphereProd_apply_snd_coe]

/-- The exact polar product decomposition of the radial standard-Gaussian
density on the punctured space. -/
theorem map_polar_radialStandardGaussian [Nontrivial E] :
    Measure.map (homeomorphUnitSphereProd E)
        ((volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)).withDensity
          (fun x ↦ ENNReal.ofReal (standardGaussianRadialDensity (x : E)))) =
      (volume.toSphere).prod
        ((Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
          (standardGaussianRayDensity (E := E))) := by
  have hpolar :=
    (volume : Measure E).measurePreserving_homeomorphUnitSphereProd
  have htilt := measurePreserving_map_withDensity_comp hpolar
    (fun z : sphere (0 : E) 1 × Ioi (0 : ℝ) ↦
      standardGaussianRayDensity (E := E) z.2)
    (measurable_standardGaussianRayDensity.comp measurable_snd)
  rw [prod_withDensity_right measurable_standardGaussianRayDensity]
  rw [← htilt]
  congr 2
  funext x
  exact standardGaussian_density_polar x

/-- The punctured radial-density construction is exactly the standard
Gaussian after reinserting it into the ambient space. -/
theorem map_subtype_puncturedRadialStandardGaussian [Nontrivial E] :
    Measure.map (Subtype.val : ({0}ᶜ : Set E) → E)
        ((volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)).withDensity
          (fun x ↦ ENNReal.ofReal (standardGaussianRadialDensity (x : E)))) =
      stdGaussian E := by
  have hsub : MeasurePreserving (Subtype.val : ({0}ᶜ : Set E) → E)
      (volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)) volume := by
    refine ⟨measurable_subtype_coe, ?_⟩
    rw [map_comap_subtype_coe (measurableSet_singleton (0 : E)).compl,
      restrict_compl_singleton]
  have htilt := measurePreserving_map_withDensity_comp hsub
    (fun x : E ↦ ENNReal.ofReal (standardGaussianRadialDensity x))
    measurable_standardGaussianRadialDensity.ennreal_ofReal
  change Measure.map (Subtype.val : ({0}ᶜ : Set E) → E)
      ((volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)).withDensity
        ((fun x : E ↦ ENNReal.ofReal (standardGaussianRadialDensity x)) ∘
          Subtype.val)) = stdGaussian E
  rw [htilt, radialStandardGaussian_eq_stdGaussian]

/-- Surface-uniform probability measure on the unit sphere, defined by
normalizing Mathlib's Haar surface measure. -/
def uniformSphereSurfaceMeasure [Nontrivial E] : Measure (sphere (0 : E) 1) :=
  ((volume.toSphere : Measure (sphere (0 : E) 1)) univ)⁻¹ • volume.toSphere

instance uniformSphereSurfaceMeasure_isProbability [Nontrivial E] :
    IsProbabilityMeasure (uniformSphereSurfaceMeasure (E := E)) := by
  refine ⟨?_⟩
  unfold uniformSphereSurfaceMeasure
  rw [Measure.smul_apply]
  change ((volume.toSphere : Measure (sphere (0 : E) 1)) univ)⁻¹ *
      volume.toSphere univ = 1
  exact ENNReal.inv_mul_cancel
    (Measure.measure_univ_ne_zero.mpr
      (Measure.toSphere_ne_zero (volume : Measure E)))
    (measure_ne_top _ _)

/-- A normalized finite-dimensional standard Gaussian has exactly the
normalized Haar surface law on the unit sphere. -/
theorem map_unitDirection_stdGaussian_eq_uniformSphereSurfaceMeasure
    [Nontrivial E] :
    Measure.map unitDirection (stdGaussian E) =
      Measure.map (Subtype.val : sphere (0 : E) 1 → E)
        (uniformSphereSurfaceMeasure (E := E)) := by
  let nu : Measure ({0}ᶜ : Set E) :=
    (volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)).withDensity
      (fun x ↦ ENNReal.ofReal (standardGaussianRadialDensity (x : E)))
  let ray : Measure (Ioi (0 : ℝ)) :=
    (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
      (standardGaussianRayDensity (E := E))
  have hsub : Measure.map (Subtype.val : ({0}ᶜ : Set E) → E) nu =
      stdGaussian E := by
    simpa only [nu] using
      (map_subtype_puncturedRadialStandardGaussian (E := E))
  have hpolar : Measure.map (homeomorphUnitSphereProd E) nu =
      (volume.toSphere).prod ray := by
    simpa only [nu, ray] using (map_polar_radialStandardGaussian (E := E))
  have hnu_mass : nu univ = 1 := by
    have h := congrArg (fun mu : Measure E ↦ mu univ) hsub
    rw [Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable
      MeasurableSet.univ] at h
    simpa using h
  have hprod_mass :
      (volume.toSphere : Measure (sphere (0 : E) 1)) univ * ray univ = 1 := by
    calc
      (volume.toSphere : Measure (sphere (0 : E) 1)) univ * ray univ =
          ((volume.toSphere : Measure (sphere (0 : E) 1)).prod ray) univ := by
            rw [← univ_prod_univ, Measure.prod_prod]
      _ = (Measure.map (homeomorphUnitSphereProd E) nu) univ := by rw [hpolar]
      _ = nu univ := by
        rw [Measure.map_apply_of_aemeasurable
          (homeomorphUnitSphereProd E).measurable.aemeasurable MeasurableSet.univ]
        simp
      _ = 1 := hnu_mass
  have hray : ray univ =
      ((volume.toSphere : Measure (sphere (0 : E) 1)) univ)⁻¹ := by
    exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hprod_mass)
  calc
    Measure.map unitDirection (stdGaussian E) =
        Measure.map unitDirection
          (Measure.map (Subtype.val : ({0}ᶜ : Set E) → E) nu) := by rw [hsub]
    _ = Measure.map (unitDirection ∘
          (Subtype.val : ({0}ᶜ : Set E) → E)) nu := by
        rw [Measure.map_map measurable_unitDirection measurable_subtype_coe]
    _ = Measure.map ((Subtype.val : sphere (0 : E) 1 → E) ∘
          Prod.fst ∘ (homeomorphUnitSphereProd E)) nu := by
        apply Measure.map_congr
        filter_upwards [] with x
        exact unitDirection_subtype_nonzero x
    _ = Measure.map (Subtype.val : sphere (0 : E) 1 → E)
          (Measure.map Prod.fst
            (Measure.map (homeomorphUnitSphereProd E) nu)) := by
        symm
        calc
          Measure.map (Subtype.val : sphere (0 : E) 1 → E)
              (Measure.map Prod.fst
                (Measure.map (homeomorphUnitSphereProd E) nu)) =
              Measure.map (Subtype.val : sphere (0 : E) 1 → E)
                (Measure.map (Prod.fst ∘ homeomorphUnitSphereProd E) nu) := by
                  congr 1
                  rw [Measure.map_map measurable_fst
                    (homeomorphUnitSphereProd E).measurable]
          _ = Measure.map ((Subtype.val : sphere (0 : E) 1 → E) ∘
                Prod.fst ∘ homeomorphUnitSphereProd E) nu := by
                  rw [Measure.map_map measurable_subtype_coe
                    (measurable_fst.comp (homeomorphUnitSphereProd E).measurable)]
    _ = Measure.map (Subtype.val : sphere (0 : E) 1 → E)
          (Measure.map Prod.fst ((volume.toSphere).prod ray)) := by rw [hpolar]
    _ = Measure.map (Subtype.val : sphere (0 : E) 1 → E)
          ((ray univ) • volume.toSphere) := by rw [Measure.map_fst_prod]
    _ = Measure.map (Subtype.val : sphere (0 : E) 1 → E)
          (uniformSphereSurfaceMeasure (E := E)) := by
        unfold uniformSphereSurfaceMeasure
        rw [hray]

end

end LogdetLean
