import TomographyOracleCore.PortedGaussianSphereDirection
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# Independence of Gaussian radial energy and direction

This module upgrades the already-ported Gaussian polar decomposition to an
exact independence theorem.  It is deliberately generic in the ambient
finite-dimensional real Hilbert space so the complex tail block used by the
one-copy POVM calculation can instantiate it after a real-linear isometry.

The proof identifies the joint pushforward with the product of its two
marginal pushforwards.  No distributional fact is postulated.
-/

namespace TomographyOracleCore

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Totalized Gaussian polar coordinates: unit direction and norm. -/
def gaussianNormDirection (x : E) : E × ℝ :=
  (LogdetLean.unitDirection x, ‖x‖)

theorem measurable_gaussianNormDirection :
    Measurable (gaussianNormDirection : E → E × ℝ) := by
  exact LogdetLean.measurable_unitDirection.prodMk measurable_id.norm

/-- Exact joint product law for the direction and norm of a standard
finite-dimensional Gaussian. -/
theorem map_gaussianNormDirection_stdGaussian_eq_prod [Nontrivial E] :
    Measure.map (gaussianNormDirection : E → E × ℝ) (stdGaussian E) =
      (Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
        (Measure.map norm (stdGaussian E)) := by
  let nu : Measure ({0}ᶜ : Set E) :=
    (volume.comap (Subtype.val : ({0}ᶜ : Set E) → E)).withDensity
      (fun x ↦ ENNReal.ofReal (LogdetLean.standardGaussianRadialDensity (x : E)))
  let ray : Measure (Ioi (0 : ℝ)) :=
    (Measure.volumeIoiPow (Module.finrank ℝ E - 1)).withDensity
      (LogdetLean.standardGaussianRayDensity (E := E))
  let sphereVolume : Measure (sphere (0 : E) 1) := volume.toSphere
  let sphereVal : sphere (0 : E) 1 → E := Subtype.val
  let rayVal : Ioi (0 : ℝ) → ℝ := Subtype.val
  have hsub : Measure.map (Subtype.val : ({0}ᶜ : Set E) → E) nu =
      stdGaussian E := by
    simpa only [nu] using
      (LogdetLean.map_subtype_puncturedRadialStandardGaussian (E := E))
  have hpolar :
      Measure.map (homeomorphUnitSphereProd E) nu =
        sphereVolume.prod ray := by
    simpa only [nu, ray, sphereVolume] using
      (LogdetLean.map_polar_radialStandardGaussian (E := E))
  have hnu_mass : nu univ = 1 := by
    have h := congrArg (fun mu : Measure E ↦ mu univ) hsub
    rw [Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable
      MeasurableSet.univ] at h
    simpa using h
  have hmass : sphereVolume univ * ray univ = 1 := by
    calc
      sphereVolume univ * ray univ = (sphereVolume.prod ray) univ := by
        rw [← univ_prod_univ, Measure.prod_prod]
      _ = (Measure.map (homeomorphUnitSphereProd E) nu) univ := by rw [hpolar]
      _ = nu univ := by
        rw [Measure.map_apply_of_aemeasurable
          (homeomorphUnitSphereProd E).measurable.aemeasurable MeasurableSet.univ]
        simp
      _ = 1 := hnu_mass
  have hjoint :
      Measure.map (gaussianNormDirection : E → E × ℝ) (stdGaussian E) =
        (Measure.map sphereVal sphereVolume).prod (Measure.map rayVal ray) := by
    calc
      Measure.map (gaussianNormDirection : E → E × ℝ) (stdGaussian E) =
          Measure.map (gaussianNormDirection : E → E × ℝ)
            (Measure.map (Subtype.val : ({0}ᶜ : Set E) → E) nu) := by rw [hsub]
      _ = Measure.map
          ((Prod.map sphereVal rayVal) ∘ homeomorphUnitSphereProd E) nu := by
        rw [Measure.map_map measurable_gaussianNormDirection measurable_subtype_coe]
        apply Measure.map_congr
        filter_upwards [] with x
        apply Prod.ext
        · exact LogdetLean.unitDirection_subtype_nonzero x
        · change ‖(x : E)‖ = (((homeomorphUnitSphereProd E) x).2 : ℝ)
          exact (homeomorphUnitSphereProd_apply_snd_coe E x).symm
      _ = Measure.map (Prod.map sphereVal rayVal)
          (Measure.map (homeomorphUnitSphereProd E) nu) := by
        rw [Measure.map_map
          (measurable_subtype_coe.prodMap measurable_subtype_coe)
          (homeomorphUnitSphereProd E).measurable]
      _ = Measure.map (Prod.map sphereVal rayVal) (sphereVolume.prod ray) := by
        rw [hpolar]
      _ = (Measure.map sphereVal sphereVolume).prod (Measure.map rayVal ray) := by
        exact (Measure.map_prod_map sphereVolume ray
          measurable_subtype_coe measurable_subtype_coe).symm
  have hdir :
      Measure.map LogdetLean.unitDirection (stdGaussian E) =
        (ray univ) • Measure.map sphereVal sphereVolume := by
    have hray_mass : (Measure.map rayVal ray) univ = ray univ := by
      rw [Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable
        MeasurableSet.univ]
      simp
    calc
      Measure.map LogdetLean.unitDirection (stdGaussian E) =
          Measure.map (Prod.fst ∘ (gaussianNormDirection : E → E × ℝ))
            (stdGaussian E) := by rfl
      _ = Measure.map Prod.fst
            (Measure.map (gaussianNormDirection : E → E × ℝ)
              (stdGaussian E)) := by
        rw [Measure.map_map measurable_fst measurable_gaussianNormDirection]
      _ = Measure.map Prod.fst
          ((Measure.map sphereVal sphereVolume).prod (Measure.map rayVal ray)) := by
        rw [hjoint]
      _ = ((Measure.map rayVal ray) univ) • Measure.map sphereVal sphereVolume := by
        rw [Measure.map_fst_prod]
      _ = (ray univ) • Measure.map sphereVal sphereVolume := by
        rw [hray_mass]
  have hnorm :
      Measure.map norm (stdGaussian E) =
        (sphereVolume univ) • Measure.map rayVal ray := by
    have hsphere_mass :
        (Measure.map sphereVal sphereVolume) univ = sphereVolume univ := by
      rw [Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable
        MeasurableSet.univ]
      simp
    calc
      Measure.map norm (stdGaussian E) =
          Measure.map (Prod.snd ∘ (gaussianNormDirection : E → E × ℝ))
            (stdGaussian E) := by rfl
      _ = Measure.map Prod.snd
            (Measure.map (gaussianNormDirection : E → E × ℝ)
              (stdGaussian E)) := by
        rw [Measure.map_map measurable_snd measurable_gaussianNormDirection]
      _ = Measure.map Prod.snd
          ((Measure.map sphereVal sphereVolume).prod (Measure.map rayVal ray)) := by
        rw [hjoint]
      _ = ((Measure.map sphereVal sphereVolume) univ) • Measure.map rayVal ray := by
        rw [Measure.map_snd_prod]
      _ = (sphereVolume univ) • Measure.map rayVal ray := by
        rw [hsphere_mass]
  rw [hjoint, hdir, hnorm, Measure.prod_smul_left,
    Measure.prod_smul_right, smul_smul]
  have hrs : ray univ * sphereVolume univ = 1 := by
    simpa [mul_comm] using hmass
  rw [hrs, one_smul]

/-- Exact product law for direction and squared radial energy. -/
theorem map_gaussianDirectionEnergy_stdGaussian_eq_prod [Nontrivial E] :
    Measure.map
        (fun x : E ↦ (LogdetLean.unitDirection x, ‖x‖ ^ 2))
        (stdGaussian E) =
      (Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
        (Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E)) := by
  let sq : ℝ → ℝ := fun r ↦ r ^ 2
  let liftSq : E × ℝ → E × ℝ := Prod.map id sq
  have hlift : Measurable liftSq := by
    exact measurable_id.prodMap (by fun_prop)
  calc
    Measure.map
        (fun x : E ↦ (LogdetLean.unitDirection x, ‖x‖ ^ 2))
        (stdGaussian E) =
        Measure.map liftSq
          (Measure.map (gaussianNormDirection : E → E × ℝ)
            (stdGaussian E)) := by
      rw [Measure.map_map hlift measurable_gaussianNormDirection]
      congr 1
    _ = Measure.map liftSq
        ((Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
          (Measure.map norm (stdGaussian E))) := by
      rw [map_gaussianNormDirection_stdGaussian_eq_prod]
    _ = (Measure.map id (Measure.map LogdetLean.unitDirection (stdGaussian E))).prod
        (Measure.map sq (Measure.map norm (stdGaussian E))) := by
      exact (Measure.map_prod_map _ _ measurable_id (by fun_prop)).symm
    _ = (Measure.map LogdetLean.unitDirection (stdGaussian E)).prod
        (Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E)) := by
      have hsquare :
          Measure.map sq (Measure.map norm (stdGaussian E)) =
            Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E) := by
        calc
          Measure.map sq (Measure.map norm (stdGaussian E)) =
              Measure.map (sq ∘ (fun x : E ↦ ‖x‖)) (stdGaussian E) :=
                Measure.map_map (by fun_prop) measurable_id.norm
          _ = Measure.map (fun x : E ↦ ‖x‖ ^ 2) (stdGaussian E) := by rfl
      rw [Measure.map_id, hsquare]

/-- A standard Gaussian's unit direction and squared norm are independent. -/
theorem indepFun_unitDirection_normSq_stdGaussian [Nontrivial E] :
    IndepFun LogdetLean.unitDirection (fun x : E ↦ ‖x‖ ^ 2)
      (stdGaussian E) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    LogdetLean.measurable_unitDirection.aemeasurable
    (measurable_id.norm.pow_const 2).aemeasurable).2
  exact map_gaussianDirectionEnergy_stdGaussian_eq_prod (E := E)

/-- The orientation needed by tail-factorization arguments: squared norm is
independent of unit direction. -/
theorem indepFun_normSq_unitDirection_stdGaussian [Nontrivial E] :
    IndepFun (fun x : E ↦ ‖x‖ ^ 2) LogdetLean.unitDirection
      (stdGaussian E) :=
  (indepFun_unitDirection_normSq_stdGaussian (E := E)).symm

end

end TomographyOracleCore
