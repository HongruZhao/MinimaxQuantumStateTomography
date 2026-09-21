import TomographyOracleCore.Candidate2PhaseRandomization
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The probability law of the Candidate 2 quarter-phase lift

This file upgrades the finite algebra in `Candidate2PhaseRandomization` to an
actual probability law.  Starting from a probability measure `mu` on a
finite-dimensional complex Hilbert space, it takes the product with the
uniform law on `Fin 4` and pushes that product forward by

`(j, x) |-> quarterPhase j • x`.

The resulting law is measurable, centered whenever `id` is integrable,
preserves fixed norm and all `MemLp id p` assumptions, and has the exact
second- and sixth-marginal relations needed before applying a real covariance
estimate.  No covariance concentration statement is made here.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace ENNReal

namespace TomographyOracleCore.Candidate2PhaseRandomizedLaw

noncomputable section

set_option maxHeartbeats 1000000

open Candidate2PhaseRandomization

/-- The uniform probability measure on the four quarter phases. -/
def quarterPhaseMeasure : Measure (Fin 4) :=
  (PMF.uniformOfFintype (Fin 4)).toMeasure

instance instIsProbabilityMeasureQuarterPhaseMeasure :
    IsProbabilityMeasure quarterPhaseMeasure := by
  unfold quarterPhaseMeasure
  infer_instance

/-- Integration under the uniform `Fin 4` law is the arithmetic average. -/
theorem integral_quarterPhaseMeasure_eq_average
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : Fin 4 → F) :
    ∫ j, f j ∂quarterPhaseMeasure =
      ((4 : ℝ)⁻¹) • ∑ j, f j := by
  rw [quarterPhaseMeasure, PMF.integral_eq_sum]
  have hweight (j : Fin 4) :
      ((PMF.uniformOfFintype (Fin 4) j).toReal) = (4 : ℝ)⁻¹ := by
    rw [PMF.uniformOfFintype_apply]
    norm_num
  calc
    (∑ j : Fin 4, (PMF.uniformOfFintype (Fin 4) j).toReal • f j) =
        ∑ j : Fin 4, ((4 : ℝ)⁻¹) • f j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hweight j]
    _ = ((4 : ℝ)⁻¹) • ∑ j : Fin 4, f j :=
      Finset.smul_sum.symm

section HilbertSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : InnerProductSpace ℝ E :=
  InnerProductSpace.complexToReal

/-- The measurable map whose pushforward is the randomized law. -/
def phaseProductMap (z : Fin 4 × E) : E :=
  phaseVector z.1 z.2

theorem measurable_phaseProductMap :
    Measurable (phaseProductMap (E := E)) := by
  unfold phaseProductMap phaseVector
  exact ((measurable_of_finite quarterPhase).comp measurable_fst).smul
    measurable_snd

/-- The independent product of a uniform quarter phase and the original law. -/
def phaseProductMeasure (mu : Measure E) : Measure (Fin 4 × E) :=
  quarterPhaseMeasure.prod mu

instance instIsProbabilityMeasurePhaseProductMeasure
    (mu : Measure E) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (phaseProductMeasure mu) := by
  unfold phaseProductMeasure
  infer_instance

/-- The pushforward law of `(j, x) |-> quarterPhase j • x`. -/
def phaseRandomizedLaw (mu : Measure E) : Measure E :=
  (phaseProductMeasure mu).map (phaseProductMap (E := E))

instance instIsProbabilityMeasurePhaseRandomizedLaw
    (mu : Measure E) [IsProbabilityMeasure mu] :
    IsProbabilityMeasure (phaseRandomizedLaw mu) := by
  exact Measure.isProbabilityMeasure_map
    (measurable_phaseProductMap (E := E)).aemeasurable

/-- A reusable Fubini formula for the randomized law: first average over the
four phases, then integrate over the original law. -/
theorem integral_phaseRandomizedLaw_eq_integral_average
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (mu : Measure E) [SFinite mu] (g : E → F)
    (hg : Integrable g (phaseRandomizedLaw mu)) :
    ∫ y, g y ∂phaseRandomizedLaw mu =
      ∫ x, ((4 : ℝ)⁻¹) • ∑ j : Fin 4, g (phaseVector j x) ∂mu := by
  have hmap := measurable_phaseProductMap (E := E)
  have hcomp :
      Integrable (g ∘ phaseProductMap (E := E)) (phaseProductMeasure mu) :=
    (integrable_map_measure hg.aestronglyMeasurable hmap.aemeasurable).mp hg
  calc
    (∫ y, g y ∂phaseRandomizedLaw mu) =
        ∫ z, g (phaseProductMap z) ∂phaseProductMeasure mu := by
      exact integral_map hmap.aemeasurable hg.aestronglyMeasurable
    _ = ∫ x, ∫ j, g (phaseProductMap (j, x)) ∂quarterPhaseMeasure ∂mu := by
      simpa [phaseProductMeasure, Function.comp_def] using
        (integral_prod_symm
          (fun z : Fin 4 × E ↦ g (phaseProductMap z)) hcomp)
    _ = ∫ x, ((4 : ℝ)⁻¹) •
        ∑ j : Fin 4, g (phaseVector j x) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa [phaseProductMap] using
        (integral_quarterPhaseMeasure_eq_average
          (fun j : Fin 4 ↦ g (phaseVector j x)))

/-- Every `L^p` norm assumption on the original vector is inherited exactly
by the phase-randomized vector, because all four phases have norm one. -/
theorem memLp_id_phaseRandomizedLaw
    {mu : Measure E} [IsProbabilityMeasure mu] {p : ℝ≥0∞}
    (hmu : MemLp id p mu) :
    MemLp id p (phaseRandomizedLaw mu) := by
  have hsnd :
      MemLp (fun z : Fin 4 × E ↦ z.2) p (phaseProductMeasure mu) := by
    simpa [phaseProductMeasure] using hmu.comp_snd quarterPhaseMeasure
  have hphase :
      MemLp (phaseProductMap (E := E)) p (phaseProductMeasure mu) := by
    exact hsnd.congr_norm
      (measurable_phaseProductMap (E := E)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ by
        simpa [phaseProductMap] using (norm_phaseVector z.1 z.2).symm)
  rw [phaseRandomizedLaw,
    memLp_map_measure_iff aestronglyMeasurable_id
      (measurable_phaseProductMap (E := E)).aemeasurable]
  simpa [Function.comp_def] using hphase

/-- Integrability of the identity is preserved by quarter-phase
randomization. -/
theorem integrable_id_phaseRandomizedLaw
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu : Integrable id mu) :
    Integrable id (phaseRandomizedLaw mu) := by
  rw [← memLp_one_iff_integrable] at hmu ⊢
  exact memLp_id_phaseRandomizedLaw hmu

/-- The randomized law has mean zero. -/
theorem integral_id_phaseRandomizedLaw_eq_zero
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu : Integrable id mu) :
    ∫ y, y ∂phaseRandomizedLaw mu = 0 := by
  have hnu := integrable_id_phaseRandomizedLaw hmu
  calc
    (∫ y, y ∂phaseRandomizedLaw mu) =
        ∫ x, ((4 : ℝ)⁻¹) • ∑ j : Fin 4, phaseVector j x ∂mu := by
      simpa only [id_eq] using
        (integral_phaseRandomizedLaw_eq_integral_average mu id hnu)
    _ = 0 := by simp [sum_phaseVector]

/-- An almost-sure fixed norm is inherited by the randomized law. -/
theorem ae_fixedNorm_phaseRandomizedLaw
    {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}
    (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    ∀ᵐ y ∂phaseRandomizedLaw mu, ‖y‖ ^ 2 = q := by
  rw [phaseRandomizedLaw]
  have hset : MeasurableSet {y : E | ‖y‖ ^ 2 = q} :=
    measurableSet_eq.preimage (measurable_norm.pow_const 2)
  apply (ae_map_iff
    (measurable_phaseProductMap (E := E)).aemeasurable hset).2
  change ∀ᵐ z ∂phaseProductMeasure mu,
    phaseProductMap z ∈ {y : E | ‖y‖ ^ 2 = q}
  rw [phaseProductMeasure, Measure.ae_prod_iff_ae_ae
    (hset.preimage (measurable_phaseProductMap (E := E)))]
  filter_upwards [] with j
  filter_upwards [hnorm] with x hx
  simpa [phaseProductMap] using hx

/-- Exact second real marginal identity under the randomized law. -/
theorem integral_real_inner_sq_phaseRandomizedLaw
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu : MemLp id 2 mu) (u : E) :
    (∫ y, ⟪y, u⟫_ℝ ^ 2 ∂phaseRandomizedLaw mu) =
      ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu := by
  have hnu : MemLp id 2 (phaseRandomizedLaw mu) :=
    memLp_id_phaseRandomizedLaw hmu
  have hreal :
      Integrable (fun y ↦ ⟪y, u⟫_ℝ ^ 2) (phaseRandomizedLaw mu) := by
    simpa only [id_eq] using (hnu.inner_const u).integrable_sq
  calc
    (∫ y, ⟪y, u⟫_ℝ ^ 2 ∂phaseRandomizedLaw mu) =
        ∫ x, ((4 : ℝ)⁻¹) *
          ∑ j : Fin 4, ⟪phaseVector j x, u⟫_ℝ ^ 2 ∂mu := by
      simpa only [smul_eq_mul] using
        (integral_phaseRandomizedLaw_eq_integral_average mu
          (fun y ↦ ⟪y, u⟫_ℝ ^ 2) hreal)
    _ = ∫ x, ((2 : ℝ)⁻¹) * ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [sum_real_inner_phaseVector_sq]
      ring
    _ = ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu := by
      rw [integral_const_mul]

/-- The sixth real marginal moment is at most one half of the sixth complex
marginal moment. -/
theorem integral_abs_real_inner_sixth_phaseRandomizedLaw_le
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu : MemLp id 6 mu) (u : E) :
    (∫ y, |⟪y, u⟫_ℝ| ^ 6 ∂phaseRandomizedLaw mu) ≤
      ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu := by
  have hnu : MemLp id 6 (phaseRandomizedLaw mu) :=
    memLp_id_phaseRandomizedLaw hmu
  have hrealLp :
      MemLp (fun y : E ↦ ⟪y, u⟫_ℝ) 6 (phaseRandomizedLaw mu) := by
    simpa only [id_eq] using (hnu.inner_const u)
  have hreal :
      Integrable (fun y ↦ |⟪y, u⟫_ℝ| ^ 6) (phaseRandomizedLaw mu) := by
    simpa only [id_eq, Real.norm_eq_abs] using
      hrealLp.integrable_norm_pow (by norm_num : 6 ≠ 0)
  have hcomplexLp :
      MemLp (fun x : E ↦ ⟪x, u⟫_ℂ) 6 mu := by
    simpa only [id_eq] using (hmu.inner_const u)
  have hcomplex :
      Integrable (fun x ↦ ‖⟪x, u⟫_ℂ‖ ^ 6) mu := by
    simpa only [id_eq] using
      hcomplexLp.integrable_norm_pow (by norm_num : 6 ≠ 0)
  have haverage_nonneg :
      0 ≤ᵐ[mu] fun x ↦ ((4 : ℝ)⁻¹) *
        ∑ j : Fin 4, |⟪phaseVector j x, u⟫_ℝ| ^ 6 := by
    filter_upwards [] with x
    positivity
  have hpoint : ∀ᵐ x ∂mu,
      ((4 : ℝ)⁻¹) *
          ∑ j : Fin 4, |⟪phaseVector j x, u⟫_ℝ| ^ 6 ≤
        ((2 : ℝ)⁻¹) * ‖⟪x, u⟫_ℂ‖ ^ 6 := by
    filter_upwards [] with x
    calc
      ((4 : ℝ)⁻¹) *
          ∑ j : Fin 4, |⟪phaseVector j x, u⟫_ℝ| ^ 6 ≤
          ((4 : ℝ)⁻¹) * (2 * ‖⟪x, u⟫_ℂ‖ ^ 6) := by
        exact mul_le_mul_of_nonneg_left
          (sum_real_inner_phaseVector_sixth_le x u) (by norm_num)
      _ = ((2 : ℝ)⁻¹) * ‖⟪x, u⟫_ℂ‖ ^ 6 := by ring
  calc
    (∫ y, |⟪y, u⟫_ℝ| ^ 6 ∂phaseRandomizedLaw mu) =
        ∫ x, ((4 : ℝ)⁻¹) *
          ∑ j : Fin 4, |⟪phaseVector j x, u⟫_ℝ| ^ 6 ∂mu := by
      simpa only [smul_eq_mul] using
        (integral_phaseRandomizedLaw_eq_integral_average mu
          (fun y ↦ |⟪y, u⟫_ℝ| ^ 6) hreal)
    _ ≤ ∫ x, ((2 : ℝ)⁻¹) * ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu := by
      exact integral_mono_of_nonneg haverage_nonneg
        (hcomplex.const_mul ((2 : ℝ)⁻¹)) hpoint
    _ = ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu := by
      rw [integral_const_mul]

/-- Quarter-phase averaging of the covariance integrand, in application
form. -/
theorem average_covarianceIntegrand_phaseVector (x u : E) :
    ((4 : ℝ)⁻¹) •
        ∑ j : Fin 4, ⟪u, phaseVector j x⟫_ℝ • phaseVector j x =
      ((2 : ℝ)⁻¹) • (⟪x, u⟫_ℂ • x) := by
  calc
    ((4 : ℝ)⁻¹) •
        ∑ j : Fin 4, ⟪u, phaseVector j x⟫_ℝ • phaseVector j x =
        ((4 : ℝ)⁻¹) •
          (∑ j : Fin 4,
            PeriodicForwardCovariance.rankOneCovariance (phaseVector j x)) u := by
      congr 1
      rw [ContinuousLinearMap.sum_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [PeriodicForwardCovariance.rankOneCovariance_apply,
        real_inner_comm]
    _ = ((2 : ℝ)⁻¹) • (⟪x, u⟫_ℂ • x) :=
      average_rankOneCovariance_phaseVector_apply x u

/-- Application identity for the real population covariance of the
randomized law.  The right side is one half of the original complex rank-one
second-moment integral. -/
theorem populationCovariance_phaseRandomizedLaw_apply
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu : MemLp id 2 mu) (u : E) :
    PeriodicForwardCovariance.populationCovariance
        (phaseRandomizedLaw mu) u =
      ((2 : ℝ)⁻¹) • ∫ x, ⟪x, u⟫_ℂ • x ∂mu := by
  have hnu : MemLp id 2 (phaseRandomizedLaw mu) :=
    memLp_id_phaseRandomizedLaw hmu
  have hscalar :
      MemLp (fun y : E ↦ ⟪u, y⟫_ℝ) 2 (phaseRandomizedLaw mu) := by
    simpa only [id_eq] using (hnu.const_inner u)
  have hcovarianceIntegrand :
      Integrable (fun y ↦ ⟪u, y⟫_ℝ • y) (phaseRandomizedLaw mu) := by
    have hproduct :
        MemLp (fun y : E ↦ ⟪u, y⟫_ℝ • y) 1
          (phaseRandomizedLaw mu) := by
      simpa only [id_eq, Pi.smul_def'] using hnu.smul hscalar
    exact memLp_one_iff_integrable.mp hproduct
  calc
    PeriodicForwardCovariance.populationCovariance
        (phaseRandomizedLaw mu) u =
        ∫ y, ⟪u, y⟫_ℝ • y ∂phaseRandomizedLaw mu := by
      exact covarianceOperator_apply hnu u
    _ = ∫ x, ((4 : ℝ)⁻¹) •
        ∑ j : Fin 4,
          ⟪u, phaseVector j x⟫_ℝ • phaseVector j x ∂mu := by
      simpa using
        (integral_phaseRandomizedLaw_eq_integral_average mu
          (fun y ↦ ⟪u, y⟫_ℝ • y) hcovarianceIntegrand)
    _ = ∫ x, ((2 : ℝ)⁻¹) • (⟪x, u⟫_ℂ • x) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact average_covarianceIntegrand_phaseVector x u
    _ = ((2 : ℝ)⁻¹) • ∫ x, ⟪x, u⟫_ℂ • x ∂mu := by
      rw [integral_smul]

end HilbertSpace

end

end TomographyOracleCore.Candidate2PhaseRandomizedLaw
