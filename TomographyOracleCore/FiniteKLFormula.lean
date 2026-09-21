import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

/-!
# The KL divergence of a finite probability law

On a finite measurable space whose singletons are measurable, a strictly
positive reference probability gives positive mass to every atom.  The
Radon--Nikodym derivative is therefore the atomwise likelihood ratio, and
the integral definition of KL is the familiar finite sum.

The final theorem also records deterministic data processing in the same
explicit finite-sum form.  Finiteness of the raw KL is stated explicitly:
`ENNReal.toReal infinity = 0`, so no real-valued data-processing statement
can be true without this hypothesis.

No declaration in this file is an axiom.
-/

/-- A finite measure is absolutely continuous with respect to a measure
which gives strictly positive real mass to every atom. -/
theorem absolutelyContinuous_of_forall_pos_measureReal_singleton
    {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (mu nu : Measure Y) [IsFiniteMeasure mu]
    (hnu : ∀ y, 0 < nu.real {y}) :
    mu ≪ nu := by
  refine Measure.AbsolutelyContinuous.mk (fun s _hs hnus ↦ ?_)
  have hsempty : s = ∅ := by
    ext y
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hy
    have hsingleton : nu {y} = 0 :=
      measure_mono_null (Set.singleton_subset_iff.mpr hy) hnus
    have hsingletonReal : nu.real {y} = 0 := by
      simp [measureReal_def, hsingleton]
    exact (ne_of_gt (hnu y)) hsingletonReal
  simp [hsempty]

/-- On a finite atomic space with a positive reference atom, the real
Radon--Nikodym derivative is the ratio of the two atom masses. -/
theorem toReal_rnDeriv_eq_measureReal_singleton_div
    {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (mu nu : Measure Y) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (hnu : ∀ y, 0 < nu.real {y}) (y : Y) :
    (mu.rnDeriv nu y).toReal = mu.real {y} / nu.real {y} := by
  have hac : mu ≪ nu :=
    absolutelyContinuous_of_forall_pos_measureReal_singleton mu nu hnu
  have hmass : mu.rnDeriv nu y * nu {y} = mu {y} := by
    simpa only [lintegral_singleton] using
      (Measure.setLIntegral_rnDeriv' (μ := mu) (ν := nu) hac
        (measurableSet_singleton y))
  have hmassReal := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def] at hmassReal
  exact (eq_div_iff (ne_of_gt (hnu y))).2 hmassReal

/-- Exact finite-alphabet formula for the real value of KL divergence. -/
theorem toReal_klDiv_eq_sum_measureReal_mul_log_div
    {Y : Type*} [Fintype Y] [MeasurableSpace Y]
    [MeasurableSingletonClass Y]
    (mu nu : Measure Y) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (hnu : ∀ y, 0 < nu.real {y}) :
    (klDiv mu nu).toReal =
      ∑ y, mu.real {y} * Real.log (mu.real {y} / nu.real {y}) := by
  have hac : mu ≪ nu :=
    absolutelyContinuous_of_forall_pos_measureReal_singleton mu nu hnu
  have hint : Integrable (llr mu nu) mu := by
    simpa only [integrableOn_univ] using
      (IntegrableOn.of_finite (μ := mu) (f := llr mu nu)
        Set.finite_univ)
  rw [toReal_klDiv_of_measure_eq hac (by simp), integral_fintype hint]
  apply Finset.sum_congr rfl
  intro y _hy
  change mu.real {y} • Real.log (mu.rnDeriv nu y).toReal = _
  rw [toReal_rnDeriv_eq_measureReal_singleton_div mu nu hnu y]
  simp only [smul_eq_mul]

/-- Explicit finite decoded likelihood sums are bounded by the real raw KL
after any measurable deterministic decoder. -/
theorem sum_mapped_measureReal_mul_log_div_le_toReal_klDiv
    {X Y : Type*} [MeasurableSpace X]
    [Fintype Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
    (mu nu : Measure X) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu]
    (decode : X → Y) (hdecode : Measurable decode)
    (hnu : ∀ y, 0 < (nu.map decode).real {y})
    (hfinite : klDiv mu nu ≠ ∞) :
    ∑ y, (mu.map decode).real {y} *
        Real.log ((mu.map decode).real {y} /
          (nu.map decode).real {y}) ≤
      (klDiv mu nu).toReal := by
  letI : IsProbabilityMeasure (mu.map decode) :=
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  letI : IsProbabilityMeasure (nu.map decode) :=
    Measure.isProbabilityMeasure_map hdecode.aemeasurable
  rw [← toReal_klDiv_eq_sum_measureReal_mul_log_div
    (mu.map decode) (nu.map decode) hnu]
  exact ENNReal.toReal_mono hfinite (klDiv_map_le mu nu hdecode)

end TomographyOracleCore
