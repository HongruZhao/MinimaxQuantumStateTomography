import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace TomographyOracleCore

open MeasureTheory InformationTheory

/-!
# KL divergence is bounded by Pearson chi-square divergence

This module records the scalar inequality and its measure-theoretic
consequence in the exact Radon--Nikodym form needed by the physical
tomography lower bound.  It introduces no statistical premise: the only
hypotheses are absolute continuity and the integrability needed to interpret
the finite real-valued divergences.
-/

/-- Pearson's chi-square functional, written directly through the real
Radon--Nikodym derivative. -/
noncomputable def pearsonChiSquare
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) : ℝ :=
  ∫ z, ((μ.rnDeriv ν z).toReal - 1) ^ 2 ∂ν

/-- The pointwise convex integrand of KL is bounded by the squared Pearson
integrand on the nonnegative half-line. -/
theorem klFun_le_sq_sub_one {x : ℝ} (hx : 0 ≤ x) :
    klFun x ≤ (x - 1) ^ 2 := by
  rcases hx.eq_or_lt with rfl | hxpos
  · simp [klFun]
  have hlog : Real.log x ≤ x - 1 :=
    Real.log_le_sub_one_of_pos hxpos
  have hmul : x * Real.log x ≤ x * (x - 1) :=
    mul_le_mul_of_nonneg_left hlog hx
  rw [klFun]
  nlinarith

/-- For finite measures, finite KL is at most Pearson chi-square.  The
integrability assumptions are analytic facts, not conclusions about the
tomography model; later modules discharge them from the strictly positive
reference Born density and the Haar second-moment estimate. -/
theorem toReal_klDiv_le_pearsonChiSquare
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν)
    (hllr : Integrable (llr μ ν) μ)
    (hpearson : Integrable
      (fun z ↦ ((μ.rnDeriv ν z).toReal - 1) ^ 2) ν) :
    (klDiv μ ν).toReal ≤ pearsonChiSquare μ ν := by
  rw [toReal_klDiv_eq_integral_klFun hμν]
  unfold pearsonChiSquare
  apply integral_mono_ae
  · exact (integrable_klFun_rnDeriv_iff hμν).2 hllr
  · exact hpearson
  · filter_upwards with z
    exact klFun_le_sq_sub_one ENNReal.toReal_nonneg

/-- The same hypotheses certify that the KL divergence is genuinely finite,
which is required before applying monotonicity of `ENNReal.toReal`. -/
theorem klDiv_ne_top_of_llr_integrable
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hllr : Integrable (llr μ ν) μ) :
    klDiv μ ν ≠ ⊤ := by
  rw [klDiv_ne_top_iff]
  exact ⟨hμν, hllr⟩

end TomographyOracleCore
