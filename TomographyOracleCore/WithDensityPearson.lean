import TomographyOracleCore.PearsonKL
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

namespace TomographyOracleCore

open MeasureTheory
open scoped ENNReal

/-!
# Pearson divergence for two densities over one base measure

The physical POVM model represents every Born law as a density with respect
to one finite scalar base measure.  This file proves the exact
Radon--Nikodym ratio and Pearson integral formula for that representation.
It contains no tomography-specific assumption and no external theorem.
-/

/-- The Radon--Nikodym derivative of `p * μ` with respect to `q * μ` is
`p / q` whenever the reference density is positive and both densities are
finite almost everywhere. -/
theorem rnDeriv_withDensity_div
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ]
    (p q : Ω → ℝ≥0∞)
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ)
    (hp_ne_top : ∀ᵐ z ∂μ, p z ≠ ∞)
    (hq_ne_zero : ∀ᵐ z ∂μ, q z ≠ 0)
    (hq_ne_top : ∀ᵐ z ∂μ, q z ≠ ∞) :
    (μ.withDensity p).rnDeriv (μ.withDensity q) =ᵐ[μ]
      fun z ↦ p z / q z := by
  letI : SigmaFinite (μ.withDensity p) :=
    SigmaFinite.withDensity_of_ne_top hp_ne_top
  have hright :=
    Measure.rnDeriv_withDensity_right (μ.withDensity p) μ
      hq hq_ne_zero hq_ne_top
  have hleft := Measure.rnDeriv_withDensity₀ μ hp
  filter_upwards [hright, hleft] with z hzright hzleft
  rw [hzright, hzleft]
  simp only [div_eq_mul_inv, mul_comm]

/-- Positivity of the reference density gives absolute continuity of the two
weighted laws in the direction required by KL. -/
theorem withDensity_absolutelyContinuous_withDensity
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q : Ω → ℝ≥0∞)
    (hq : AEMeasurable q μ)
    (hq_ne_zero : ∀ᵐ z ∂μ, q z ≠ 0) :
    μ.withDensity p ≪ μ.withDensity q := by
  exact (withDensity_absolutelyContinuous μ p).trans
    (withDensity_absolutelyContinuous' hq hq_ne_zero)

/-- Exact real Pearson formula for two weighted laws over one base measure. -/
theorem pearsonChiSquare_withDensity_eq_integral
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ]
    (p q : Ω → ℝ≥0∞)
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ)
    (hp_ne_top : ∀ᵐ z ∂μ, p z ≠ ∞)
    (hq_ne_zero : ∀ᵐ z ∂μ, q z ≠ 0)
    (hq_ne_top : ∀ᵐ z ∂μ, q z ≠ ∞) :
    pearsonChiSquare (μ.withDensity p) (μ.withDensity q) =
      ∫ z, ((p z).toReal - (q z).toReal) ^ 2 /
        (q z).toReal ∂μ := by
  have hratio := rnDeriv_withDensity_div μ p q hp hq
    hp_ne_top hq_ne_zero hq_ne_top
  have hratio_q :
      (μ.withDensity p).rnDeriv (μ.withDensity q) =ᵐ[μ.withDensity q]
        fun z ↦ p z / q z :=
    (withDensity_absolutelyContinuous μ q).ae_eq hratio
  have hcongr :
      (fun z ↦
        (((μ.withDensity p).rnDeriv (μ.withDensity q) z).toReal - 1) ^ 2)
        =ᵐ[μ.withDensity q]
      (fun z ↦ ((p z / q z).toReal - 1) ^ 2) := by
    filter_upwards [hratio_q] with z hz
    rw [hz]
  unfold pearsonChiSquare
  rw [integral_congr_ae hcongr]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hq
    (hq_ne_top.mono fun z hz ↦ (lt_top_iff_ne_top).2 hz)]
  apply integral_congr_ae
  filter_upwards [hq_ne_zero, hq_ne_top] with z hq0 hqtop
  have hqreal : (q z).toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hq0, hqtop⟩
  simp only [ENNReal.toReal_div, smul_eq_mul]
  field_simp

end TomographyOracleCore
