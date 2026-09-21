import TomographyOracleCore.ProjectiveHaarMeasure
import Mathlib.Probability.Distributions.Beta
import Mathlib.Tactic

namespace TomographyOracleCore

open Filter MeasureTheory ProbabilityTheory Real Set Metric
open scoped ENNReal NNReal Topology

noncomputable section

/-!
# Beta integrals for a two-dimensional Haar block

The geometric part of the complex-sphere block decomposition identifies the
head mass with `Beta(2,k)`.  This file first develops the exact singular
integral needed by the information calculation directly from Mathlib's beta
density.  In particular, the inverse moment below is not postulated.
-/

/-- A positive-parameter real beta density is nonnegative. -/
lemma betaPDFReal_nonneg_of_pos' {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    0 ≤ betaPDFReal a b x := by
  rw [betaPDFReal]
  split_ifs with hx
  · exact mul_nonneg
      (mul_nonneg (one_div_nonneg.mpr (beta_pos ha hb).le)
        (Real.rpow_nonneg hx.1.le _))
      (Real.rpow_nonneg (by linarith [hx.2]) _)
  · exact le_rfl

/-- Converting Mathlib's `ℝ≥0∞` beta density back to `ℝ` recovers the
real beta density. -/
lemma betaPDF_toReal' {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x : ℝ) :
    (betaPDF a b x).toReal = betaPDFReal a b x := by
  rw [betaPDF]
  exact ENNReal.toReal_ofReal (betaPDFReal_nonneg_of_pos' ha hb x)

/-- The real beta density has integral one. -/
lemma integral_betaPDFReal_eq_one' {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    ∫ x, betaPDFReal a b x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (betaPDFReal_nonneg_of_pos' ha hb))
    (stronglyMeasurable_betaPDFReal a b).aestronglyMeasurable]
  simpa [betaPDF] using
    congrArg ENNReal.toReal (lintegral_betaPDF_eq_one ha hb)

/-- The real beta density is integrable. -/
lemma integrable_betaPDFReal' {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) :
    Integrable (betaPDFReal a b) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_betaPDFReal_eq_one' ha hb]
  exact one_ne_zero

/-- Multiplication by a real power shifts the first beta shape parameter. -/
lemma rpow_mul_betaPDFReal' {a b z x : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haz : 0 < a + z) :
    x ^ z * betaPDFReal a b x =
      (beta (a + z) b / beta a b) * betaPDFReal (a + z) b x := by
  rw [betaPDFReal, betaPDFReal]
  by_cases hx : 0 < x ∧ x < 1
  · rw [if_pos hx, if_pos hx]
    have hB : beta a b ≠ 0 := (beta_pos ha hb).ne'
    have hBz : beta (a + z) b ≠ 0 := (beta_pos haz hb).ne'
    have hxpow : x ^ z * x ^ (a - 1) = x ^ (a + z - 1) := by
      rw [← Real.rpow_add hx.1]
      congr 1
      ring
    calc
      x ^ z * (1 / beta a b * x ^ (a - 1) * (1 - x) ^ (b - 1)) =
          (1 / beta a b) * (x ^ z * x ^ (a - 1)) *
            (1 - x) ^ (b - 1) := by ring
      _ = (1 / beta a b) * x ^ (a + z - 1) *
            (1 - x) ^ (b - 1) := by rw [hxpow]
      _ = (beta (a + z) b / beta a b) *
          (1 / beta (a + z) b * x ^ (a + z - 1) *
            (1 - x) ^ (b - 1)) := by
        field_simp
  · rw [if_neg hx, if_neg hx]
    ring

/-- Exact Mellin transform of Mathlib's beta measure. -/
theorem integral_rpow_betaMeasure' {a b z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haz : 0 < a + z) :
    ∫ x, x ^ z ∂betaMeasure a b = beta (a + z) b / beta a b := by
  rw [betaMeasure]
  change (∫ x, x ^ z ∂volume.withDensity
      (fun x ↦ ENNReal.ofReal (betaPDFReal a b x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_betaPDFReal a b).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (betaPDFReal_nonneg_of_pos' ha hb _),
    mul_comm (betaPDFReal a b _), rpow_mul_betaPDFReal' ha hb haz]
  rw [integral_const_mul, integral_betaPDFReal_eq_one' haz hb, mul_one]

/-- Real powers in the natural Mellin strip are beta-integrable. -/
theorem integrable_rpow_betaMeasure' {a b z : ℝ}
    (ha : 0 < a) (hb : 0 < b) (haz : 0 < a + z) :
    Integrable (fun x : ℝ ↦ x ^ z) (betaMeasure a b) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_rpow_betaMeasure' ha hb haz]
  exact div_ne_zero (beta_pos haz hb).ne' (beta_pos ha hb).ne'

/-- A beta law with positive shapes is concentrated on `(0,1)`. -/
theorem ae_mem_Ioo_betaMeasure' (a b : ℝ) :
    ∀ᵐ x ∂betaMeasure a b, x ∈ Ioo (0 : ℝ) 1 := by
  rw [betaMeasure]
  refine (ae_withDensity_iff
    (measurable_betaPDFReal a b).ennreal_ofReal).2 ?_
  filter_upwards with x
  intro hpdf
  by_contra hx
  apply hpdf
  have hzero : betaPDFReal a b x = 0 := by
    rw [betaPDFReal, if_neg]
    exact hx
  rw [hzero, ENNReal.ofReal_zero]

/-- The reciprocal observable agrees almost everywhere with the `-1` Mellin
power under a beta law. -/
theorem inv_ae_eq_rpow_neg_one_betaMeasure (a b : ℝ) :
    (fun x : ℝ ↦ x⁻¹) =ᵐ[betaMeasure a b]
      (fun x : ℝ ↦ x ^ (-1 : ℝ)) := by
  filter_upwards [ae_mem_Ioo_betaMeasure' a b] with x hx
  rw [Real.rpow_neg_one]

/-- Exact reciprocal moment of `Beta(2,k)`. -/
theorem integral_inv_betaMeasure_two (k : ℕ) (hk : 1 ≤ k) :
    ∫ x : ℝ, x⁻¹ ∂betaMeasure 2 (k : ℝ) = (k : ℝ) + 1 := by
  rw [integral_congr_ae (inv_ae_eq_rpow_neg_one_betaMeasure 2 (k : ℝ))]
  rw [integral_rpow_betaMeasure' (by norm_num) (by positivity) (by norm_num)]
  unfold beta
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hGk : Real.Gamma (k : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hGk1 : Real.Gamma ((k : ℝ) + 1) =
      (k : ℝ) * Real.Gamma (k : ℝ) :=
    Real.Gamma_add_one hk0
  have hGk2 : Real.Gamma ((k : ℝ) + 1 + 1) =
      ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) :=
    Real.Gamma_add_one (by positivity)
  have hGk2' : Real.Gamma (2 + (k : ℝ)) =
      ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := by
    convert hGk2 using 1 <;> ring
  have hGk1' : Real.Gamma (1 + (k : ℝ)) =
      Real.Gamma (k : ℝ) * (k : ℝ) := by
    rw [show 1 + (k : ℝ) = (k : ℝ) + 1 by ring, hGk1]
    ring
  have hGk1'' : Real.Gamma ((k : ℝ) + 1) =
      Real.Gamma (k : ℝ) * (k : ℝ) := by
    rw [hGk1]
    ring
  norm_num [hGk1', hGk1'', hGk2']
  field_simp

/-- Exact first moment of `Beta(2,k)`. -/
theorem integral_id_betaMeasure_two (k : ℕ) (hk : 1 ≤ k) :
    ∫ x : ℝ, x ∂betaMeasure 2 (k : ℝ) =
      2 / ((k : ℝ) + 2) := by
  have hpow : (fun x : ℝ ↦ x) = (fun x : ℝ ↦ x ^ (1 : ℝ)) := by
    funext x
    simp
  rw [hpow, integral_rpow_betaMeasure' (by norm_num) (by positivity)
    (by norm_num)]
  unfold beta
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hGk : Real.Gamma (k : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hGk1 : Real.Gamma ((k : ℝ) + 1) =
      (k : ℝ) * Real.Gamma (k : ℝ) :=
    Real.Gamma_add_one hk0
  have hGk2 : Real.Gamma ((k : ℝ) + 1 + 1) =
      ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) :=
    Real.Gamma_add_one (by positivity)
  have hGk3 : Real.Gamma ((k : ℝ) + 1 + 1 + 1) =
      ((k : ℝ) + 2) * Real.Gamma ((k : ℝ) + 1 + 1) := by
    convert Real.Gamma_add_one (show (k : ℝ) + 2 ≠ 0 by positivity) using 1 <;> ring
  have hGk2' : Real.Gamma (2 + (k : ℝ)) =
      ((k : ℝ) + 1) * Real.Gamma ((k : ℝ) + 1) := by
    convert hGk2 using 1 <;> ring
  have hGk3' : Real.Gamma (3 + (k : ℝ)) =
      ((k : ℝ) + 2) * Real.Gamma (2 + (k : ℝ)) := by
    calc
      Real.Gamma (3 + (k : ℝ)) =
          Real.Gamma ((k : ℝ) + 1 + 1 + 1) := by congr 1 <;> ring
      _ = ((k : ℝ) + 2) *
          Real.Gamma ((k : ℝ) + 1 + 1) := hGk3
      _ = ((k : ℝ) + 2) * Real.Gamma (2 + (k : ℝ)) := by
        congr 2 <;> ring
  norm_num [hGk1, hGk2', hGk3']
  field_simp

/-- Integrability of the singular information observable for `Beta(2,k)`. -/
theorem integrable_one_sub_sq_div_betaMeasure_two
    (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun x : ℝ ↦ (1 - x) ^ 2 / x)
      (betaMeasure 2 (k : ℝ)) := by
  have hinv : Integrable (fun x : ℝ ↦ x⁻¹)
      (betaMeasure 2 (k : ℝ)) := by
    exact (integrable_rpow_betaMeasure' (a := 2) (b := (k : ℝ))
      (z := -1) (by norm_num) (by positivity) (by norm_num)).congr
        (inv_ae_eq_rpow_neg_one_betaMeasure 2 (k : ℝ)).symm
  have hconst : Integrable (fun _ : ℝ ↦ (2 : ℝ))
      (betaMeasure 2 (k : ℝ)) := by
    letI : IsProbabilityMeasure (betaMeasure 2 (k : ℝ)) :=
      isProbabilityMeasureBeta (by norm_num) (by positivity)
    exact integrable_const 2
  have hid : Integrable (fun x : ℝ ↦ x)
      (betaMeasure 2 (k : ℝ)) := by
    simpa using integrable_rpow_betaMeasure' (a := 2) (b := (k : ℝ))
      (z := 1) (by norm_num) (by positivity) (by norm_num)
  have hbase : Integrable (fun x : ℝ ↦ x⁻¹ - 2 + x)
      (betaMeasure 2 (k : ℝ)) :=
    (hinv.sub hconst).add hid
  refine hbase.congr ?_
  filter_upwards [ae_mem_Ioo_betaMeasure' 2 (k : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx.1
  change x⁻¹ - 2 + x = (1 - x) ^ 2 / x
  field_simp
  ring

/-- Exact inverse information moment for the head mass `S ~ Beta(2,k)`:

`E[(1-S)^2/S] = k(k+1)/(k+2)`.
-/
theorem integral_one_sub_sq_div_betaMeasure_two
    (k : ℕ) (hk : 1 ≤ k) :
    ∫ x : ℝ, (1 - x) ^ 2 / x ∂betaMeasure 2 (k : ℝ) =
      (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
  have hae : (fun x : ℝ ↦ (1 - x) ^ 2 / x) =ᵐ[
      betaMeasure 2 (k : ℝ)] (fun x : ℝ ↦ x⁻¹ - 2 + x) := by
    filter_upwards [ae_mem_Ioo_betaMeasure' 2 (k : ℝ)] with x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    field_simp
    ring
  rw [integral_congr_ae hae]
  have hinv : Integrable (fun x : ℝ ↦ x⁻¹)
      (betaMeasure 2 (k : ℝ)) := by
    exact (integrable_rpow_betaMeasure' (a := 2) (b := (k : ℝ))
      (z := -1) (by norm_num) (by positivity) (by norm_num)).congr
        (inv_ae_eq_rpow_neg_one_betaMeasure 2 (k : ℝ)).symm
  have hconst : Integrable (fun _ : ℝ ↦ (2 : ℝ))
      (betaMeasure 2 (k : ℝ)) := by
    letI : IsProbabilityMeasure (betaMeasure 2 (k : ℝ)) :=
      isProbabilityMeasureBeta (by norm_num) (by positivity)
    exact integrable_const 2
  have hid : Integrable (fun x : ℝ ↦ x)
      (betaMeasure 2 (k : ℝ)) := by
    simpa using integrable_rpow_betaMeasure' (a := 2) (b := (k : ℝ))
      (z := 1) (by norm_num) (by positivity) (by norm_num)
  have huniv : ∫ _x : ℝ, (2 : ℝ) ∂betaMeasure 2 (k : ℝ) = 2 := by
    letI : IsProbabilityMeasure (betaMeasure 2 (k : ℝ)) :=
      isProbabilityMeasureBeta (by norm_num) (by positivity)
    simp
  calc
    (∫ x : ℝ, x⁻¹ - 2 + x ∂betaMeasure 2 (k : ℝ)) =
        (∫ x : ℝ, x⁻¹ - 2 ∂betaMeasure 2 (k : ℝ)) +
          ∫ x : ℝ, x ∂betaMeasure 2 (k : ℝ) := by
      exact integral_add (hinv.sub hconst) hid
    _ = ((∫ x : ℝ, x⁻¹ ∂betaMeasure 2 (k : ℝ)) -
          ∫ _x : ℝ, (2 : ℝ) ∂betaMeasure 2 (k : ℝ)) +
          ∫ x : ℝ, x ∂betaMeasure 2 (k : ℝ) := by
      rw [integral_sub hinv hconst]
    _ = ((k : ℝ) + 1 - 2) + 2 / ((k : ℝ) + 2) := by
      rw [integral_inv_betaMeasure_two k hk,
        integral_id_betaMeasure_two k hk, huniv]
    _ = (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
      have hk2 : (k : ℝ) + 2 ≠ 0 := by positivity
      field_simp
      ring

/-! ## Exact remaining geometric bridge -/

/-- Squared mass of the first two complex coordinates of a unit vector in
`ℂ^(2+k)`. -/
noncomputable def complexHaarHeadMass (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) : ℝ :=
  ∑ i : Fin 2, Complex.normSq (x.1 (Fin.castAdd k i))

theorem measurable_complexHaarHeadMass (k : ℕ) :
    Measurable (complexHaarHeadMass k) := by
  unfold complexHaarHeadMass
  fun_prop

/-- The exact, still-geometric statement required to transport the beta
calculation to the concrete normalized Haar sphere measure.  This is a
definition of a proposition, not an axiom or an assumed theorem. -/
def ComplexHaarHeadMassBetaLaw (k : ℕ) : Prop :=
  Measure.map (complexHaarHeadMass k)
      (complexUnitSphereHaarLaw (Fin (2 + k))) =
    betaMeasure 2 (k : ℝ)

/-- Once the geometric pushforward identity is established, integrability of
the singular Haar head-mass observable follows from the unconditional beta
calculation above. -/
theorem integrable_complexHaarHeadMass_information
    (k : ℕ) (hk : 1 ≤ k) (hlaw : ComplexHaarHeadMassBetaLaw k) :
    Integrable
      (fun x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1 ↦
        (1 - complexHaarHeadMass k x) ^ 2 / complexHaarHeadMass k x)
      (complexUnitSphereHaarLaw (Fin (2 + k))) := by
  let g : ℝ → ℝ := fun s ↦ (1 - s) ^ 2 / s
  have hg : Integrable g
      (Measure.map (complexHaarHeadMass k)
        (complexUnitSphereHaarLaw (Fin (2 + k)))) := by
    rw [hlaw]
    exact integrable_one_sub_sq_div_betaMeasure_two k hk
  exact hg.comp_aemeasurable
    (measurable_complexHaarHeadMass k).aemeasurable |>.congr
      (Filter.Eventually.of_forall fun _ ↦ rfl)

/-- Conditional transport statement pinpointing the sole remaining gap: the
actual Haar inverse moment has the desired exact value as soon as the literal
head-mass pushforward is proved. -/
theorem integral_complexHaarHeadMass_information
    (k : ℕ) (hk : 1 ≤ k) (hlaw : ComplexHaarHeadMassBetaLaw k) :
    ∫ x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1,
        (1 - complexHaarHeadMass k x) ^ 2 / complexHaarHeadMass k x
      ∂complexUnitSphereHaarLaw (Fin (2 + k)) =
      (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) := by
  let g : ℝ → ℝ := fun s ↦ (1 - s) ^ 2 / s
  have hg : Integrable g
      (Measure.map (complexHaarHeadMass k)
        (complexUnitSphereHaarLaw (Fin (2 + k)))) := by
    rw [hlaw]
    exact integrable_one_sub_sq_div_betaMeasure_two k hk
  calc
    (∫ x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1,
        (1 - complexHaarHeadMass k x) ^ 2 / complexHaarHeadMass k x
        ∂complexUnitSphereHaarLaw (Fin (2 + k))) =
        ∫ s : ℝ, g s ∂Measure.map (complexHaarHeadMass k)
          (complexUnitSphereHaarLaw (Fin (2 + k))) := by
      symm
      exact integral_map (measurable_complexHaarHeadMass k).aemeasurable
        hg.aestronglyMeasurable
    _ = ∫ s : ℝ, (1 - s) ^ 2 / s ∂betaMeasure 2 (k : ℝ) := by
      rw [hlaw]
    _ = (k : ℝ) * ((k : ℝ) + 1) / ((k : ℝ) + 2) :=
      integral_one_sub_sq_div_betaMeasure_two k hk

end

end TomographyOracleCore
