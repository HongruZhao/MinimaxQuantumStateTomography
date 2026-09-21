import TomographyOracleCore.PortedScalarGammaBetaBridge
import Mathlib.Tactic

/-!
# Exact scalar Gamma Laplace transforms

The fixed-subspace Gaussian argument needs only an elementary Laplace
transform of an integer-shape Gamma law.  We prove it from Mathlib's literal
Gamma density, retaining the more general real Mellin--Laplace identity as a
reusable intermediate theorem.
-/

namespace TomographyOracleCore

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

/-- The real-valued Gamma density integrates to one. -/
lemma integral_gammaPDFReal_eq_one {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∫ x, gammaPDFReal a r x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae
    (ae_of_all _ (gammaPDFReal_nonneg ha hr))
    (stronglyMeasurable_gammaPDFReal a r).aestronglyMeasurable]
  simpa [gammaPDF] using
    congrArg ENNReal.toReal (lintegral_gammaPDF_eq_one ha hr)

/-- Multiplying a Gamma density by a Mellin power and exponential tilt
changes its shape and rate. -/
private theorem rpow_exp_mul_gammaPDFReal
    {a r t c x : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hat : 0 < a + t) (hrc : 0 < r + c) (hx : 0 < x) :
    x ^ t * Real.exp (-c * x) * gammaPDFReal a r x =
      (r ^ a * Real.Gamma (a + t) /
          (Real.Gamma a * (r + c) ^ (a + t))) *
        gammaPDFReal (a + t) (r + c) x := by
  rw [gammaPDFReal, gammaPDFReal, if_pos hx.le, if_pos hx.le]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGat : Real.Gamma (a + t) ≠ 0 :=
    (Real.Gamma_pos_of_pos hat).ne'
  have hxp : x ^ t * x ^ (a - 1) = x ^ (a + t - 1) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hexp : Real.exp (-c * x) * Real.exp (-(r * x)) =
      Real.exp (-((r + c) * x)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    x ^ t * Real.exp (-c * x) *
          (r ^ a / Real.Gamma a * x ^ (a - 1) * Real.exp (-(r * x))) =
        (r ^ a / Real.Gamma a) * (x ^ t * x ^ (a - 1)) *
          (Real.exp (-c * x) * Real.exp (-(r * x))) := by ring
    _ = (r ^ a / Real.Gamma a) * x ^ (a + t - 1) *
          Real.exp (-((r + c) * x)) := by rw [hxp, hexp]
    _ = (r ^ a * Real.Gamma (a + t) /
          (Real.Gamma a * (r + c) ^ (a + t))) *
        ((r + c) ^ (a + t) / Real.Gamma (a + t) *
          x ^ (a + t - 1) * Real.exp (-((r + c) * x))) := by
      field_simp [hGa, hGat, (Real.rpow_pos_of_pos hrc _).ne']

/-- Exact real Mellin--Laplace transform of a Gamma law. -/
theorem integral_rpow_mul_exp_neg_mul_gammaMeasure
    {a r t c : ℝ} (ha : 0 < a) (hr : 0 < r)
    (hat : 0 < a + t) (hrc : 0 < r + c) :
    ∫ x, x ^ t * Real.exp (-c * x) ∂gammaMeasure a r =
      r ^ a * Real.Gamma (a + t) /
        (Real.Gamma a * (r + c) ^ (a + t)) := by
  rw [gammaMeasure]
  change (∫ x, x ^ t * Real.exp (-c * x)
      ∂volume.withDensity
        (fun x ↦ ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_gammaPDFReal a r).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  simp_rw [smul_eq_mul,
    ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _)]
  have hae :
      (fun x ↦ x ^ t * Real.exp (-c * x) * gammaPDFReal a r x) =ᵐ[volume]
        (fun x ↦
          (r ^ a * Real.Gamma (a + t) /
            (Real.Gamma a * (r + c) ^ (a + t))) *
              gammaPDFReal (a + t) (r + c) x) := by
    have hne : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by
      simp [ae_iff, measure_singleton]
    filter_upwards [hne] with x hx0
    by_cases hx : 0 < x
    · exact rpow_exp_mul_gammaPDFReal ha hr hat hrc hx
    · have hxneg : x < 0 := lt_of_le_of_ne (le_of_not_gt hx) hx0
      simp [gammaPDFReal, not_le.mpr hxneg]
  have hae' :
      (fun x ↦ gammaPDFReal a r x *
          (x ^ t * Real.exp (-c * x))) =ᵐ[volume]
        (fun x ↦
          (r ^ a * Real.Gamma (a + t) /
            (Real.Gamma a * (r + c) ^ (a + t))) *
              gammaPDFReal (a + t) (r + c) x) := by
    filter_upwards [hae] with x hx
    rw [← hx]
    ring
  rw [integral_congr_ae hae', integral_const_mul,
    integral_gammaPDFReal_eq_one hat hrc, mul_one]

/-- Laplace transform of an integer-shape Gamma law at rate `1/2`. -/
theorem integral_exp_neg_mul_gammaMeasure_nat_half
    {q : ℕ} (hq : 0 < q) {c : ℝ} (hc : 0 ≤ c) :
    (∫ x : ℝ, Real.exp (-c * x) ∂gammaMeasure (q : ℝ) (1 / 2)) =
      (1 / (1 + 2 * c)) ^ q := by
  have hshape : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrate : (0 : ℝ) < 1 / 2 := by norm_num
  have hshift : (0 : ℝ) < 1 / 2 + c := by linarith
  have h := integral_rpow_mul_exp_neg_mul_gammaMeasure
    (a := (q : ℝ)) (r := 1 / 2) (t := 0) (c := c)
    hshape hrate (by simpa using hshape) hshift
  have hG : Real.Gamma (q : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hshape).ne'
  calc
    (∫ x : ℝ, Real.exp (-c * x) ∂gammaMeasure (q : ℝ) (1 / 2)) =
        (1 / 2 : ℝ) ^ q * Real.Gamma (q : ℝ) /
          (Real.Gamma (q : ℝ) * ((1 / 2 : ℝ) + c) ^ q) := by
      simpa [Real.rpow_natCast] using h
    _ = (1 / (1 + 2 * c)) ^ q := by
      have hden : (1 + 2 * c) ≠ 0 := by positivity
      rw [show (1 / 2 : ℝ) + c = (1 / 2) * (1 + 2 * c) by ring,
        mul_pow]
      field_simp [hG, hden]
      rw [← mul_pow, one_div, mul_inv_cancel₀ hden, one_pow]

/-- Mean of an integer-shape Gamma law at rate `1/2`. -/
theorem integral_id_gammaMeasure_nat_half {q : ℕ} (hq : 0 < q) :
    (∫ x : ℝ, x ∂gammaMeasure (q : ℝ) (1 / 2)) = 2 * q := by
  have hshape : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hrate : (0 : ℝ) < 1 / 2 := by norm_num
  have h := integral_rpow_mul_exp_neg_mul_gammaMeasure
    (a := (q : ℝ)) (r := 1 / 2) (t := 1) (c := 0)
    hshape hrate (by linarith) (by norm_num)
  have hG : Real.Gamma (q : ℝ) ≠ 0 :=
    (Real.Gamma_pos_of_pos hshape).ne'
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  calc
    (∫ x : ℝ, x ∂gammaMeasure (q : ℝ) (1 / 2)) =
        ∫ x : ℝ, x ^ (1 : ℝ) * Real.exp (-0 * x)
          ∂gammaMeasure (q : ℝ) (1 / 2) := by
            apply integral_congr_ae
            filter_upwards with x
            simp
    _ = (1 / 2 : ℝ) ^ (q : ℝ) * Real.Gamma ((q : ℝ) + 1) /
        (Real.Gamma (q : ℝ) *
          (1 / 2 : ℝ) ^ ((q : ℝ) + 1)) := by simpa using h
    _ = 2 * q := by
      rw [Real.Gamma_add_one]
      rw [Real.rpow_add (by norm_num : (0 : ℝ) < 1 / 2)]
      norm_num
      field_simp [hG, hq0]
      exact hq0

end

end TomographyOracleCore
