import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Beta
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

/-!
# Scalar Gamma and Beta bridge lemmas

This file develops analytic identities needed to prove that sums of independent
Gamma variables are Gamma and that normalized Gamma variables are Beta.  It is
kept independent of the log-determinant formalization.

Mathematical provenance: the chi-square/Gamma and independent-ratio-to-Beta
facts are the scalar ingredients used in Rouault (2005), proof of Proposition
2.1, printed pp. 5--6.  The ratio fact is also stated by Olkin--Rubin (1964).
This file supplies an independent measure-level proof from densities,
convolution, the beta integral, and a two-dimensional Jacobian because the
pinned mathlib version had no specialized bridge theorem.  See
`PROVENANCE.md`; these classical probability identities are not claimed as
new mathematics.
-/

namespace LogdetLean

noncomputable section

open scoped ENNReal NNReal MeasureTheory
open MeasureTheory Real Set
open ProbabilityTheory

/-- The scaled real Beta integral.  This is the exact integral that appears in
the convolution of two Gamma densities. -/
theorem integral_rpow_mul_sub_rpow {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht : 0 < t) :
    ∫ x in 0..t, x ^ (a - 1) * (t - x) ^ (b - 1) =
      t ^ (a + b - 1) * beta a b := by
  have hscaled := Complex.betaIntegral_scaled (a : ℂ) (b : ℂ) ht
  have hcomplex :
      (∫ x in 0..t,
        (x : ℂ) ^ ((a : ℂ) - 1) * ((t : ℂ) - x) ^ ((b : ℂ) - 1)) =
        ((∫ x in 0..t, x ^ (a - 1) * (t - x) ^ (b - 1) : ℝ) : ℂ) := by
    rw [intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_of_le ht.le]
    calc
      ∫ x in Ioc 0 t,
          (x : ℂ) ^ ((a : ℂ) - 1) * ((t : ℂ) - x) ^ ((b : ℂ) - 1) =
          ∫ x in Ioc 0 t, ((x ^ (a - 1) * (t - x) ^ (b - 1) : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x hx
        rcases hx with ⟨hx0, hxt⟩
        dsimp only
        rw [← Complex.ofReal_sub]
        have haexp : (a : ℂ) - 1 = ((a - 1 : ℝ) : ℂ) := by norm_num
        have hbexp : (b : ℂ) - 1 = ((b - 1 : ℝ) : ℂ) := by norm_num
        rw [haexp, hbexp, ← Complex.ofReal_cpow, ← Complex.ofReal_cpow]
        · norm_num
        · exact sub_nonneg.mpr hxt
        · exact hx0.le
      _ = ((∫ x in Ioc 0 t, x ^ (a - 1) * (t - x) ^ (b - 1) : ℝ) : ℂ) :=
        integral_ofReal
  calc
    ∫ x in 0..t, x ^ (a - 1) * (t - x) ^ (b - 1) =
        (∫ x in 0..t,
          (x : ℂ) ^ ((a : ℂ) - 1) * ((t : ℂ) - x) ^ ((b : ℂ) - 1)).re := by
      rw [hcomplex]
      norm_num
    _ = (((t : ℂ) ^ ((a : ℂ) + b - 1)) * Complex.betaIntegral a b).re := by
      rw [hscaled]
    _ = t ^ (a + b - 1) * beta a b := by
      have hexp : (a : ℂ) + (b : ℂ) - 1 = ((a + b - 1 : ℝ) : ℂ) := by norm_num
      rw [hexp, ← Complex.ofReal_cpow ht.le]
      rw [ProbabilityTheory.beta_eq_betaIntegralReal a b ha hb]
      rw [Complex.mul_re]
      norm_num

/-- Pointwise convolution identity for two real Gamma densities with the same
rate, written as an interval integral over the common positive support. -/
theorem intervalIntegral_gammaPDFReal_mul_sub {a b r t : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) (ht : 0 < t) :
    ∫ x in 0..t, gammaPDFReal a r x * gammaPDFReal b r (t - x) =
      gammaPDFReal (a + b) r t := by
  let C : ℝ :=
    (r ^ a / Real.Gamma a) * (r ^ b / Real.Gamma b) * Real.exp (-(r * t))
  have hpoint : ∀ x ∈ Ioc (0 : ℝ) t,
      gammaPDFReal a r x * gammaPDFReal b r (t - x) =
        C * (x ^ (a - 1) * (t - x) ^ (b - 1)) := by
    intro x hx
    have hx0 : 0 ≤ x := hx.1.le
    have htx : 0 ≤ t - x := sub_nonneg.mpr hx.2
    rw [gammaPDFReal, gammaPDFReal, if_pos hx0, if_pos htx]
    dsimp [C]
    have hexp : Real.exp (-(r * x)) * Real.exp (-(r * (t - x))) =
        Real.exp (-(r * t)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [← hexp]
    ring
  rw [intervalIntegral.integral_of_le ht.le]
  calc
    ∫ x in Ioc (0 : ℝ) t, gammaPDFReal a r x * gammaPDFReal b r (t - x) =
        ∫ x in Ioc (0 : ℝ) t, C * (x ^ (a - 1) * (t - x) ^ (b - 1)) :=
      setIntegral_congr_fun measurableSet_Ioc hpoint
    _ = C * ∫ x in Ioc (0 : ℝ) t, x ^ (a - 1) * (t - x) ^ (b - 1) := by
      rw [integral_const_mul]
    _ = C * (t ^ (a + b - 1) * beta a b) := by
      rw [← intervalIntegral.integral_of_le ht.le, integral_rpow_mul_sub_rpow ha hb ht]
    _ = gammaPDFReal (a + b) r t := by
      rw [gammaPDFReal, if_pos ht.le]
      dsimp [C, beta]
      rw [Real.rpow_add hr a b]
      have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
      have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
      have hGab : Real.Gamma (a + b) ≠ 0 :=
        (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
      field_simp [hGa, hGb, hGab]

/-- The exact Jacobian factorization behind the Gamma-to-Beta change of
variables `(x,y) = (u s, (1-u)s)`.  The Jacobian determinant is `s`.

This identity is the density-level core of both facts:

* `X + Y` is Gamma when `X,Y` are independent Gamma variables of a common rate;
* `X / (X+Y)` is Beta and is independent of `X+Y`.
-/
theorem gamma_beta_jacobian_factorization {a b r u s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hu0 : 0 < u) (hu1 : u < 1) (hs : 0 < s) :
    gammaPDFReal a r (u * s) * gammaPDFReal b r ((1 - u) * s) * s =
      betaPDFReal a b u * gammaPDFReal (a + b) r s := by
  have hus0 : 0 ≤ u * s := (mul_pos hu0 hs).le
  have h1us0 : 0 ≤ (1 - u) * s := (mul_pos (sub_pos.mpr hu1) hs).le
  rw [gammaPDFReal, gammaPDFReal, gammaPDFReal, betaPDFReal,
    if_pos hus0, if_pos h1us0, if_pos hs.le, if_pos ⟨hu0, hu1⟩]
  rw [Real.mul_rpow hu0.le hs.le, Real.mul_rpow (sub_nonneg.mpr hu1.le) hs.le]
  rw [Real.rpow_add hr a b]
  have hsa : s ^ (a - 1) * s ^ (b - 1) = s ^ (a + b - 2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hscombine : s ^ (a - 1) * s ^ (b - 1) * s = s ^ (a + b - 1) := by
    calc
      s ^ (a - 1) * s ^ (b - 1) * s = s ^ (a + b - 2) * s := by rw [hsa]
      _ = s ^ (a + b - 2) * s ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = s ^ ((a + b - 2) + 1) := (Real.rpow_add hs _ _).symm
      _ = s ^ (a + b - 1) := by ring_nf
  have hexp : Real.exp (-(r * (u * s))) * Real.exp (-(r * ((1 - u) * s))) =
      Real.exp (-(r * s)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← hexp]
  dsimp [beta]
  have hGa : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hGb : Real.Gamma b ≠ 0 := (Real.Gamma_pos_of_pos hb).ne'
  have hGab : Real.Gamma (a + b) ≠ 0 :=
    (Real.Gamma_pos_of_pos (add_pos ha hb)).ne'
  field_simp [hGa, hGb, hGab]
  ring_nf
  have hscombine' : s ^ (-1 + a) * s * s ^ (-1 + b) = s ^ (-1 + a + b) := by
    calc
      s ^ (-1 + a) * s * s ^ (-1 + b) =
          s ^ (-1 + a) * s ^ (1 : ℝ) * s ^ (-1 + b) := by rw [Real.rpow_one]
      _ = s ^ ((-1 + a) + 1) * s ^ (-1 + b) :=
        congrArg (fun z : ℝ ↦ z * s ^ (-1 + b)) (Real.rpow_add hs (-1 + a) 1).symm
      _ = s ^ (((-1 + a) + 1) + (-1 + b)) :=
        (Real.rpow_add hs ((-1 + a) + 1) (-1 + b)).symm
      _ = s ^ (-1 + a + b) := by ring_nf
  calc
    s ^ (-1 + a) * s * (1 - u) ^ (-1 + b) * s ^ (-1 + b) =
        (1 - u) ^ (-1 + b) * (s ^ (-1 + a) * s * s ^ (-1 + b)) := by ring
    _ = (1 - u) ^ (-1 + b) * s ^ (-1 + a + b) := by rw [hscombine']

/-- The inverse-Jacobian density obtained by squaring a standard real Gaussian
is the Gamma density with shape `1/2` and rate `1/2` (equivalently,
chi-square with one degree of freedom). -/
theorem gaussian_square_density_eq_gamma_half {x : ℝ} (hx : 0 < x) :
    (gaussianPDFReal 0 1 (Real.sqrt x) + gaussianPDFReal 0 1 (-Real.sqrt x)) /
        (2 * Real.sqrt x) =
      gammaPDFReal (1 / 2) (1 / 2) x := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hsx2 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx.le
  rw [gaussianPDFReal, gaussianPDFReal, gammaPDFReal, if_pos hx.le,
    Real.Gamma_one_half_eq]
  norm_num [hsx2]
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [Real.rpow_neg (le_of_lt hx)]
  rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.one_rpow]
  rw [Real.sqrt_eq_rpow x]
  have hexp : Real.exp (-x / 2) = Real.exp (-(1 / 2 * x)) := by
    congr 1
    ring
  rw [hexp]
  have h2 : 0 < (2 : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
  have hpi : 0 < Real.pi ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos Real.pi_pos _
  have hxhalf : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  field_simp [h2.ne', hpi.ne', hxhalf.ne']
  ring

/-! ## The Beta--Gamma coordinate change -/

/-- Coordinates `(x,y) ↦ (x/(x+y),x+y)` on the positive quadrant.  The inverse
is `(u,s) ↦ (u*s,(1-u)*s)`. -/
def betaGammaCoord : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun q := (q.1 / (q.1 + q.2), q.1 + q.2)
  invFun p := (p.1 * p.2, (1 - p.1) * p.2)
  source := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  target := Ioo (0 : ℝ) 1 ×ˢ Ioi (0 : ℝ)
  map_target' := by
    rintro ⟨u, s⟩ ⟨⟨hu0, hu1⟩, hs⟩
    exact ⟨mul_pos hu0 hs, mul_pos (sub_pos.mpr hu1) hs⟩
  map_source' := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    change 0 < x at hx
    change 0 < y at hy
    have hsum : 0 < x + y := add_pos hx hy
    exact ⟨⟨div_pos hx hsum, (div_lt_one hsum).2 (lt_add_of_pos_right x hy)⟩, hsum⟩
  right_inv' := by
    rintro ⟨u, s⟩ ⟨⟨hu0, hu1⟩, hs⟩
    change 0 < u at hu0
    change u < 1 at hu1
    change 0 < s at hs
    ext <;> dsimp
    · field_simp [hs.ne']
      ring
    · ring
  left_inv' := by
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    have hsum : x + y ≠ 0 := (add_pos hx hy).ne'
    ext <;> dsimp
    · field_simp [hsum]
    · field_simp [hsum]
      ring
  open_source := isOpen_Ioi.prod isOpen_Ioi
  open_target := isOpen_Ioo.prod isOpen_Ioi
  continuousOn_invFun := by fun_prop
  continuousOn_toFun := by
    refine ContinuousOn.prodMk ?_ (continuousOn_fst.add continuousOn_snd)
    refine ContinuousOn.div continuousOn_fst (continuousOn_fst.add continuousOn_snd) ?_
    rintro ⟨x, y⟩ ⟨hx, hy⟩
    exact (add_pos hx hy).ne'

@[simp] theorem betaGammaCoord_apply (q : ℝ × ℝ) :
    betaGammaCoord q = (q.1 / (q.1 + q.2), q.1 + q.2) := rfl

@[simp] theorem betaGammaCoord_symm_apply (p : ℝ × ℝ) :
    betaGammaCoord.symm p = (p.1 * p.2, (1 - p.1) * p.2) := rfl

/-- The derivative of `(u,s) ↦ (u*s,(1-u)*s)`. -/
def fderivBetaGammaCoordSymm (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![p.2, p.1; -p.2, 1 - p.1]).toContinuousLinearMap

theorem hasFDerivAt_betaGammaCoord_symm (p : ℝ × ℝ) :
    HasFDerivAt betaGammaCoord.symm (fderivBetaGammaCoordSymm p) p := by
  have hfst : HasFDerivAt (fun q : ℝ × ℝ ↦ q.1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) p := hasFDerivAt_fst
  have hsnd : HasFDerivAt (fun q : ℝ × ℝ ↦ q.2)
      (ContinuousLinearMap.snd ℝ ℝ ℝ) p := hasFDerivAt_snd
  have hone : HasFDerivAt (fun _q : ℝ × ℝ ↦ (1 : ℝ)) 0 p :=
    hasFDerivAt_const (𝕜 := ℝ) (x := p) (c := (1 : ℝ))
  unfold fderivBetaGammaCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert!
    HasFDerivAt.prodMk (𝕜 := ℝ)
      (hfst.mul hsnd)
      ((hone.sub hfst).mul hsnd) using 2
  all_goals
    try simp [sub_eq_add_neg]
  all_goals
    module

theorem det_fderivBetaGammaCoordSymm (p : ℝ × ℝ) :
    (fderivBetaGammaCoordSymm p).det = p.2 := by
  unfold fderivBetaGammaCoordSymm
  simp only [LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of]
  ring

/-- This local instance makes the product Lebesgue measure on `ℝ × ℝ`
available to the finite-dimensional Jacobian theorem. -/
local instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _

/-- Nonnegative change of variables from positive Cartesian coordinates to
Beta--Gamma coordinates. -/
theorem lintegral_comp_betaGammaCoord_symm (f : ℝ × ℝ → ℝ≥0∞) :
    (∫⁻ p in betaGammaCoord.target,
        ENNReal.ofReal p.2 * f (betaGammaCoord.symm p)) =
      ∫⁻ q in betaGammaCoord.source, f q := by
  symm
  calc
    (∫⁻ q in betaGammaCoord.source, f q) =
        ∫⁻ q in betaGammaCoord.symm '' betaGammaCoord.target, f q := by
      rw [betaGammaCoord.symm_image_target_eq_source]
    _ = ∫⁻ p in betaGammaCoord.target,
        ENNReal.ofReal |(fderivBetaGammaCoordSymm p).det| *
          f (betaGammaCoord.symm p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
        betaGammaCoord.open_target.measurableSet
        (fun p _ ↦ (hasFDerivAt_betaGammaCoord_symm p).hasFDerivWithinAt)
        betaGammaCoord.symm.injOn]
    _ = ∫⁻ p in betaGammaCoord.target,
        ENNReal.ofReal p.2 * f (betaGammaCoord.symm p) := by
      refine setLIntegral_congr_fun betaGammaCoord.open_target.measurableSet
        (fun p hp ↦ ?_)
      rw [det_fderivBetaGammaCoordSymm, abs_of_pos hp.2]

/-- `ℝ≥0∞`-valued form of the Beta--Gamma Jacobian factorization. -/
theorem gamma_beta_jacobian_factorization_ennreal {a b r u s : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hu0 : 0 < u) (hu1 : u < 1) (hs : 0 < s) :
    gammaPDF a r (u * s) * gammaPDF b r ((1 - u) * s) * ENNReal.ofReal s =
      betaPDF a b u * gammaPDF (a + b) r s := by
  have hga : 0 ≤ gammaPDFReal a r (u * s) :=
    gammaPDFReal_nonneg ha hr _
  have hgb : 0 ≤ gammaPDFReal b r ((1 - u) * s) :=
    gammaPDFReal_nonneg hb hr _
  have hbe : 0 ≤ betaPDFReal a b u :=
    (betaPDFReal_pos hu0 hu1 ha hb).le
  have hreal := gamma_beta_jacobian_factorization ha hb hr hu0 hu1 hs
  have h := congrArg ENNReal.ofReal hreal
  rw [ENNReal.ofReal_mul (mul_nonneg hga hgb), ENNReal.ofReal_mul hga,
    ENNReal.ofReal_mul hbe] at h
  exact h

private theorem ae_snd_ne_zero :
    ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ 0 := by
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae (by measurability)]
  exact Filter.Eventually.of_forall fun _ ↦ by
    simp [ae_iff, measure_singleton]

private theorem ae_fst_ne_zero :
    ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae (by measurability)]
  filter_upwards [(show ∀ᵐ x : ℝ ∂volume, x ≠ 0 by
    simp [ae_iff, measure_singleton])] with x hx
  exact Filter.Eventually.of_forall fun _ ↦ hx

private theorem betaGamma_target_density_ae_indicator (a b r : ℝ) :
    (fun p : ℝ × ℝ ↦ betaPDF a b p.1 * gammaPDF (a + b) r p.2) =ᵐ[volume]
      betaGammaCoord.target.indicator
        (fun p : ℝ × ℝ ↦ betaPDF a b p.1 * gammaPDF (a + b) r p.2) := by
  filter_upwards [ae_snd_ne_zero] with p hp2
  by_cases hp : p ∈ betaGammaCoord.target
  · simp [hp]
  · have hind : betaGammaCoord.target.indicator
        (fun p : ℝ × ℝ ↦ betaPDF a b p.1 * gammaPDF (a + b) r p.2) p = 0 := by
      simp [hp]
    rw [hind]
    change ¬ ((0 < p.1 ∧ p.1 < 1) ∧ 0 < p.2) at hp
    by_cases hu : 0 < p.1 ∧ p.1 < 1
    · have hsnonpos : p.2 ≤ 0 := le_of_not_gt (fun hs ↦ hp ⟨hu, hs⟩)
      have hsneg : p.2 < 0 := lt_of_le_of_ne hsnonpos hp2
      rw [gammaPDF_of_neg hsneg, mul_zero]
    · rw [betaPDF_eq]
      simp [hu]

private theorem betaGamma_source_density_ae_indicator (a b r : ℝ) :
    (fun q : ℝ × ℝ ↦ gammaPDF a r q.1 * gammaPDF b r q.2) =ᵐ[volume]
      betaGammaCoord.source.indicator
        (fun q : ℝ × ℝ ↦ gammaPDF a r q.1 * gammaPDF b r q.2) := by
  filter_upwards [ae_fst_ne_zero, ae_snd_ne_zero] with q hq1 hq2
  by_cases hq : q ∈ betaGammaCoord.source
  · simp [hq]
  · have hind : betaGammaCoord.source.indicator
        (fun q : ℝ × ℝ ↦ gammaPDF a r q.1 * gammaPDF b r q.2) q = 0 := by
      simp [hq]
    rw [hind]
    change ¬ (0 < q.1 ∧ 0 < q.2) at hq
    rcases not_and_or.mp hq with hq1nonpos | hq2nonpos
    · have hq1neg : q.1 < 0 := lt_of_le_of_ne (le_of_not_gt hq1nonpos) hq1
      rw [gammaPDF_of_neg hq1neg, zero_mul]
    · have hq2neg : q.2 < 0 := lt_of_le_of_ne (le_of_not_gt hq2nonpos) hq2
      rw [gammaPDF_of_neg hq2neg, mul_zero]

/-- The full Beta--Gamma algebra: applying `(u,s) ↦ (u*s,(1-u)*s)`
to an independent `Beta(a,b)` variable and `Gamma(a+b,r)` variable gives two
independent Gamma variables with shapes `a,b` and common rate `r`. -/
theorem map_betaGammaCoord_symm_prod_beta_gamma {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Measure.map betaGammaCoord.symm
        ((betaMeasure a b).prod (gammaMeasure (a + b) r)) =
      (gammaMeasure a r).prod (gammaMeasure b r) := by
  let hBG : ℝ × ℝ → ℝ≥0∞ :=
    fun p ↦ betaPDF a b p.1 * gammaPDF (a + b) r p.2
  let hGG : ℝ × ℝ → ℝ≥0∞ :=
    fun q ↦ gammaPDF a r q.1 * gammaPDF b r q.2
  have hβ : Measurable (betaPDF a b) :=
    ENNReal.measurable_ofReal.comp (measurable_betaPDFReal a b)
  have hγsum : Measurable (gammaPDF (a + b) r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal (a + b) r)
  have hγa : Measurable (gammaPDF a r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal a r)
  have hγb : Measurable (gammaPDF b r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal b r)
  have hBGm : Measurable hBG := by
    dsimp [hBG]
    fun_prop
  have hGGm : Measurable hGG := by
    dsimp [hGG]
    fun_prop
  have hF : Measurable betaGammaCoord.symm := by
    change Measurable (fun p : ℝ × ℝ ↦ (p.1 * p.2, (1 - p.1) * p.2))
    fun_prop
  have hprodBG :
      (betaMeasure a b).prod (gammaMeasure (a + b) r) = volume.withDensity hBG := by
    rw [betaMeasure, gammaMeasure, prod_withDensity hβ hγsum,
      ← Measure.volume_eq_prod]
  have hprodGG :
      (gammaMeasure a r).prod (gammaMeasure b r) = volume.withDensity hGG := by
    simp only [gammaMeasure]
    rw [prod_withDensity hγa hγb, ← Measure.volume_eq_prod]
  rw [hprodBG, hprodGG]
  apply Measure.ext_of_lintegral _
  intro f hf
  have hfc : Measurable (fun p ↦ f (betaGammaCoord.symm p)) := hf.comp hF
  rw [lintegral_map hf hF,
    lintegral_withDensity_eq_lintegral_mul volume hBGm hfc,
    lintegral_withDensity_eq_lintegral_mul volume hGGm hf]
  change (∫⁻ p, hBG p * f (betaGammaCoord.symm p) ∂volume) =
    ∫⁻ q, hGG q * f q ∂volume
  calc
    (∫⁻ p, hBG p * f (betaGammaCoord.symm p) ∂volume) =
        ∫⁻ p, betaGammaCoord.target.indicator
          (fun p ↦ hBG p * f (betaGammaCoord.symm p)) p ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [betaGamma_target_density_ae_indicator a b r] with p hp
      by_cases hpt : p ∈ betaGammaCoord.target
      · simp [hpt]
      · have hpzero' : betaPDF a b p.1 = 0 ∨ gammaPDF (a + b) r p.2 = 0 := by
          simpa [hpt] using hp
        have hpzero : hBG p = 0 := by
          rcases hpzero' with hpzero' | hpzero' <;> simp [hBG, hpzero']
        simp [hpt, hpzero]
    _ = ∫⁻ p in betaGammaCoord.target,
        hBG p * f (betaGammaCoord.symm p) ∂volume := by
      rw [lintegral_indicator betaGammaCoord.open_target.measurableSet]
    _ = ∫⁻ p in betaGammaCoord.target,
        ENNReal.ofReal p.2 *
          (hGG (betaGammaCoord.symm p) * f (betaGammaCoord.symm p)) ∂volume := by
      refine setLIntegral_congr_fun betaGammaCoord.open_target.measurableSet
        (fun p hp ↦ ?_)
      rcases hp with ⟨⟨hp0, hp1⟩, hp2⟩
      have hfac := gamma_beta_jacobian_factorization_ennreal ha hb hr hp0 hp1 hp2
      dsimp [hBG, hGG]
      rw [← hfac]
      ac_rfl
    _ = ∫⁻ q in betaGammaCoord.source, hGG q * f q ∂volume := by
      simpa using lintegral_comp_betaGammaCoord_symm (fun q ↦ hGG q * f q)
    _ = ∫⁻ q, betaGammaCoord.source.indicator (fun q ↦ hGG q * f q) q ∂volume := by
      rw [lintegral_indicator betaGammaCoord.open_source.measurableSet]
    _ = ∫⁻ q, hGG q * f q ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [betaGamma_source_density_ae_indicator a b r] with q hq
      by_cases hqs : q ∈ betaGammaCoord.source
      · simp [hqs]
      · have hqzero' : gammaPDF a r q.1 = 0 ∨ gammaPDF b r q.2 = 0 := by
          simpa [hqs] using hq
        have hqzero : hGG q = 0 := by
          rcases hqzero' with hqzero' | hqzero' <;> simp [hGG, hqzero']
        simp [hqs, hqzero]

/-- Convolution of Gamma measures with a common rate adds their shape
parameters. -/
theorem gammaMeasure_conv {a b r : ℝ} (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    gammaMeasure a r ∗ gammaMeasure b r = gammaMeasure (a + b) r := by
  let _ : IsProbabilityMeasure (betaMeasure a b) := isProbabilityMeasureBeta ha hb
  let _ : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  have hF : Measurable betaGammaCoord.symm := by
    change Measurable (fun p : ℝ × ℝ ↦ (p.1 * p.2, (1 - p.1) * p.2))
    fun_prop
  have hsum : Measurable (fun q : ℝ × ℝ ↦ q.1 + q.2) := by fun_prop
  unfold Measure.conv
  calc
    Measure.map (fun q : ℝ × ℝ ↦ q.1 + q.2)
        ((gammaMeasure a r).prod (gammaMeasure b r)) =
        Measure.map (fun q : ℝ × ℝ ↦ q.1 + q.2)
          (Measure.map betaGammaCoord.symm
            ((betaMeasure a b).prod (gammaMeasure (a + b) r))) := by
      rw [map_betaGammaCoord_symm_prod_beta_gamma ha hb hr]
    _ = Measure.map ((fun q : ℝ × ℝ ↦ q.1 + q.2) ∘ betaGammaCoord.symm)
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) :=
      Measure.map_map hsum hF
    _ = Measure.map Prod.snd
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) := by
      congr 1
      funext p
      simp only [Function.comp_apply, betaGammaCoord_symm_apply]
      ring
    _ = gammaMeasure (a + b) r := by simp

/-- The ratio coordinate used in the Gamma-to-Beta theorem. -/
def gammaRatio (q : ℝ × ℝ) : ℝ := q.1 / (q.1 + q.2)

/-- If the two coordinates are independent Gamma variables with a common
rate, their normalized first coordinate has the Beta law. -/
theorem map_gammaRatio_prod_gamma {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r) :
    Measure.map gammaRatio ((gammaMeasure a r).prod (gammaMeasure b r)) =
      betaMeasure a b := by
  let _ : IsProbabilityMeasure (gammaMeasure (a + b) r) :=
    isProbabilityMeasure_gammaMeasure (add_pos ha hb) hr
  let _ : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  have hF : Measurable betaGammaCoord.symm := by
    change Measurable (fun p : ℝ × ℝ ↦ (p.1 * p.2, (1 - p.1) * p.2))
    fun_prop
  have hratio : Measurable gammaRatio := by
    unfold gammaRatio
    fun_prop
  have hγzero : gammaMeasure (a + b) r ({0} : Set ℝ) = 0 := by
    apply (withDensity_absolutelyContinuous volume (gammaPDF (a + b) r))
    exact measure_singleton 0
  have hsne : ∀ᵐ p ∂((betaMeasure a b).prod (gammaMeasure (a + b) r)), p.2 ≠ 0 := by
    rw [Measure.ae_prod_iff_ae_ae (by measurability)]
    exact Filter.Eventually.of_forall fun _ ↦ by
      simpa [ae_iff] using hγzero
  calc
    Measure.map gammaRatio ((gammaMeasure a r).prod (gammaMeasure b r)) =
        Measure.map gammaRatio
          (Measure.map betaGammaCoord.symm
            ((betaMeasure a b).prod (gammaMeasure (a + b) r))) := by
      rw [map_betaGammaCoord_symm_prod_beta_gamma ha hb hr]
    _ = Measure.map (gammaRatio ∘ betaGammaCoord.symm)
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) :=
      Measure.map_map hratio hF
    _ = Measure.map Prod.fst
          ((betaMeasure a b).prod (gammaMeasure (a + b) r)) := by
      apply Measure.map_congr
      filter_upwards [hsne] with p hp
      change (p.1 * p.2) / (p.1 * p.2 + (1 - p.1) * p.2) = p.1
      rw [show p.1 * p.2 + (1 - p.1) * p.2 = p.2 by ring]
      exact (div_eq_iff hp).2 rfl
    _ = betaMeasure a b := by simp

/-! ## Squaring a standard Gaussian -/

private theorem sq_image_Ioi_zero :
    (fun x : ℝ ↦ x ^ 2) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change 0 < x at hx
    exact sq_pos_of_pos hx
  · intro hy
    refine ⟨Real.sqrt y, Real.sqrt_pos.2 hy, ?_⟩
    exact Real.sq_sqrt hy.le

private theorem sq_image_Iio_zero :
    (fun x : ℝ ↦ x ^ 2) '' Iio 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x < 0 at hx
    exact sq_pos_of_neg hx
  · intro hy
    refine ⟨-Real.sqrt y, neg_lt_zero.mpr (Real.sqrt_pos.2 hy), ?_⟩
    simpa using Real.sq_sqrt hy.le

private theorem injOn_sq_Ioi_zero : InjOn (fun x : ℝ ↦ x ^ 2) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  change x ^ 2 = y ^ 2 at hxy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with hxy | hxy
  · exact hxy
  · nlinarith

private theorem injOn_sq_Iio_zero : InjOn (fun x : ℝ ↦ x ^ 2) (Iio 0) := by
  intro x hx y hy hxy
  change x < 0 at hx
  change y < 0 at hy
  change x ^ 2 = y ^ 2 at hxy
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with hxy | hxy
  · exact hxy
  · nlinarith

private theorem hasDerivAt_sq (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ y ^ 2) (2 * x) x := by
  simpa using (hasDerivAt_pow 2 x)

/-- Positive-branch change of variables for squaring. -/
private theorem lintegral_sq_Ioi (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in Ioi (0 : ℝ), g y) =
      ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * x) * g (x ^ 2) := by
  calc
    (∫⁻ y in Ioi (0 : ℝ), g y) =
        ∫⁻ y in (fun x : ℝ ↦ x ^ 2) '' Ioi 0, g y := by
      rw [sq_image_Ioi_zero]
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal |2 * x| * g (x ^ 2) := by
      exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
        (fun x _ ↦ (hasDerivAt_sq x).hasDerivWithinAt) injOn_sq_Ioi_zero g
    _ = ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (2 * x) * g (x ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      rw [abs_of_pos (mul_pos (by norm_num) hx)]

/-- Negative-branch change of variables for squaring. -/
private theorem lintegral_sq_Iio (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in Ioi (0 : ℝ), g y) =
      ∫⁻ x in Iio (0 : ℝ), ENNReal.ofReal (-2 * x) * g (x ^ 2) := by
  calc
    (∫⁻ y in Ioi (0 : ℝ), g y) =
        ∫⁻ y in (fun x : ℝ ↦ x ^ 2) '' Iio 0, g y := by
      rw [sq_image_Iio_zero]
    _ = ∫⁻ x in Iio (0 : ℝ), ENNReal.ofReal |2 * x| * g (x ^ 2) := by
      exact lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Iio
        (fun x _ ↦ (hasDerivAt_sq x).hasDerivWithinAt) injOn_sq_Iio_zero g
    _ = ∫⁻ x in Iio (0 : ℝ), ENNReal.ofReal (-2 * x) * g (x ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Iio fun x hx ↦ ?_
      rw [abs_of_neg (mul_neg_of_pos_of_neg (by norm_num) hx)]
      congr 2
      ring

private def gaussianSqPosDensity (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (gaussianPDFReal 0 1 (Real.sqrt y) / (2 * Real.sqrt y))

private def gaussianSqNegDensity (y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal
    (gaussianPDFReal 0 1 (-Real.sqrt y) / (2 * Real.sqrt y))

private theorem measurable_gaussianSqPosDensity : Measurable gaussianSqPosDensity := by
  unfold gaussianSqPosDensity
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

private theorem measurable_gaussianSqNegDensity : Measurable gaussianSqNegDensity := by
  unfold gaussianSqNegDensity
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

private theorem lintegral_gaussian_sq_pos (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Ioi (0 : ℝ), gaussianPDF 0 1 x * f (x ^ 2)) =
      ∫⁻ y in Ioi (0 : ℝ), gaussianSqPosDensity y * f y := by
  conv_rhs => rw [lintegral_sq_Ioi]
  refine setLIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
  change 0 < x at hx
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) * f (x ^ 2) =
    ENNReal.ofReal (2 * x) *
      (ENNReal.ofReal
        (gaussianPDFReal 0 1 (Real.sqrt (x ^ 2)) /
          (2 * Real.sqrt (x ^ 2))) * f (x ^ 2))
  rw [Real.sqrt_sq hx.le]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (mul_pos (by norm_num) hx).le]
  congr 1
  apply congrArg ENNReal.ofReal
  field_simp [hx.ne']

private theorem lintegral_gaussian_sq_neg (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Iio (0 : ℝ), gaussianPDF 0 1 x * f (x ^ 2)) =
      ∫⁻ y in Ioi (0 : ℝ), gaussianSqNegDensity y * f y := by
  rw [lintegral_sq_Iio]
  refine setLIntegral_congr_fun measurableSet_Iio fun x hx ↦ ?_
  change x < 0 at hx
  change ENNReal.ofReal (gaussianPDFReal 0 1 x) * f (x ^ 2) =
    ENNReal.ofReal (-2 * x) *
      (ENNReal.ofReal
        (gaussianPDFReal 0 1 (-Real.sqrt (x ^ 2)) /
          (2 * Real.sqrt (x ^ 2))) * f (x ^ 2))
  rw [Real.sqrt_sq_eq_abs, abs_of_neg hx]
  have hmx : 0 < -2 * x := mul_pos_of_neg_of_neg (by norm_num) hx
  rw [← mul_assoc, ← ENNReal.ofReal_mul hmx.le]
  congr 1
  apply congrArg ENNReal.ofReal
  field_simp [hx.ne]

private theorem gaussianSqPosDensity_add_neg {y : ℝ} (hy : 0 < y) :
    gaussianSqPosDensity y + gaussianSqNegDensity y =
      gammaPDF (1 / 2) (1 / 2) y := by
  have hsqrt : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hp : 0 ≤ gaussianPDFReal 0 1 (Real.sqrt y) / (2 * Real.sqrt y) := by
    exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_nonneg (by norm_num) hsqrt.le)
  have hn : 0 ≤ gaussianPDFReal 0 1 (-Real.sqrt y) / (2 * Real.sqrt y) := by
    exact div_nonneg (gaussianPDFReal_nonneg _ _ _) (mul_nonneg (by norm_num) hsqrt.le)
  unfold gaussianSqPosDensity gaussianSqNegDensity gammaPDF
  rw [← ENNReal.ofReal_add hp hn]
  apply congrArg ENNReal.ofReal
  calc
    gaussianPDFReal 0 1 (Real.sqrt y) / (2 * Real.sqrt y) +
        gaussianPDFReal 0 1 (-Real.sqrt y) / (2 * Real.sqrt y) =
        (gaussianPDFReal 0 1 (Real.sqrt y) +
          gaussianPDFReal 0 1 (-Real.sqrt y)) / (2 * Real.sqrt y) := by
      field_simp [hsqrt.ne']
    _ = gammaPDFReal (1 / 2) (1 / 2) y :=
      gaussian_square_density_eq_gamma_half hy

/-- The square of a standard real Gaussian has the Gamma law with shape
`1/2` and rate `1/2`.  This is the chi-square-one identity, stated entirely
as an equality of measures. -/
theorem map_sq_gaussianReal_zero_one :
    Measure.map (fun x : ℝ ↦ x ^ 2) (gaussianReal 0 1) =
      gammaMeasure (1 / 2) (1 / 2) := by
  have hsq : Measurable (fun x : ℝ ↦ x ^ 2) := by fun_prop
  have hgauss : Measurable (gaussianPDF 0 1) := measurable_gaussianPDF 0 1
  have hgamma : Measurable (gammaPDF (1 / 2) (1 / 2)) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal (1 / 2) (1 / 2))
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0), gammaMeasure]
  apply Measure.ext_of_lintegral _
  intro f hf
  have hfc : Measurable (fun x : ℝ ↦ f (x ^ 2)) := hf.comp hsq
  rw [lintegral_map hf hsq,
    lintegral_withDensity_eq_lintegral_mul volume hgauss hfc,
    lintegral_withDensity_eq_lintegral_mul volume hgamma hf]
  change (∫⁻ x, gaussianPDF 0 1 x * f (x ^ 2) ∂volume) =
    ∫⁻ y, gammaPDF (1 / 2) (1 / 2) y * f y ∂volume
  calc
    (∫⁻ x, gaussianPDF 0 1 x * f (x ^ 2) ∂volume) =
        (∫⁻ x in Ioi (0 : ℝ), gaussianPDF 0 1 x * f (x ^ 2) ∂volume) +
        ∫⁻ x in Iio (0 : ℝ), gaussianPDF 0 1 x * f (x ^ 2) ∂volume := by
      rw [← lintegral_add_compl
        (fun x ↦ gaussianPDF 0 1 x * f (x ^ 2)) measurableSet_Ioi, compl_Ioi]
      congr 1
      exact setLIntegral_congr Iio_ae_eq_Iic.symm
    _ = (∫⁻ y in Ioi (0 : ℝ), gaussianSqPosDensity y * f y ∂volume) +
        ∫⁻ y in Ioi (0 : ℝ), gaussianSqNegDensity y * f y ∂volume := by
      rw [lintegral_gaussian_sq_pos f, lintegral_gaussian_sq_neg f]
    _ = ∫⁻ y in Ioi (0 : ℝ),
        (gaussianSqPosDensity y * f y + gaussianSqNegDensity y * f y) ∂volume := by
      symm
      exact lintegral_add_left
        (μ := volume.restrict (Ioi (0 : ℝ)))
        (measurable_gaussianSqPosDensity.fun_mul hf)
        (fun y ↦ gaussianSqNegDensity y * f y)
    _ = ∫⁻ y in Ioi (0 : ℝ),
        (gaussianSqPosDensity y + gaussianSqNegDensity y) * f y ∂volume := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun y _ ↦ ?_
      simp [mul_add, mul_comm]
    _ = ∫⁻ y in Ioi (0 : ℝ), gammaPDF (1 / 2) (1 / 2) y * f y ∂volume := by
      refine setLIntegral_congr_fun measurableSet_Ioi fun y hy ↦ ?_
      rw [gaussianSqPosDensity_add_neg hy]
    _ = ∫⁻ y, gammaPDF (1 / 2) (1 / 2) y * f y ∂volume := by
      symm
      calc
        (∫⁻ y, gammaPDF (1 / 2) (1 / 2) y * f y ∂volume) =
            (∫⁻ y in Ici (0 : ℝ), gammaPDF (1 / 2) (1 / 2) y * f y ∂volume) +
            ∫⁻ y in Iio (0 : ℝ), gammaPDF (1 / 2) (1 / 2) y * f y ∂volume := by
          rw [← lintegral_add_compl
            (fun y ↦ gammaPDF (1 / 2) (1 / 2) y * f y) measurableSet_Ici,
            compl_Ici]
        _ = (∫⁻ y in Ici (0 : ℝ), gammaPDF (1 / 2) (1 / 2) y * f y ∂volume) + 0 := by
          congr 1
          exact setLIntegral_eq_zero measurableSet_Iio fun y hy ↦ by
            simp [gammaPDF_of_neg hy]
        _ = ∫⁻ y in Ioi (0 : ℝ), gammaPDF (1 / 2) (1 / 2) y * f y ∂volume := by
          rw [add_zero]
          exact setLIntegral_congr Ioi_ae_eq_Ici.symm

/-! ## Random-variable interfaces -/

/-- A random variable with the standard real Gaussian law has a square with
the `Gamma(1/2,1/2)` law. -/
theorem HasLaw.sq_standardGaussian {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) P) :
    HasLaw (fun ω ↦ (X ω) ^ 2) (gammaMeasure (1 / 2) (1 / 2)) P := by
  have hsq : HasLaw (fun x : ℝ ↦ x ^ 2) (gammaMeasure (1 / 2) (1 / 2))
      (gaussianReal 0 1) :=
    { aemeasurable := (show Measurable (fun x : ℝ ↦ x ^ 2) by fun_prop).aemeasurable
      map_eq := map_sq_gaussianReal_zero_one }
  simpa using hsq.fun_comp hX

/-- Sums of independent common-rate Gamma random variables add the shapes. -/
theorem IndepFun.hasLaw_add_gamma {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : Ω → ℝ} {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hX : HasLaw X (gammaMeasure a r) P)
    (hY : HasLaw Y (gammaMeasure b r) P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω + Y ω) (gammaMeasure (a + b) r) P := by
  let _ : IsProbabilityMeasure (gammaMeasure a r) :=
    isProbabilityMeasure_gammaMeasure ha hr
  let _ : IsProbabilityMeasure (gammaMeasure b r) :=
    isProbabilityMeasure_gammaMeasure hb hr
  have h := hXY.hasLaw_fun_add hX hY
  rwa [gammaMeasure_conv ha hb hr] at h

/-- The normalized first coordinate of two independent common-rate Gamma
random variables has the Beta law. -/
theorem IndepFun.hasLaw_gammaRatio {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsFiniteMeasure P] {X Y : Ω → ℝ} {a b r : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hr : 0 < r)
    (hX : HasLaw X (gammaMeasure a r) P)
    (hY : HasLaw Y (gammaMeasure b r) P)
    (hXY : IndepFun X Y P) :
    HasLaw (fun ω ↦ X ω / (X ω + Y ω)) (betaMeasure a b) P := by
  have hjoint : HasLaw (fun ω ↦ (X ω, Y ω))
      ((gammaMeasure a r).prod (gammaMeasure b r)) P :=
    hXY.hasLaw_prod hX hY
  have hratio : HasLaw gammaRatio (betaMeasure a b)
      ((gammaMeasure a r).prod (gammaMeasure b r)) :=
    { aemeasurable :=
        (show Measurable gammaRatio by unfold gammaRatio; fun_prop).aemeasurable
      map_eq := map_gammaRatio_prod_gamma ha hb hr }
  simpa [gammaRatio] using hratio.fun_comp hjoint

end

end LogdetLean
