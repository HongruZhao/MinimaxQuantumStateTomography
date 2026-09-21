import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory

noncomputable section

/-!
# A reusable lower-tail Chernoff wrapper

The Grassmann overlap argument eventually supplies a Laplace-transform bound
for one real random variable.  This file keeps the generic probability step
separate from the matrix/Haar calculation: a bound on
`integral (exp (-s * X))` immediately bounds the lower-tail event.

No distributional or Haar fact is assumed here.
-/

/-- A lower-tail Chernoff bound stated directly from a negative Laplace
transform estimate.  This is the exact interface needed after the
Haar-overlap moment calculation. -/
theorem measure_lowerTail_le_exp_of_laplace_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega -> Real) (a s B : Real)
    (hs : 0 <= s)
    (h_integrable :
      Integrable (fun omega => Real.exp ((-s) * X omega)) mu)
    (h_laplace :
      (∫ omega, Real.exp ((-s) * X omega) ∂mu) <=
        Real.exp B) :
    mu.real {omega | X omega <= a} <= Real.exp (s * a + B) := by
  have h_mgf : mgf X mu (-s) <= Real.exp B := by
    simpa only [mgf] using h_laplace
  calc
    mu.real {omega | X omega <= a}
        <= Real.exp (-(-s) * a) * mgf X mu (-s) :=
      measure_le_le_exp_mul_mgf a (neg_nonpos.mpr hs) h_integrable
    _ <= Real.exp (s * a) * Real.exp B := by
      simpa only [neg_neg] using
        mul_le_mul_of_nonneg_left h_mgf (Real.exp_nonneg (s * a))
    _ = Real.exp (s * a + B) := (Real.exp_add (s * a) B).symm

/-- The same wrapper when the Laplace estimate has already been packaged as
an `mgf` inequality. -/
theorem measure_lowerTail_le_exp_of_mgf_bound
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (X : Omega -> Real) (a s B : Real)
    (hs : 0 <= s)
    (h_integrable :
      Integrable (fun omega => Real.exp ((-s) * X omega)) mu)
    (h_mgf : mgf X mu (-s) <= Real.exp B) :
    mu.real {omega | X omega <= a} <= Real.exp (s * a + B) := by
  apply measure_lowerTail_le_exp_of_laplace_bound mu X a s B hs h_integrable
  simpa only [mgf] using h_mgf

/-- The elementary logarithmic estimate used to simplify the exact
Hayden--Leung--Winter exponent to the quadratic Lowe--Nayak exponent. -/
theorem add_log_one_sub_le_neg_half_sq
    {t : Real} (ht_nonneg : 0 <= t) (ht_lt_one : t < 1) :
    t + Real.log (1 - t) <= -(t ^ 2) / 2 := by
  have h_abs : |t| < 1 := by
    simpa only [abs_of_nonneg ht_nonneg] using ht_lt_one
  have h_series := Real.hasSum_pow_div_log_of_abs_lt_one h_abs
  have h_partial :
      (∑ n ∈ Finset.range 2, t ^ (n + 1) / (n + 1)) <=
        ∑' n : Nat, t ^ (n + 1) / (n + 1) :=
    h_series.summable.sum_le_tsum (Finset.range 2) (by
      intro n hn
      positivity)
  rw [h_series.tsum_eq] at h_partial
  norm_num [Finset.sum_range_succ] at h_partial
  nlinarith

/-- Multiplying the logarithmic estimate by a nonnegative rank product and
using monotonicity of `exp` gives the usual quadratic lower-tail exponent. -/
theorem exp_mul_add_log_one_sub_le_quadratic
    {r t : Real} (hr_nonneg : 0 <= r)
    (ht_nonneg : 0 <= t) (ht_lt_one : t < 1) :
    Real.exp (r * (t + Real.log (1 - t))) <=
      Real.exp (-(r * t ^ 2) / 2) := by
  apply Real.exp_le_exp.mpr
  have hlog := add_log_one_sub_le_neg_half_sq ht_nonneg ht_lt_one
  have hmul := mul_le_mul_of_nonneg_left hlog hr_nonneg
  nlinarith

/-- The exact `t = 1/4` exponent used by the canonical Grassmann overlap
tail. -/
theorem exp_hlw_quarter_le_lownayak_quarter
    {r : Real} (hr_nonneg : 0 <= r) :
    Real.exp (r * ((1 : Real) / 4 + Real.log (1 - (1 : Real) / 4))) <=
      Real.exp (-r / 32) := by
  have h := exp_mul_add_log_one_sub_le_quadratic
    hr_nonneg (by norm_num : (0 : Real) <= 1 / 4)
      (by norm_num : (1 : Real) / 4 < 1)
  convert h using 1 <;> ring_nf

end

end TomographyOracleCore
