import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Tactic

namespace TomographyOracleCore.Revision.GaussianChangeOfMeasure

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal NNReal
noncomputable section

/-- Coordinate density formulas tensorize for actual finite product measures. -/
theorem pi_eq_withDensity_of_coordinates
    {ι : Type*} [Fintype ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (mu nu : (i : ι) → Measure (X i)) [∀ i, SigmaFinite (mu i)] [∀ i, SigmaFinite (nu i)]
    (f : (i : ι) → X i → ℝ) (hf : ∀ i, Integrable (f i) (mu i))
    (hnonneg : ∀ i x, 0 ≤ f i x)
    (hdensity : ∀ i, nu i = (mu i).withDensity (fun x => ENNReal.ofReal (f i x))) :
    Measure.pi nu = (Measure.pi mu).withDensity (fun x => ENNReal.ofReal (∏ i, f i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    Measure.restrict_pi_pi]
  have hprod : Integrable (fun x : (i : ι) → X i => ∏ i, f i (x i))
      (Measure.pi (fun i => (mu i).restrict (s i))) :=
    Integrable.fintype_prod_dep (fun i => (hf i).restrict)
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (ae_of_all _ fun x => Finset.prod_nonneg fun i _ => hnonneg i (x i)),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg]
  · apply Finset.prod_congr rfl
    intro i _
    rw [hdensity i, withDensity_apply _ (hs i)]
    exact ofReal_integral_eq_lintegral_ofReal (hf i).restrict (ae_of_all _ (hnonneg i))
  · intro i _
    exact integral_nonneg (hnonneg i)

def gaussianShiftLogDensity (m : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  m * x / (v : ℝ) - m ^ 2 / (2 * (v : ℝ))

/-- Completing the square gives the literal Gaussian density ratio. -/
theorem gaussianReal_shift_density (m : ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianReal m v = (gaussianReal 0 v).withDensity
      (fun x => ENNReal.ofReal (Real.exp (gaussianShiftLogDensity m v x))) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_mul volume (measurable_gaussianPDF 0 v) (by unfold gaussianShiftLogDensity; fun_prop)]
  congr 1
  funext x
  change ENNReal.ofReal (gaussianPDFReal m v x) =
    ENNReal.ofReal (gaussianPDFReal 0 v x) * ENNReal.ofReal (Real.exp (gaussianShiftLogDensity m v x))
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 v x)]
  congr 1
  unfold gaussianPDFReal gaussianShiftLogDensity
  simp only [mul_assoc, ← Real.exp_add]
  congr 2
  have hvR : (v : ℝ) ≠ 0 := by exact_mod_cast hv
  field_simp
  ring

theorem integrable_gaussianShiftDensity (m : ℝ) (v : ℝ≥0) :
    Integrable (fun x => Real.exp (gaussianShiftLogDensity m v x)) (gaussianReal 0 v) := by
  have h := (integrable_exp_mul_gaussianReal (μ := 0) (v := v) (m / (v : ℝ))).mul_const
    (Real.exp (-m ^ 2 / (2 * (v : ℝ))))
  convert h using 1
  funext x
  rw [← Real.exp_add]
  congr 1
  unfold gaussianShiftLogDensity
  ring

def gaussianVectorLaw {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ℝ≥0) : Measure (ι → ℝ) :=
  Measure.pi (fun i => gaussianReal (m i) v)

instance {ι : Type*} [Fintype ι] (m : ι → ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianVectorLaw m v) := by unfold gaussianVectorLaw; infer_instance

def gaussianVectorShiftLogDensity {ι : Type*} [Fintype ι] (m : ι → ℝ)
    (v : ℝ≥0) (x : ι → ℝ) : ℝ := ∑ i, gaussianShiftLogDensity (m i) v (x i)

theorem gaussianVector_shift_density {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianVectorLaw m v = (gaussianVectorLaw (fun _ : ι => 0) v).withDensity
      (fun x => ENNReal.ofReal (Real.exp (gaussianVectorShiftLogDensity m v x))) := by
  rw [gaussianVectorLaw, gaussianVectorLaw]
  have h := pi_eq_withDensity_of_coordinates (fun _ : ι => gaussianReal 0 v)
    (fun i => gaussianReal (m i) v) (fun i x => Real.exp (gaussianShiftLogDensity (m i) v x))
    (fun i => integrable_gaussianShiftDensity (m i) v) (fun _ _ => (Real.exp_pos _).le)
    (fun i => gaussianReal_shift_density (m i) v hv)
  simpa only [gaussianVectorShiftLogDensity, Real.exp_sum] using h

theorem gaussianVector_absolutelyContinuous {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianVectorLaw m v ≪ gaussianVectorLaw (fun _ : ι => 0) v := by
  rw [gaussianVector_shift_density m v hv]
  exact withDensity_absolutelyContinuous _ _

theorem integrable_gaussianVectorShiftLogDensity {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (gaussianVectorShiftLogDensity m v) (gaussianVectorLaw m v) := by
  unfold gaussianVectorShiftLogDensity gaussianVectorLaw gaussianShiftLogDensity
  apply integrable_finsetSum
  intro i _
  exact ((integrable_eval (IsGaussian.integrable_id (μ := gaussianReal (m i) v))).const_mul
    (m i)).div_const (v : ℝ) |>.sub (integrable_const _)

theorem integral_gaussianVectorShiftLogDensity {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) :
    (∫ x, gaussianVectorShiftLogDensity m v x ∂gaussianVectorLaw m v) =
      (∑ i, m i ^ 2) / (2 * (v : ℝ)) := by
  unfold gaussianVectorShiftLogDensity gaussianVectorLaw gaussianShiftLogDensity
  rw [integral_finsetSum]
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    have hi : Integrable (fun x : ι → ℝ => m i * x i / (v : ℝ))
        (Measure.pi (fun j => gaussianReal (m j) v)) :=
      ((integrable_eval (IsGaussian.integrable_id (μ := gaussianReal (m i) v))).const_mul
        (m i)).div_const (v : ℝ)
    rw [integral_sub hi (integrable_const _), integral_div, integral_const_mul,
      integral_eval, integral_id_gaussianReal, integral_const, probReal_univ,
      smul_eq_mul, one_mul]
    ring
  · intro i _
    exact ((integrable_eval (IsGaussian.integrable_id (μ := gaussianReal (m i) v))).const_mul
      (m i)).div_const (v : ℝ) |>.sub (integrable_const _)

theorem gaussianVector_llr {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    llr (gaussianVectorLaw m v) (gaussianVectorLaw (fun _ : ι => 0) v)
      =ᵐ[gaussianVectorLaw m v] gaussianVectorShiftLogDensity m v := by
  have hac := gaussianVector_absolutelyContinuous m v hv
  have hrn : (gaussianVectorLaw m v).rnDeriv (gaussianVectorLaw (fun _ : ι => 0) v)
      =ᵐ[gaussianVectorLaw (fun _ : ι => 0) v]
        (fun x => ENNReal.ofReal (Real.exp (gaussianVectorShiftLogDensity m v x))) := by
    rw [gaussianVector_shift_density m v hv]
    apply Measure.rnDeriv_withDensity
    unfold gaussianVectorShiftLogDensity gaussianShiftLogDensity
    fun_prop
  filter_upwards [hac.ae_le hrn] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

theorem gaussianVector_kl_finite {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianVectorLaw m v) (gaussianVectorLaw (fun _ : ι => 0) v) ≠ ⊤ := by
  apply klDiv_ne_top (gaussianVector_absolutelyContinuous m v hv)
  exact (integrable_gaussianVectorShiftLogDensity m v).congr (gaussianVector_llr m v hv).symm

/-- The Gaussian relative entropy is derived from the actual density,
including all absolute-continuity and integrability obligations. -/
theorem gaussianVector_kl {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (klDiv (gaussianVectorLaw m v) (gaussianVectorLaw (fun _ : ι => 0) v)).toReal =
      (∑ i, m i ^ 2) / (2 * (v : ℝ)) := by
  rw [toReal_klDiv_of_measure_eq (gaussianVector_absolutelyContinuous m v hv) (by simp),
    integral_congr_ae (gaussianVector_llr m v hv), integral_gaussianVectorShiftLogDensity]

end
end TomographyOracleCore.Revision.GaussianChangeOfMeasure
