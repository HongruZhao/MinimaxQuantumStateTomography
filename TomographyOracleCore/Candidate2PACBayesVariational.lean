import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TomographyOracleCore.GrassmannHaarJensen

/-!
# A finite-KL PAC--Bayes variational inequality

This module isolates the deterministic change-of-measure step used in
PAC--Bayes arguments.  The proof tilts the reference probability by `exp f`
and applies Gibbs' inequality to the KL divergence from the posterior to that
tilted probability.

All finiteness assumptions are explicit.  In particular, the integral of `f`
under the posterior and the exponential integral under the reference measure
must exist, and the log-likelihood ratio must be integrable.  The latter is
equivalent to finiteness of Mathlib's extended-real `klDiv` once absolute
continuity is known.
-/

namespace TomographyOracleCore

open MeasureTheory Real
open InformationTheory

noncomputable section

/-- The Donsker--Varadhan / PAC--Bayes change-of-measure inequality, stated
with the primitive absolute-continuity and log-likelihood integrability
hypotheses used by Mathlib's KL API.  `Integrable` includes the required
almost-everywhere measurability. -/
theorem integral_le_toReal_klDiv_add_log_integral_exp_of_ac
    {Omega : Type*} [MeasurableSpace Omega]
    (rho mu : Measure Omega)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (f : Omega -> Real)
    (hrhoMu : rho ≪ mu)
    (hfRho : Integrable f rho)
    (hllr : Integrable (llr rho mu) rho)
    (hexpMu : Integrable (fun omega => Real.exp (f omega)) mu) :
    (∫ omega, f omega ∂rho) <=
      (klDiv rho mu).toReal +
        Real.log (∫ omega, Real.exp (f omega) ∂mu) := by
  let _ : IsProbabilityMeasure (mu.tilted f) :=
    isProbabilityMeasure_tilted hexpMu
  have hrhoTilt : rho ≪ mu.tilted f :=
    hrhoMu.trans (absolutelyContinuous_tilted hexpMu)
  have hllrTilt : Integrable (llr rho (mu.tilted f)) rho :=
    integrable_llr_tilted_right hrhoMu hfRho hllr hexpMu
  have hGibbs : 0 <= ∫ omega, llr rho (mu.tilted f) omega ∂rho := by
    simpa using
      (integral_llr_add_sub_measure_univ_nonneg hrhoTilt hllrTilt)
  rw [integral_llr_tilted_right hrhoMu hfRho hexpMu hllr] at hGibbs
  have hKL :
      (klDiv rho mu).toReal = ∫ omega, llr rho mu omega ∂rho :=
    toReal_klDiv_of_measure_eq hrhoMu (by simp)
  rw [hKL]
  linarith

/-- Finite-KL form of the deterministic PAC--Bayes inequality.  Finiteness of
`klDiv` supplies both absolute continuity and integrability of the
log-likelihood ratio. -/
theorem integral_le_toReal_klDiv_add_log_integral_exp
    {Omega : Type*} [MeasurableSpace Omega]
    (rho mu : Measure Omega)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (f : Omega -> Real)
    (hfRho : Integrable f rho)
    (hexpMu : Integrable (fun omega => Real.exp (f omega)) mu)
    (hKLFinite : klDiv rho mu ≠ ⊤) :
    (∫ omega, f omega ∂rho) <=
      (klDiv rho mu).toReal +
        Real.log (∫ omega, Real.exp (f omega) ∂mu) := by
  rcases klDiv_ne_top_iff.mp hKLFinite with ⟨hrhoMu, hllr⟩
  exact integral_le_toReal_klDiv_add_log_integral_exp_of_ac
    rho mu f hrhoMu hfRho hllr hexpMu

/-- Exponential, one-sample form of the PAC--Bayes inequality.  It is often
the most convenient input to a later Markov or Chernoff argument. -/
theorem exp_integral_sub_toReal_klDiv_le_integral_exp
    {Omega : Type*} [MeasurableSpace Omega]
    (rho mu : Measure Omega)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (f : Omega -> Real)
    (hfRho : Integrable f rho)
    (hexpMu : Integrable (fun omega => Real.exp (f omega)) mu)
    (hKLFinite : klDiv rho mu ≠ ⊤) :
    Real.exp ((∫ omega, f omega ∂rho) - (klDiv rho mu).toReal) <=
      ∫ omega, Real.exp (f omega) ∂mu := by
  have h := integral_le_toReal_klDiv_add_log_integral_exp
    rho mu f hfRho hexpMu hKLFinite
  have hlog :
      (∫ omega, f omega ∂rho) - (klDiv rho mu).toReal <=
        Real.log (∫ omega, Real.exp (f omega) ∂mu) := by
    linarith
  have hexp := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (integral_exp_pos hexpMu)] at hexp
  exact hexp

/-- Temperature-scaled PAC--Bayes inequality.  For positive `lambda`, the
posterior expectation is controlled by KL divided by `lambda` plus the
log-moment-generating function under the reference probability. -/
theorem integral_le_pacBayes_scaled
    {Omega : Type*} [MeasurableSpace Omega]
    (rho mu : Measure Omega)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (f : Omega -> Real) (lambda : Real)
    (hlambda : 0 < lambda)
    (hfRho : Integrable f rho)
    (hexpMu : Integrable
      (fun omega => Real.exp (lambda * f omega)) mu)
    (hKLFinite : klDiv rho mu ≠ ⊤) :
    (∫ omega, f omega ∂rho) <=
      ((klDiv rho mu).toReal +
        Real.log (∫ omega, Real.exp (lambda * f omega) ∂mu)) / lambda := by
  have h := integral_le_toReal_klDiv_add_log_integral_exp
    rho mu (fun omega => lambda * f omega)
      (hfRho.const_mul lambda) hexpMu hKLFinite
  rw [integral_const_mul] at h
  exact (le_div_iff₀ hlambda).2 (by simpa [mul_comm] using h)

/-- For one random sample, a unit prior exponential moment makes the bad
samplewise prior-moment event have probability at most `delta`.  This is the
Markov half of the usual one-sample PAC--Bayes statement.  Product
integrability explicitly supplies both Fubini and measurability of the inner
prior integral. -/
theorem oneSample_priorExpMoment_tail
    {Sample Parameter : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Parameter]
    (sampleLaw : Measure Sample) (prior : Measure Parameter)
    [IsProbabilityMeasure sampleLaw] [IsProbabilityMeasure prior]
    (score : Sample -> Parameter -> Real)
    (hExp : Integrable
      (fun z : Sample × Parameter => Real.exp (score z.1 z.2))
      (sampleLaw.prod prior))
    (hUnitMoment :
      (∫ z, Real.exp (score z.1 z.2) ∂sampleLaw.prod prior) <= 1)
    {delta : Real} (hdelta : 0 < delta) :
    sampleLaw.real
        {sample | 1 / delta <=
          ∫ parameter, Real.exp (score sample parameter) ∂prior} <= delta := by
  have hInner : Integrable
      (fun sample =>
        ∫ parameter, Real.exp (score sample parameter) ∂prior) sampleLaw :=
    hExp.integral_prod_left
  have hInnerNonneg :
      ∀ᵐ sample ∂sampleLaw,
        0 <= ∫ parameter, Real.exp (score sample parameter) ∂prior :=
    Filter.Eventually.of_forall fun sample =>
      integral_nonneg fun parameter => (Real.exp_pos _).le
  have hMarkov := mul_meas_ge_le_integral_of_nonneg
    hInnerNonneg hInner (1 / delta)
  have hFubini := integral_prod
    (fun z : Sample × Parameter => Real.exp (score z.1 z.2)) hExp
  rw [← hFubini] at hMarkov
  have hScaled :
      (1 / delta) * sampleLaw.real
          {sample | 1 / delta <=
            ∫ parameter, Real.exp (score sample parameter) ∂prior} <= 1 :=
    hMarkov.trans hUnitMoment
  calc
    sampleLaw.real
        {sample | 1 / delta <=
          ∫ parameter, Real.exp (score sample parameter) ∂prior} =
        delta * ((1 / delta) * sampleLaw.real
          {sample | 1 / delta <=
            ∫ parameter, Real.exp (score sample parameter) ∂prior}) := by
      field_simp [hdelta.ne']
    _ <= delta * 1 := mul_le_mul_of_nonneg_left hScaled hdelta.le
    _ = delta := mul_one delta

/-- On every sample whose prior exponential moment is below the Markov
threshold, every finite-KL posterior satisfying the displayed sectionwise
integrability assumptions obeys the corresponding PAC--Bayes bound.  This
pointwise formulation avoids imposing any unnecessary measurability condition
on a data-dependent posterior. -/
theorem oneSample_pacBayes_of_priorExpMoment_le
    {Sample Parameter : Type*}
    [MeasurableSpace Sample] [MeasurableSpace Parameter]
    (prior posterior : Measure Parameter)
    [IsProbabilityMeasure prior] [IsProbabilityMeasure posterior]
    (score : Sample -> Parameter -> Real) (sample : Sample)
    {delta : Real} (hdelta : 0 < delta)
    (hscorePosterior : Integrable (score sample) posterior)
    (hexpPrior : Integrable
      (fun parameter => Real.exp (score sample parameter)) prior)
    (hGood :
      (∫ parameter, Real.exp (score sample parameter) ∂prior) <= 1 / delta)
    (hKLFinite : klDiv posterior prior ≠ ⊤) :
    (∫ parameter, score sample parameter ∂posterior) <=
      (klDiv posterior prior).toReal + Real.log (1 / delta) := by
  have hDV := integral_le_toReal_klDiv_add_log_integral_exp
    posterior prior (score sample) hscorePosterior hexpPrior hKLFinite
  have hLog :
      Real.log (∫ parameter, Real.exp (score sample parameter) ∂prior) <=
        Real.log (1 / delta) :=
    (Real.log_le_log_iff (integral_exp_pos hexpPrior)
      (one_div_pos.mpr hdelta)).2 hGood
  exact hDV.trans (add_le_add le_rfl hLog)

end

end TomographyOracleCore
