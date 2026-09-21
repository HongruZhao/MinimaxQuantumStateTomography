import TomographyOracleCore.Candidate2PACBayesVariational

namespace TomographyOracleCore.Revision.LogDensityRelativeEntropy

open MeasureTheory InformationTheory
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

theorem logDensity_llr (rho mu : Measure Ω) [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (ell : Ω → ℝ) (hell : Measurable ell)
    (hdensity : rho = mu.withDensity (fun x => ENNReal.ofReal (Real.exp (ell x)))) :
    llr rho mu =ᵐ[rho] ell := by
  have hac : rho ≪ mu := by rw [hdensity]; exact withDensity_absolutelyContinuous _ _
  have hrn : rho.rnDeriv mu =ᵐ[mu] (fun x => ENNReal.ofReal (Real.exp (ell x))) := by
    rw [hdensity]
    exact Measure.rnDeriv_withDensity _ (hell.exp.ennreal_ofReal)
  filter_upwards [hac.ae_le hrn] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal (Real.exp_pos _).le, Real.log_exp]

theorem logDensity_kl_finite (rho mu : Measure Ω)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (ell : Ω → ℝ) (hell : Measurable ell)
    (hdensity : rho = mu.withDensity (fun x => ENNReal.ofReal (Real.exp (ell x))))
    (hi : Integrable ell rho) : klDiv rho mu ≠ ⊤ := by
  have hac : rho ≪ mu := by rw [hdensity]; exact withDensity_absolutelyContinuous _ _
  exact klDiv_ne_top hac (hi.congr (logDensity_llr rho mu ell hell hdensity).symm)

theorem logDensity_kl (rho mu : Measure Ω)
    [IsProbabilityMeasure rho] [IsProbabilityMeasure mu]
    (ell : Ω → ℝ) (hell : Measurable ell)
    (hdensity : rho = mu.withDensity (fun x => ENNReal.ofReal (Real.exp (ell x)))) :
    (klDiv rho mu).toReal = ∫ x, ell x ∂rho := by
  have hac : rho ≪ mu := by rw [hdensity]; exact withDensity_absolutelyContinuous _ _
  rw [toReal_klDiv_of_measure_eq hac (by simp)]
  exact integral_congr_ae (logDensity_llr rho mu ell hell hdensity)

end
end TomographyOracleCore.Revision.LogDensityRelativeEntropy
