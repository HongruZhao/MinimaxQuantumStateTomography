import TomographyOracleCore.Revision.GaussianChangeOfMeasure
import TomographyOracleCore.Revision.LogDensityRelativeEntropy

namespace TomographyOracleCore.Revision.GaussianPairPosterior

open MeasureTheory ProbabilityTheory InformationTheory GaussianChangeOfMeasure
open LogDensityRelativeEntropy
open scoped BigOperators ENNReal NNReal
noncomputable section

variable {ι : Type*} [Fintype ι]

def gaussianPairLaw (m : ι → ℝ) (v : ℝ≥0) : Measure ((ι → ℝ) × (ι → ℝ)) :=
  (gaussianVectorLaw m v).prod (gaussianVectorLaw m v)

instance (m : ι → ℝ) (v : ℝ≥0) : IsProbabilityMeasure (gaussianPairLaw m v) := by
  unfold gaussianPairLaw
  infer_instance

def gaussianPairShiftLogDensity (m : ι → ℝ) (v : ℝ≥0)
    (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  gaussianVectorShiftLogDensity m v z.1 + gaussianVectorShiftLogDensity m v z.2

theorem gaussianPair_shift_density (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    gaussianPairLaw m v = (gaussianPairLaw (fun _ : ι => 0) v).withDensity
      (fun z => ENNReal.ofReal (Real.exp (gaussianPairShiftLogDensity m v z))) := by
  unfold gaussianPairLaw
  rw [gaussianVector_shift_density m v hv]
  rw [prod_withDensity (by unfold gaussianVectorShiftLogDensity gaussianShiftLogDensity; fun_prop)
    (by unfold gaussianVectorShiftLogDensity gaussianShiftLogDensity; fun_prop)]
  congr 1
  funext z
  rw [gaussianPairShiftLogDensity, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

theorem integrable_gaussianPairShiftLogDensity (m : ι → ℝ) (v : ℝ≥0) :
    Integrable (gaussianPairShiftLogDensity m v) (gaussianPairLaw m v) :=
  ((integrable_gaussianVectorShiftLogDensity m v).comp_fst _).add
    ((integrable_gaussianVectorShiftLogDensity m v).comp_snd _)

theorem integral_gaussianPairShiftLogDensity (m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, gaussianPairShiftLogDensity m v z ∂gaussianPairLaw m v) =
      (∑ i, m i ^ 2) / (v : ℝ) := by
  unfold gaussianPairShiftLogDensity gaussianPairLaw
  rw [integral_add ((integrable_gaussianVectorShiftLogDensity m v).comp_fst _)
    ((integrable_gaussianVectorShiftLogDensity m v).comp_snd _),
    integral_fun_fst, integral_fun_snd, probReal_univ, one_smul,
    integral_gaussianVectorShiftLogDensity]
  ring

theorem gaussianPair_kl_finite (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    klDiv (gaussianPairLaw m v) (gaussianPairLaw (fun _ : ι => 0) v) ≠ ⊤ := by
  apply logDensity_kl_finite _ _ (gaussianPairShiftLogDensity m v)
    (by unfold gaussianPairShiftLogDensity gaussianVectorShiftLogDensity gaussianShiftLogDensity
        fun_prop) (gaussianPair_shift_density m v hv)
  exact integrable_gaussianPairShiftLogDensity m v

/-- The product posterior used in the covariance argument has exactly this
relative entropy; no Gaussian formula is assumed. -/
theorem gaussianPair_kl (m : ι → ℝ) (v : ℝ≥0) (hv : v ≠ 0) :
    (klDiv (gaussianPairLaw m v) (gaussianPairLaw (fun _ : ι => 0) v)).toReal =
      (∑ i, m i ^ 2) / (v : ℝ) := by
  rw [logDensity_kl _ _ (gaussianPairShiftLogDensity m v)
    (by unfold gaussianPairShiftLogDensity gaussianVectorShiftLogDensity gaussianShiftLogDensity
        fun_prop) (gaussianPair_shift_density m v hv),
    integral_gaussianPairShiftLogDensity]

end
end TomographyOracleCore.Revision.GaussianPairPosterior
