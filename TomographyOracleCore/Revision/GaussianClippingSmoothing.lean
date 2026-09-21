import TomographyOracleCore.Revision.GaussianReflection
import TomographyOracleCore.Revision.QuadraticLogIntegrability

namespace TomographyOracleCore.Revision.GaussianClippingSmoothing

open MeasureTheory ProbabilityTheory GaussianChangeOfMeasure GaussianPairPosterior
open GaussianMarginalMoments GaussianReflection ClippingLogCalculus ClippingLogSmoothing
open QuadraticLogIntegrability
open TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
open scoped BigOperators NNReal
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem min_mean_fourth_le_posterior_min (x m : ι → ℝ) (v : ℝ≥0) (lambda : ℝ) :
    min 1 (lambda ^ 2 * marginal x m ^ 4) ≤
      4 * ∫ z, min 1 ((lambda * pairMarginal x z) ^ 2) ∂gaussianPairLaw m v := by
  let B := min 1 (lambda ^ 2 * marginal x m ^ 4)
  let G := marginalGood x m ×ˢ marginalGood x m
  have hG : MeasurableSet G := (measurableSet_marginalGood x m).prod (measurableSet_marginalGood x m)
  have hB : 0 ≤ B := le_min (by norm_num) (mul_nonneg (sq_nonneg _) (by positivity))
  have hi := integrable_min_one_sq (gaussianPairLaw m v) (fun z => lambda * pairMarginal x z)
    ((integrable_pairMarginal x m v).const_mul lambda).aestronglyMeasurable
  have hpoint : ∀ z, G.indicator (fun _ => B) z ≤ min 1 ((lambda * pairMarginal x z) ^ 2) := by
    intro z
    by_cases hz : z ∈ G
    · rw [Set.indicator_of_mem hz]
      apply min_le_min le_rfl
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_left (pairMarginal_sq_on_good x m z hz) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hz]
      exact le_min (by norm_num) (sq_nonneg _)
  have hint := integral_mono ((integrable_const B).indicator hG) hi hpoint
  rw [integral_indicator_const _ hG, smul_eq_mul] at hint
  have hp := gaussian_pair_good_probability x m v
  change (1 / 4 : ℝ) ≤ (gaussianPairLaw m v).real G at hp
  have hpB := mul_le_mul_of_nonneg_right hp hB
  change B ≤ _
  linarith

theorem scalar_min_second_moment (lambda b r : ℝ) :
    2 * min 1 (lambda ^ 2 * (b ^ 2 + r) ^ 2) ≤
      4 * min 1 (lambda ^ 2 * b ^ 4) + 4 * lambda ^ 2 * r ^ 2 := by
  have hs : lambda ^ 2 * (b ^ 2 + r) ^ 2 ≤
      2 * lambda ^ 2 * b ^ 4 + 2 * lambda ^ 2 * r ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg lambda) (sq_nonneg (b ^ 2 - r))]
  by_cases hsmall : lambda ^ 2 * b ^ 4 ≤ 1
  · rw [min_eq_right hsmall]
    have := min_le_right (1 : ℝ) (lambda ^ 2 * (b ^ 2 + r) ^ 2)
    linarith
  · rw [min_eq_left (le_of_not_ge hsmall)]
    have := min_le_left (1 : ℝ) (lambda ^ 2 * (b ^ 2 + r) ^ 2)
    nlinarith [mul_nonneg (sq_nonneg lambda) (sq_nonneg r)]

/-- Gaussian smoothing for the clipped quadratic observable, using the
actual posterior measures and the repaired elementary clipping inequality.
The parameter lambda can have either sign. -/
theorem gaussian_clipping_smoothing (x m : ι → ℝ) (v : ℝ≥0) (lambda : ℝ) :
    clippedPsi (lambda * marginal x m ^ 2) ≤
      (∫ z, quadraticLog (smoothingCoefficient 16) (lambda * pairMarginal x z)
        ∂gaussianPairLaw m v) +
      4 * lambda ^ 2 * (v : ℝ) ^ 2 * (∑ i, x i ^ 2) ^ 2 := by
  have hZ := (integrable_pairMarginal x m v).const_mul lambda
  have hZ2 : Integrable (fun z => (lambda * pairMarginal x z) ^ 2) (gaussianPairLaw m v) := by
    simpa only [mul_pow] using (integrable_pairMarginal_sq x m v).const_mul (lambda ^ 2)
  have hsmooth := clipped_integral_le_log_integral_add_min (gaussianPairLaw m v)
    (fun z => lambda * pairMarginal x z) hZ hZ2
  rw [integral_const_mul, integral_pairMarginal] at hsmooth
  have hmoment : (∫ z, (lambda * pairMarginal x z) ^ 2 ∂gaussianPairLaw m v) =
      lambda ^ 2 * (marginal x m ^ 2 + (v : ℝ) * ∑ i, x i ^ 2) ^ 2 := by
    simp only [mul_pow]
    rw [integral_const_mul, integral_pairMarginal_sq]
  rw [hmoment] at hsmooth
  have hmin := min_mean_fourth_le_posterior_min x m v lambda
  have hscalar := scalar_min_second_moment lambda (marginal x m) ((v : ℝ) * ∑ i, x i ^ 2)
  have hlog := integrable_logQuadratic (gaussianPairLaw m v) _ hZ hZ2
  have htrunc := integrable_min_one_sq (gaussianPairLaw m v) _ hZ.aestronglyMeasurable
  have hbig := integrable_quadraticLog (gaussianPairLaw m v) (smoothingCoefficient 16)
    (smoothingCoefficient_ge_one (by norm_num)) _ hZ hZ2
  have habsorb := integral_mono (hlog.add (htrunc.const_mul 16)) hbig
    (fun z => logQuadratic_add_min_le_log 16 (lambda * pairMarginal x z) (by norm_num))
  simp only [Pi.add_apply] at habsorb
  rw [integral_add hlog (htrunc.const_mul 16), integral_const_mul] at habsorb
  nlinarith

end
end TomographyOracleCore.Revision.GaussianClippingSmoothing
