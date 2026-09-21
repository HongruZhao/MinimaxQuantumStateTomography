import TomographyOracleCore.Revision.GaussianPairPosterior
import Mathlib.Probability.Moments.Variance

namespace TomographyOracleCore.Revision.GaussianMarginalMoments

open MeasureTheory ProbabilityTheory GaussianChangeOfMeasure GaussianPairPosterior
open scoped BigOperators ENNReal NNReal
noncomputable section

variable {ι : Type*} [Fintype ι]

def marginal (x theta : ι → ℝ) : ℝ := ∑ i, x i * theta i

theorem memLp_marginal (x m : ι → ℝ) (v : ℝ≥0) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (marginal x) p (gaussianVectorLaw m v) := by
  unfold marginal gaussianVectorLaw
  apply memLp_finsetSum
  intro i _
  exact ((memLp_id_gaussianReal' (μ := m i) (v := v) p hp).const_mul (x i)).comp_measurePreserving
    (measurePreserving_eval _ i)

theorem integrable_marginal (x m : ι → ℝ) (v : ℝ≥0) :
    Integrable (marginal x) (gaussianVectorLaw m v) :=
  (memLp_marginal x m v 1 (by norm_num)).integrable le_rfl

theorem integral_marginal (x m : ι → ℝ) (v : ℝ≥0) :
    (∫ theta, marginal x theta ∂gaussianVectorLaw m v) = marginal x m := by
  unfold marginal gaussianVectorLaw
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_eval, integral_id_gaussianReal]
  · intro i _
    exact (integrable_eval (IsGaussian.integrable_id (μ := gaussianReal (m i) v))).const_mul _

theorem variance_marginal (x m : ι → ℝ) (v : ℝ≥0) :
    variance (marginal x) (gaussianVectorLaw m v) = (v : ℝ) * ∑ i, x i ^ 2 := by
  have h := variance_sum_pi (X := fun i t => x i * t)
    (fun i => (memLp_id_gaussianReal' (μ := m i) (v := v) 2 (by norm_num)).const_mul (x i))
  have heq : (∑ i, fun omega : ι → ℝ => x i * omega i) = marginal x := by
    funext omega
    simp [marginal]
  rw [heq] at h
  change variance (marginal x) (gaussianVectorLaw m v) = _ at h
  rw [h]
  calc
    (∑ i, variance (fun t => x i * t) (gaussianReal (m i) v)) =
        ∑ i, x i ^ 2 * (v : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (variance_const_mul (x i) id (gaussianReal (m i) v)).trans
        (by rw [variance_id_gaussianReal])
    _ = (v : ℝ) * ∑ i, x i ^ 2 := by rw [← Finset.sum_mul, mul_comm]

theorem integral_marginal_sq (x m : ι → ℝ) (v : ℝ≥0) :
    (∫ theta, (marginal x theta) ^ 2 ∂gaussianVectorLaw m v) =
      (marginal x m) ^ 2 + (v : ℝ) * ∑ i, x i ^ 2 := by
  have h := variance_eq_sub (memLp_marginal x m v 2 (by norm_num))
  rw [variance_marginal, integral_marginal] at h
  change (v : ℝ) * ∑ i, x i ^ 2 =
    (∫ theta, (marginal x theta) ^ 2 ∂gaussianVectorLaw m v) - marginal x m ^ 2 at h
  linarith

def pairMarginal (x : ι → ℝ) (z : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  marginal x z.1 * marginal x z.2

theorem integrable_pairMarginal (x m : ι → ℝ) (v : ℝ≥0) :
    Integrable (pairMarginal x) (gaussianPairLaw m v) :=
  (integrable_marginal x m v).mul_prod (integrable_marginal x m v)

theorem integrable_pairMarginal_sq (x m : ι → ℝ) (v : ℝ≥0) :
    Integrable (fun z => pairMarginal x z ^ 2) (gaussianPairLaw m v) := by
  simpa only [pairMarginal, mul_pow, gaussianPairLaw] using
    (memLp_marginal x m v 2 (by norm_num)).integrable_sq.mul_prod
      (memLp_marginal x m v 2 (by norm_num)).integrable_sq

theorem integral_pairMarginal (x m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, pairMarginal x z ∂gaussianPairLaw m v) = marginal x m ^ 2 := by
  unfold pairMarginal gaussianPairLaw
  rw [integral_prod_mul (marginal x) (marginal x), integral_marginal, pow_two]

/-- The second moment of the bilinear posterior observable is an exact
Gaussian product calculation. -/
theorem integral_pairMarginal_sq (x m : ι → ℝ) (v : ℝ≥0) :
    (∫ z, pairMarginal x z ^ 2 ∂gaussianPairLaw m v) =
      (marginal x m ^ 2 + (v : ℝ) * ∑ i, x i ^ 2) ^ 2 := by
  simp only [pairMarginal, mul_pow, gaussianPairLaw]
  rw [integral_prod_mul (fun theta => marginal x theta ^ 2)
    (fun theta => marginal x theta ^ 2), integral_marginal_sq]
  ring

end
end TomographyOracleCore.Revision.GaussianMarginalMoments
