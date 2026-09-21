import TomographyOracleCore.Revision.GaussianMarginalMoments

namespace TomographyOracleCore.Revision.GaussianReflection

open MeasureTheory ProbabilityTheory GaussianChangeOfMeasure GaussianPairPosterior
open GaussianMarginalMoments
open scoped BigOperators ENNReal NNReal
noncomputable section

variable {ι : Type*} [Fintype ι]

def reflection (m theta : ι → ℝ) : ι → ℝ := fun i => 2 * m i - theta i

theorem gaussianVector_reflection (m : ι → ℝ) (v : ℝ≥0) :
    (gaussianVectorLaw m v).map (reflection m) = gaussianVectorLaw m v := by
  unfold gaussianVectorLaw reflection
  rw [Measure.pi_map_pi (fun i => (show Measurable (fun t : ℝ => 2 * m i - t) by fun_prop).aemeasurable)]
  congr 1
  funext i
  rw [gaussianReal_map_const_sub]
  congr 1
  ring

theorem marginal_reflection (x m theta : ι → ℝ) :
    marginal x theta + marginal x (reflection m theta) = 2 * marginal x m := by
  unfold marginal reflection
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def marginalGood (x m : ι → ℝ) : Set (ι → ℝ) :=
  {theta | |marginal x m| ≤ |marginal x theta|}

theorem measurableSet_marginalGood (x m : ι → ℝ) : MeasurableSet (marginalGood x m) := by
  unfold marginalGood marginal
  exact measurableSet_le measurable_const (by fun_prop)

theorem good_union_reflection (x m : ι → ℝ) :
    Set.univ ⊆ marginalGood x m ∪ (reflection m) ⁻¹' marginalGood x m := by
  intro theta _
  by_cases h : theta ∈ marginalGood x m
  · exact Or.inl h
  · apply Or.inr
    change |marginal x m| ≤ |marginal x (reflection m theta)|
    have hlt : |marginal x theta| < |marginal x m| := lt_of_not_ge h
    have ht := abs_add_le (marginal x theta) (marginal x (reflection m theta))
    rw [marginal_reflection, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)] at ht
    linarith

/-- Reflection about the actual Gaussian mean supplies the one-half
small-ball probability, without an anti-concentration assumption. -/
theorem gaussian_marginal_smallBall (x m : ι → ℝ) (v : ℝ≥0) :
    (1 / 2 : ℝ) ≤ (gaussianVectorLaw m v).real (marginalGood x m) := by
  have href : (gaussianVectorLaw m v).real ((reflection m) ⁻¹' marginalGood x m) =
      (gaussianVectorLaw m v).real (marginalGood x m) := by
    rw [← map_measureReal_apply (by unfold reflection; fun_prop)
      (measurableSet_marginalGood x m), gaussianVector_reflection]
  have hmono := measureReal_mono (μ := gaussianVectorLaw m v) (good_union_reflection x m)
  have hu := measureReal_union_le (μ := gaussianVectorLaw m v)
    (marginalGood x m) ((reflection m) ⁻¹' marginalGood x m)
  rw [probReal_univ] at hmono
  rw [href] at hu
  linarith

theorem gaussian_pair_good_probability (x m : ι → ℝ) (v : ℝ≥0) :
    (1 / 4 : ℝ) ≤ (gaussianPairLaw m v).real (marginalGood x m ×ˢ marginalGood x m) := by
  rw [gaussianPairLaw, measureReal_prod_prod]
  have h := gaussian_marginal_smallBall x m v
  nlinarith

theorem pairMarginal_sq_on_good (x m : ι → ℝ) (z : (ι → ℝ) × (ι → ℝ))
    (hz : z ∈ marginalGood x m ×ˢ marginalGood x m) :
    marginal x m ^ 4 ≤ pairMarginal x z ^ 2 := by
  have h1 : |marginal x m| ≤ |marginal x z.1| := hz.1
  have h2 : |marginal x m| ≤ |marginal x z.2| := hz.2
  have hsq1 : marginal x m ^ 2 ≤ marginal x z.1 ^ 2 := (sq_le_sq).2 h1
  have hsq2 : marginal x m ^ 2 ≤ marginal x z.2 ^ 2 := (sq_le_sq).2 h2
  have h := mul_le_mul hsq1 hsq2 (sq_nonneg _) (sq_nonneg _)
  unfold pairMarginal
  nlinarith

end
end TomographyOracleCore.Revision.GaussianReflection
