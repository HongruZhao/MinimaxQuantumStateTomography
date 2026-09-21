import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# Standard Gaussian vectors avoid proper linear subspaces

This is the minimal self-contained null-subspace lemma needed by the
Gaussian-to-sphere transfer.  It depends only on Mathlib.
-/

namespace LogdetLean

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- A standard Gaussian vector in a finite-dimensional real inner-product
space belongs to any fixed proper linear subspace with probability zero. -/
theorem stdGaussian_proper_submodule_null (K : Submodule ℝ E) (hK : K ≠ ⊤) :
    stdGaussian E (K : Set E) = 0 := by
  have hKperp : Kᗮ ≠ ⊥ := by
    intro h
    exact hK (K.orthogonal_eq_bot_iff.mp h)
  obtain ⟨x, hxK, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKperp
  let L : StrongDual ℝ E := innerSL ℝ x
  have hL0 : L ≠ 0 := by
    intro h
    have hn : ‖L‖ = 0 := by rw [h, norm_zero]
    rw [show ‖L‖ = ‖x‖ by simp [L, innerSL_apply_norm]] at hn
    exact hx0 (norm_eq_zero.mp hn)
  have hvar0 : Var[L; stdGaussian E].toNNReal ≠ 0 := by
    rw [variance_dual_stdGaussian]
    simp [hL0]
  have hsubset : (K : Set E) ⊆ L ⁻¹' ({0} : Set ℝ) := by
    intro y hy
    change L y = 0
    simpa [L, innerSL_apply_apply] using (K.mem_orthogonal' x).mp hxK y hy
  rw [← nonpos_iff_eq_zero]
  calc
    stdGaussian E (K : Set E) ≤ stdGaussian E (L ⁻¹' ({0} : Set ℝ)) :=
      measure_mono hsubset
    _ = ((stdGaussian E).map L) ({0} : Set ℝ) := by
      rw [Measure.map_apply (by fun_prop) (measurableSet_singleton (0 : ℝ))]
    _ = gaussianReal ((stdGaussian E)[L]) Var[L; stdGaussian E].toNNReal
          ({0} : Set ℝ) := by
      rw [IsGaussian.map_eq_gaussianReal]
    _ = 0 := by
      have hnull : NullSingletonClass
          (gaussianReal ((stdGaussian E)[L]) Var[L; stdGaussian E].toNNReal) :=
        nullSingletonClass_gaussianReal hvar0
      exact @measure_singleton ℝ _ _ hnull 0

/-- In particular, a nontrivial finite-dimensional standard Gaussian vector
is nonzero almost surely. -/
theorem stdGaussian_zero_singleton [Nontrivial E] :
    stdGaussian E ({0} : Set E) = 0 := by
  simpa using
    stdGaussian_proper_submodule_null (⊥ : Submodule ℝ E) bot_ne_top

end

end LogdetLean
