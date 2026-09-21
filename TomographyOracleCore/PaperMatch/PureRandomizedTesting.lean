import TomographyOracleCore.PaperMatch.PureTestRepresentation
import TomographyOracleCore.PhysicalTranscriptKL
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section UnitTest
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem integrable_unitTest [IsFiniteMeasure μ] (g : Ω → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable 1
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hg1 x)

theorem integral_unitTest_bounds [IsProbabilityMeasure μ] (g : Ω → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    0 ≤ ∫ x, g x ∂μ ∧ (∫ x, g x ∂μ) ≤ 1 := by
  refine ⟨integral_nonneg hg0, ?_⟩
  have h := integral_mono (integrable_unitTest μ g hg hg0 hg1)
    (integrable_const (1 : ℝ)) hg1
  simpa using h
end UnitTest

section Seed
variable {m T : ℕ} {Seed Ω : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem cube_experiment_test_gap (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (design : RandomizedNonadaptiveDesign (m + 1) T Seed Ω)
    (g : Seed × (Fin T → Ω) → ℝ) (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (θ : SignCube m) (j : Fin m) :
    |(∫ x, g x ∂design.experimentKernel (cubeState a ha θ)) -
     (∫ x, g x ∂design.experimentKernel (cubeState a ha (cubeFlip j θ)))| ≤ 1 / 2 := by
  letI : IsProbabilityMeasure design.seed := design.seed_probability
  let mean (θ : SignCube m) (s : Seed) : ℝ :=
    ∫ y, g (s, y) ∂design.outcomes (cubeState a ha θ, s)
  have hm (θ : SignCube m) : Measurable (mean θ) :=
    (hg.stronglyMeasurable.integral_kernel_prod_right'
      (κ := Kernel.sectR design.outcomes (cubeState a ha θ))).measurable
  have hmb (θ : SignCube m) (s : Seed) : 0 ≤ mean θ s ∧ mean θ s ≤ 1 :=
    integral_unitTest_bounds _ _ (hg.comp measurable_prodMk_left)
      (fun y => hg0 (s, y)) (fun y => hg1 (s, y))
  have hmi (θ : SignCube m) : Integrable (mean θ) design.seed :=
    integrable_unitTest _ _ (hm θ) (fun s => (hmb θ s).1) (fun s => (hmb θ s).2)
  have hid (θ : SignCube m) :
      (∫ x, g x ∂design.experimentKernel (cubeState a ha θ)) = ∫ s, mean θ s ∂design.seed := by
    have h := ProbabilityTheory.integral_compProd
      (integrable_unitTest (design.experimentKernel (cubeState a ha θ)) g hg hg0 hg1)
    exact h
  have hgap (s : Seed) : |mean θ s - mean (cubeFlip j θ) s| ≤ 1 / 2 := by
    dsimp [mean]
    rw [design.outcomes_eq_pi, design.outcomes_eq_pi]
    exact cube_product_test_gap a ha ha1 hTa (fun t => design.measurement t s)
      (fun y => g (s, y)) (hg.comp measurable_prodMk_left)
      (fun y => hg0 (s, y)) (fun y => hg1 (s, y)) θ j
  rw [hid θ, hid (cubeFlip j θ), ← integral_sub (hmi θ) (hmi (cubeFlip j θ))]
  calc
    _ ≤ ∫ s, |mean θ s - mean (cubeFlip j θ) s| ∂design.seed := abs_integral_le_integral_abs
    _ ≤ ∫ _s : Seed, (1 / 2 : ℝ) ∂design.seed :=
      integral_mono ((hmi θ).sub (hmi (cubeFlip j θ))).abs (integrable_const _) hgap
    _ = _ := by simp
end Seed

/-- State-independent reconstruction randomization preserves the proved test bound. -/
theorem cube_estimate_test_gap {m T : ℕ} (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T)
    (f : DensityOperator (Fin (m + 1)) → ℝ) (hf : Measurable f)
    (hf0 : ∀ σ, 0 ≤ f σ) (hf1 : ∀ σ, f σ ≤ 1)
    (θ : SignCube m) (j : Fin m) :
    |(∫ σ, f σ ∂estimateKernel design estimator (cubeState a ha θ)) -
     (∫ σ, f σ ∂estimateKernel design estimator (cubeState a ha (cubeFlip j θ)))| ≤ 1 / 2 := by
  let g (x : Data T) : ℝ := ∫ σ, f σ ∂estimator.kernel x
  have hg : Measurable g := (hf.stronglyMeasurable.integral_kernel (κ := estimator.kernel)).measurable
  have hgb (x : Data T) : 0 ≤ g x ∧ g x ≤ 1 :=
    integral_unitTest_bounds _ f hf hf0 hf1
  have hid (θ : SignCube m) :
      (∫ σ, f σ ∂estimateKernel design estimator (cubeState a ha θ)) =
        ∫ x, g x ∂design.experimentKernel (cubeState a ha θ) :=
    Kernel.integral_comp (integrable_unitTest _ f hf hf0 hf1)
  rw [hid θ, hid (cubeFlip j θ)]
  exact cube_experiment_test_gap a ha ha1 hTa design g hg
    (fun x => (hgb x).1) (fun x => (hgb x).2) θ j
end
end TomographyOracleCore.PaperMatch.RankMinimax
