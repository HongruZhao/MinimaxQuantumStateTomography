import TomographyOracleCore.PaperMatch.PurePOVMTesting

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {D T : ℕ} {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

def productTestEffect (M : Fin T → DominatedPOVM D Ω) (g : (Fin T → Ω) → ℝ) :
    Matrix (Fin T → Fin D) (Fin T → Fin D) ℂ :=
  entryIntegral (productBase M) (fun y => g y • productEffect M y)

theorem productTestEffect_valid (M : Fin T → DominatedPOVM D Ω)
    (g : (Fin T → Ω) → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1) :
    (productTestEffect M g).PosSemidef ∧ (1 - productTestEffect M g).PosSemidef :=
  randomized_binary_effect _ _ (productEffect_integrable M) (productEffect_ae_pos M)
    (productEffect_normalized M) g hg hg0 hg1

theorem productTestEffect_integrable (M : Fin T → DominatedPOVM D Ω)
    (g : (Fin T → Ω) → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (i j : Fin T → Fin D) :
    Integrable (fun y => (g y • productEffect M y) i j) (productBase M) := by
  exact (productEffect_integrable M i j).bdd_mul
    (Complex.continuous_ofReal.measurable.comp hg).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 y)] using hg1 y)

/-- A randomized transcript test is represented by an actual binary effect,
with no finiteness restriction on the measurable outcome space. -/
theorem productTestEffect_represents (M : Fin T → DominatedPOVM D Ω)
    (g : (Fin T → Ω) → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    ∫ y, g y ∂Measure.pi (fun t => (M t).bornMeasure (complexSpherePureState v)) =
      (⟪tensorVector (fun _ : Fin T => v.1),
        (productTestEffect M g).toEuclideanLin (tensorVector (fun _ : Fin T => v.1))⟫_ℂ).re := by
  let p : (Fin T → Ω) → ℝ := fun y => ∏ t, nonnegativeBornTrace (M t) (complexSpherePureState v) (y t)
  have hp : Measurable p := by
    apply Finset.measurable_prod
    intro t ht
    exact (nonnegativeBornTrace_measurable (M t) _).comp (measurable_pi_apply t)
  have hp0 (y) : 0 ≤ p y := Finset.prod_nonneg fun _ _ => le_max_right _ _
  rw [productBorn_density]
  change (∫ y, g y ∂(productBase M).withDensity (fun y => ENNReal.ofReal (p y))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    (f := fun y => ENNReal.ofReal (p y))
    (ENNReal.measurable_ofReal.comp hp) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) g]
  simp only [ENNReal.toReal_ofReal (hp0 _), smul_eq_mul]
  rw [productTestEffect, entryIntegral_inner _ _ (productTestEffect_integrable M g hg hg0 hg1)]
  have hint := integrable_matrix_inner (productBase M) (fun y => g y • productEffect M y)
    (productTestEffect_integrable M g hg hg0 hg1)
    (tensorVector (fun _ : Fin T => v.1)) (tensorVector (fun _ : Fin T => v.1))
  rw [← RCLike.re_to_complex, ← integral_re hint]
  apply integral_congr_ae
  filter_upwards [productBorn_inner_ae M v] with y hy
  rw [inner_real_smul_matrix, hy]
  simp only [p, RCLike.re_to_complex, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero, mul_comm]

/-- Neighboring actual product Born laws are hard for every bounded test. -/
theorem cube_product_test_gap {m T : ℕ} (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (M : Fin T → DominatedPOVM (m + 1) Ω)
    (g : (Fin T → Ω) → ℝ) (hg : Measurable g) (hg0 : ∀ y, 0 ≤ g y) (hg1 : ∀ y, g y ≤ 1)
    (θ : SignCube m) (j : Fin m) :
    |(∫ y, g y ∂Measure.pi (fun t => (M t).bornMeasure (cubeState a ha θ))) -
     (∫ y, g y ∂Measure.pi (fun t => (M t).bornMeasure (cubeState a ha (cubeFlip j θ))))| ≤ 1 / 2 := by
  let v (θ : SignCube m) : Metric.sphere (0 : EuclideanSpace ℂ (Fin (m + 1))) 1 :=
    ⟨cubeVector m a θ, by simpa [Metric.mem_sphere] using cubeVector_norm a θ ha⟩
  change |(∫ y, g y ∂Measure.pi (fun t => (M t).bornMeasure (complexSpherePureState (v θ)))) -
    (∫ y, g y ∂Measure.pi (fun t => (M t).bornMeasure (complexSpherePureState (v (cubeFlip j θ)))))| ≤ _
  rw [productTestEffect_represents M g hg hg0 hg1 (v θ),
    productTestEffect_represents M g hg hg0 hg1 (v (cubeFlip j θ))]
  exact cubeTensor_binary_gap a ha ha1 hTa θ j _
    (productTestEffect_valid M g hg hg0 hg1).1 (productTestEffect_valid M g hg hg0 hg1).2
end
end TomographyOracleCore.PaperMatch.RankMinimax
