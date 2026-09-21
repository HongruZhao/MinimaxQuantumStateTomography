import TomographyOracleCore.PhysicalHaarOneCopyPointwise

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set MatrixReduction
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder

noncomputable section

/-! # Haar averaging for one arbitrary positive effect -/

/-- The oriented Pearson integrand contributed by one positive trace-one
effect. -/
def orientedEffectPearsonIntegrand (k : ℕ) (b : ℝ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) : ℝ :=
  (b * (unitaryConjugateMatrix U (embeddedTailMatrix k A) * E).trace.re) ^ 2 /
    (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re

theorem measurable_orientedEffectPearsonIntegrand (k : ℕ) (b : ℝ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
    Measurable (orientedEffectPearsonIntegrand k b A E) := by
  have htrace (B : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
      Measurable (fun U : unitary
        (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
          (unitaryConjugateMatrix U B * E).trace.re) := by
    exact Complex.measurable_re.comp
      ((by fun_prop : Continuous (fun C :
        Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ ↦ (C * E).trace)).measurable.comp
        (continuous_unitaryConjugateMatrix_fixed B).measurable)
  unfold orientedEffectPearsonIntegrand
  exact (((measurable_const.mul
      (htrace (embeddedTailMatrix k A))).pow_const 2).div
    (htrace (hardReferenceMatrix k b)))

/- The oriented contribution of every physical effect is integrable over
the hidden unitary orientation. -/
set_option maxHeartbeats 800000 in
theorem integrable_orientedEffectPearsonIntegrand_of_posSemidef
    (k : ℕ) (hk : 1 ≤ k)
    (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) (hb1 : b < 1)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)
    (hE : E.PosSemidef) (htraceE : E.trace = 1) :
    Integrable (orientedEffectPearsonIntegrand k b A E)
      (unitaryHaarProbability (k + 2)) := by
  let c : ℝ := 2 * b ^ 2 / (1 - b)
  let w : Fin (k + 2) → ℝ := fun i ↦ hE.isHermitian.eigenvalues i
  let v : Fin (k + 2) →
      sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1 :=
    fun i ↦ hermitianEigenvectorSphere E hE.isHermitian i
  let R : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) → ℝ :=
    fun U ↦ c * ∑ i : Fin (k + 2), w i *
      complexHaarTailRatio k A (hardCanonicalInverseOrbit k (v i) U)
  have hc_nonneg : 0 ≤ c := by
    unfold c
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg b))
      (sub_nonneg.mpr (le_of_lt hb1))
  have hw_nonneg (i : Fin (k + 2)) : 0 ≤ w i := hE.eigenvalues_nonneg i
  have hterm_int (i : Fin (k + 2)) : Integrable
      (fun U ↦ complexHaarTailRatio k A
        (hardCanonicalInverseOrbit k (v i) U))
      (unitaryHaarProbability (k + 2)) := by
    exact integrable_hardCanonicalInverseOrbit_tailRatio k hk A (v i)
  have hRint : Integrable R (unitaryHaarProbability (k + 2)) := by
    unfold R
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro i hi
    exact (hterm_int i).const_mul (w i)
  have hlhs_nonneg (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
      0 ≤ orientedEffectPearsonIntegrand k b A E U := by
    unfold orientedEffectPearsonIntegrand
    have href : 0 ≤
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re := by
      rw [trace_mul_re_eq_sum_eigenvalues_mul_quadratic _ E hE.isHermitian]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hE.eigenvalues_nonneg i)
        (hermitianQuadraticValue_nonneg_of_posSemidef
          (unitaryConjugateMatrix_posSemidef U
            (hardReferenceMatrix_posSemidef k b hb0 hbquarter)) _)
    exact div_nonneg (sq_nonneg _) href
  have hpointwise : ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      orientedEffectPearsonIntegrand k b A E U ≤ R U := by
    filter_upwards [ae_all_effectEigenvector_headMass_pos
      k hk E hE.isHermitian] with U hhead
    exact orientedPositiveEffect_ratio_le_spectralTailRatio
      k b hb0 hb1 A U E hE htraceE hhead
  apply hRint.mono'
    (measurable_orientedEffectPearsonIntegrand k b A E).aestronglyMeasurable
  filter_upwards [hpointwise] with U hle
  rw [Real.norm_eq_abs, abs_of_nonneg (hlhs_nonneg U)]
  exact hle

/- Exact common-orientation Haar bound for every fixed positive trace-one
effect.  This is the complete finite-dimensional spectral/Tonelli kernel
behind the arbitrary standard-Borel POVM estimate. -/
set_option maxHeartbeats 800000 in
theorem integral_orientedPositiveEffect_ratio_le
    (k : ℕ) (hk : 1 ≤ k)
    (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) (hb1 : b < 1)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htraceA : A.trace = 0)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)
    (hE : E.PosSemidef) (htraceE : E.trace = 1) :
    (∫ U, orientedEffectPearsonIntegrand k b A E U
      ∂unitaryHaarProbability (k + 2)) ≤
      (2 * b ^ 2 / (1 - b)) *
        ((A * A).trace.re / ((k : ℝ) + 2)) := by
  let c : ℝ := 2 * b ^ 2 / (1 - b)
  let w : Fin (k + 2) → ℝ := fun i ↦ hE.isHermitian.eigenvalues i
  let v : Fin (k + 2) →
      sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1 :=
    fun i ↦ hermitianEigenvectorSphere E hE.isHermitian i
  let R : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) → ℝ :=
    fun U ↦ c * ∑ i : Fin (k + 2), w i *
      complexHaarTailRatio k A (hardCanonicalInverseOrbit k (v i) U)
  have hc_nonneg : 0 ≤ c := by
    unfold c
    exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg b))
      (sub_nonneg.mpr (le_of_lt hb1))
  have hw_nonneg (i : Fin (k + 2)) : 0 ≤ w i := hE.eigenvalues_nonneg i
  have hw_sum : (∑ i : Fin (k + 2), w i) = 1 := by
    have ht := hE.isHermitian.trace_eq_sum_eigenvalues
    have hre := congrArg Complex.re ht
    rw [htraceE] at hre
    simpa [w] using hre.symm
  have hterm_int (i : Fin (k + 2)) : Integrable
      (fun U ↦ complexHaarTailRatio k A
        (hardCanonicalInverseOrbit k (v i) U))
      (unitaryHaarProbability (k + 2)) := by
    exact integrable_hardCanonicalInverseOrbit_tailRatio k hk A (v i)
  have hRint : Integrable R (unitaryHaarProbability (k + 2)) := by
    unfold R
    apply Integrable.const_mul
    apply integrable_finset_sum
    intro i hi
    exact (hterm_int i).const_mul (w i)
  have hR_nonneg (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
      0 ≤ R U := by
    unfold R
    apply mul_nonneg hc_nonneg
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg (hw_nonneg i)
    unfold complexHaarTailRatio
    apply div_nonneg (sq_nonneg _)
    unfold complexHaarHeadMass
    exact Finset.sum_nonneg fun j hj ↦ Complex.normSq_nonneg _
  have hlhs_nonneg (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
      0 ≤ orientedEffectPearsonIntegrand k b A E U := by
    unfold orientedEffectPearsonIntegrand
    have href : 0 ≤
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re := by
      rw [trace_mul_re_eq_sum_eigenvalues_mul_quadratic _ E hE.isHermitian]
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg (hE.eigenvalues_nonneg i)
        (hermitianQuadraticValue_nonneg_of_posSemidef
          (unitaryConjugateMatrix_posSemidef U
            (hardReferenceMatrix_posSemidef k b hb0 hbquarter)) _)
    exact div_nonneg (sq_nonneg _) href
  have hpointwise : ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      orientedEffectPearsonIntegrand k b A E U ≤ R U := by
    filter_upwards [ae_all_effectEigenvector_headMass_pos
      k hk E hE.isHermitian] with U hhead
    exact orientedPositiveEffect_ratio_le_spectralTailRatio
      k b hb0 hb1 A U E hE htraceE hhead
  have hlhs_int : Integrable (orientedEffectPearsonIntegrand k b A E)
      (unitaryHaarProbability (k + 2)) := by
    apply hRint.mono'
      (measurable_orientedEffectPearsonIntegrand k b A E).aestronglyMeasurable
    filter_upwards [hpointwise] with U hle
    rw [Real.norm_eq_abs, abs_of_nonneg (hlhs_nonneg U)]
    exact hle
  calc
    (∫ U, orientedEffectPearsonIntegrand k b A E U
      ∂unitaryHaarProbability (k + 2)) ≤
        ∫ U, R U ∂unitaryHaarProbability (k + 2) :=
      integral_mono_ae hlhs_int hRint hpointwise
    _ = c * ∑ i : Fin (k + 2), w i *
        ((A * A).trace.re / ((k : ℝ) + 2)) := by
      unfold R
      rw [integral_const_mul]
      rw [integral_finset_sum]
      · apply congrArg (fun x : ℝ ↦ c * x)
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_const_mul]
        rw [integral_hardCanonicalInverseOrbit_tailRatio
          k hk A hA htraceA (v i)]
      · intro i hi
        exact (hterm_int i).const_mul (w i)
    _ = (2 * b ^ 2 / (1 - b)) *
        ((A * A).trace.re / ((k : ℝ) + 2)) := by
      rw [← Finset.sum_mul]
      rw [hw_sum]
      simp [c]

end

end TomographyOracleCore
