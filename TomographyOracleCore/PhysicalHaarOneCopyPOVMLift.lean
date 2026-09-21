import TomographyOracleCore.PhysicalHaarOneCopy
import TomographyOracleCore.PhysicalHaarOneCopyEffectAverage
import Mathlib.MeasureTheory.Integral.Prod

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set MatrixReduction
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder

noncomputable section

namespace PhysicalPOVM.DominatedPOVM

variable {Outcome : Type*} [MeasurableSpace Outcome]
  [StandardBorelSpace Outcome]

/-! # Tonelli lift from one effect to an arbitrary dominated POVM -/

/-- The common-orientation Pearson contribution of the effect density at
one outcome of an arbitrary dominated POVM. -/
def orientedPOVMEffectPearsonIntegrand (k : ℕ) (b : ℝ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (M : DominatedPOVM (k + 2) Outcome)
    (z : Outcome)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) : ℝ :=
  orientedEffectPearsonIntegrand k b A (M.effect z) U

/-- Joint measurability in the arbitrary standard-Borel outcome and the
hidden unitary orientation. -/
theorem measurable_uncurry_orientedPOVMEffectPearsonIntegrand
    (k : ℕ) (b : ℝ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (M : DominatedPOVM (k + 2) Outcome) :
    Measurable (Function.uncurry
      (orientedPOVMEffectPearsonIntegrand k b A M)) := by
  have htrace (B : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
      Measurable (fun p : Outcome ×
        unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
          (unitaryConjugateMatrix p.2 B * M.effect p.1).trace.re) := by
    apply Complex.measurable_re.comp
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.measurable_sum Finset.univ (fun i _ ↦
      Finset.measurable_sum Finset.univ (fun j _ ↦
        (((measurable_complexMatrix_apply (Fin (k + 2)) i j).comp
            ((continuous_unitaryConjugateMatrix_fixed B).measurable.comp
              measurable_snd)).mul
          ((M.effect_measurable j i).comp measurable_fst))))
  unfold Function.uncurry orientedPOVMEffectPearsonIntegrand
    orientedEffectPearsonIntegrand
  exact (((measurable_const.mul
      (htrace (embeddedTailMatrix k A))).pow_const 2).div
    (htrace (hardReferenceMatrix k b)))

/-- A positive effect gives a nonnegative Pearson contribution at every
orientation. -/
theorem orientedPOVMEffectPearsonIntegrand_nonneg
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (M : DominatedPOVM (k + 2) Outcome)
    (z : Outcome) (hE : (M.effect z).PosSemidef)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    0 ≤ orientedPOVMEffectPearsonIntegrand k b A M z U := by
  unfold orientedPOVMEffectPearsonIntegrand orientedEffectPearsonIntegrand
  have href : 0 ≤
      (unitaryConjugateMatrix U (hardReferenceMatrix k b) *
        M.effect z).trace.re := by
    rw [trace_mul_re_eq_sum_eigenvalues_mul_quadratic _
      (M.effect z) hE.isHermitian]
    apply Finset.sum_nonneg
    intro i hi
    exact mul_nonneg (hE.eigenvalues_nonneg i)
      (hermitianQuadraticValue_nonneg_of_posSemidef
        (unitaryConjugateMatrix_posSemidef U
          (hardReferenceMatrix_posSemidef k b hb0 hbquarter)) _)
  exact div_nonneg (sq_nonneg _) href

/- The arbitrary-outcome/Haar integrand is integrable on the full product
measure.  This is the finiteness statement needed for Fubini, not an
implicit Tonelli side condition. -/
set_option maxHeartbeats 1200000 in
theorem integrable_uncurry_orientedPOVMEffectPearsonIntegrand
    (k : ℕ) (hk : 1 ≤ k)
    (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) (hb1 : b < 1)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htraceA : A.trace = 0)
    (M : DominatedPOVM (k + 2) Outcome) :
    Integrable (Function.uncurry
      (orientedPOVMEffectPearsonIntegrand k b A M))
      (M.base.prod (unitaryHaarProbability (k + 2))) := by
  letI : IsFiniteMeasure M.base := M.base_finite
  let F := Function.uncurry (orientedPOVMEffectPearsonIntegrand k b A M)
  let C := (2 * b ^ 2 / (1 - b)) *
    ((A * A).trace.re / ((k : ℝ) + 2))
  have hFmeas : AEStronglyMeasurable F
      (M.base.prod (unitaryHaarProbability (k + 2))) :=
    (measurable_uncurry_orientedPOVMEffectPearsonIntegrand
      k b A M).aestronglyMeasurable
  apply (integrable_prod_iff hFmeas).2
  constructor
  · filter_upwards [M.effect_ae_posSemidef, M.effect_ae_trace_one]
      with z hE htraceE
    exact integrable_orientedEffectPearsonIntegrand_of_posSemidef
      k hk b hb0 hbquarter hb1 A (M.effect z) hE htraceE
  · apply Integrable.of_bound hFmeas.norm.integral_prod_right' C
    filter_upwards [M.effect_ae_posSemidef, M.effect_ae_trace_one]
      with z hE htraceE
    have hnorm :
        (∫ U, ‖F (z, U)‖ ∂unitaryHaarProbability (k + 2)) =
          ∫ U, F (z, U) ∂unitaryHaarProbability (k + 2) := by
      apply integral_congr_ae
      filter_upwards with U
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact orientedPOVMEffectPearsonIntegrand_nonneg
        k b hb0 hbquarter A M z hE U
    rw [hnorm, Real.norm_eq_abs, abs_of_nonneg]
    · exact integral_orientedPositiveEffect_ratio_le
        k hk b hb0 hbquarter hb1 A hA htraceA (M.effect z) hE htraceE
    · exact integral_nonneg fun U ↦
        orientedPOVMEffectPearsonIntegrand_nonneg
          k b hb0 hbquarter A M z hE U

/- Tonelli/Fubini and the exact mass `k+2` of the trace-dominating measure
lift the fixed trace-one-effect estimate to every standard-Borel dominated
POVM.  The factor `1/(k+2)` cancels with the base mass. -/
set_option maxHeartbeats 1200000 in
theorem integral_unitaryHaar_integral_orientedPOVMEffectPearsonIntegrand_le
    (k : ℕ) (hk : 1 ≤ k)
    (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) (hb1 : b < 1)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htraceA : A.trace = 0)
    (M : DominatedPOVM (k + 2) Outcome) :
    (∫ U, ∫ z, orientedPOVMEffectPearsonIntegrand k b A M z U
        ∂M.base ∂unitaryHaarProbability (k + 2)) ≤
      (2 * b ^ 2 / (1 - b)) * (A * A).trace.re := by
  letI : IsFiniteMeasure M.base := M.base_finite
  let F := Function.uncurry (orientedPOVMEffectPearsonIntegrand k b A M)
  let C := (2 * b ^ 2 / (1 - b)) *
    ((A * A).trace.re / ((k : ℝ) + 2))
  have hFint : Integrable F
      (M.base.prod (unitaryHaarProbability (k + 2))) :=
    integrable_uncurry_orientedPOVMEffectPearsonIntegrand
      k hk b hb0 hbquarter hb1 A hA htraceA M
  have hswap :
      (∫ U, ∫ z, orientedPOVMEffectPearsonIntegrand k b A M z U
          ∂M.base ∂unitaryHaarProbability (k + 2)) =
        ∫ z, ∫ U, orientedPOVMEffectPearsonIntegrand k b A M z U
          ∂unitaryHaarProbability (k + 2) ∂M.base := by
    exact (integral_integral_swap hFint).symm
  rw [hswap]
  calc
    (∫ z, ∫ U, orientedPOVMEffectPearsonIntegrand k b A M z U
        ∂unitaryHaarProbability (k + 2) ∂M.base) ≤
        ∫ _z : Outcome, C ∂M.base := by
      apply integral_mono_ae hFint.integral_prod_left (integrable_const C)
      filter_upwards [M.effect_ae_posSemidef, M.effect_ae_trace_one]
        with z hE htraceE
      exact integral_orientedPositiveEffect_ratio_le
        k hk b hb0 hbquarter hb1 A hA htraceA (M.effect z) hE htraceE
    _ = (2 * b ^ 2 / (1 - b)) * (A * A).trace.re := by
      rw [integral_const, base_real_univ_eq_dimension M, smul_eq_mul]
      dsimp only [C]
      have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
      norm_num [Nat.cast_add]
      field_simp [ne_of_gt hk2]

end PhysicalPOVM.DominatedPOVM

end

end TomographyOracleCore
