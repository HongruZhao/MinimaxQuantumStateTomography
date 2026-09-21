import TomographyOracleCore.PhysicalHaarOneCopyKL
import TomographyOracleCore.SharedHaarTensorization
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.CompProdEqIff

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

namespace TomographyOracleCore

noncomputable section

/-!
# Conditional KL for composition-product measures

Mathlib's general KL chain rule deliberately leaves conditional KL as a
composition-product divergence because the fibrewise KL need not be
measurable on arbitrary measurable spaces.  For a countably generated
outcome space, the jointly measurable Radon--Nikodym derivative of two
kernels supplies the missing measurable representative.  This module proves
the corresponding exact fibre-integration identity.
-/

/-- A jointly measurable version of the KL divergence between two kernel
fibres. -/
def kernelConditionalKL
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (κ η : Kernel Z Y) (z : Z) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (klFun ((κ.rnDeriv η z y).toReal)) ∂η z

theorem measurable_kernelConditionalKL
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (κ η : Kernel Z Y) [IsFiniteKernel κ] [IsFiniteKernel η] :
    Measurable (kernelConditionalKL κ η) := by
  unfold kernelConditionalKL
  apply Measurable.lintegral_kernel_prod_right
  fun_prop

/-- The measurable representative agrees pointwise with ordinary KL whenever
the left fibre is absolutely continuous with respect to the right fibre. -/
theorem kernelConditionalKL_eq_klDiv
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (κ η : Kernel Z Y) [IsFiniteKernel κ] [IsFiniteKernel η]
    (z : Z) (hac : κ z ≪ η z) :
    kernelConditionalKL κ η z = klDiv (κ z) (η z) := by
  rw [klDiv_eq_lintegral_klFun_of_ac hac]
  unfold kernelConditionalKL
  apply lintegral_congr_ae
  filter_upwards [κ.rnDeriv_eq_rnDeriv_measure (η := η) (a := z)] with y hy
  rw [hy]

/-- Exact conditional-KL formula for two composition products with the same
left measure and pointwise absolutely continuous Markov kernels. -/
theorem klDiv_compProd_same_eq_lintegral_kernelConditionalKL
    {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (μ : Measure Z) [IsFiniteMeasure μ]
    (κ η : Kernel Z Y) [IsMarkovKernel κ] [IsMarkovKernel η]
    (hac : ∀ z, κ z ≪ η z) :
    klDiv (μ ⊗ₘ κ) (μ ⊗ₘ η) =
      ∫⁻ z, kernelConditionalKL κ η z ∂μ := by
  let f : Z → Y → ℝ≥0∞ := κ.rnDeriv η
  have hf : Measurable (Function.uncurry f) := by
    exact κ.measurable_rnDeriv η
  have hkern : η.withDensity f = κ := by
    apply Kernel.ext
    intro z
    exact Kernel.withDensity_rnDeriv_eq (hac z)
  have hjoint : μ ⊗ₘ κ =
      (μ ⊗ₘ η).withDensity (fun p ↦ f p.1 p.2) := by
    rw [← hkern]
    exact Measure.compProd_withDensity hf
  have hjoint_ac : μ ⊗ₘ κ ≪ μ ⊗ₘ η := by
    exact Measure.AbsolutelyContinuous.compProd_right (.of_forall hac)
  rw [klDiv_eq_lintegral_klFun_of_ac hjoint_ac]
  have hrn : (μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) =ᵐ[μ ⊗ₘ η]
      fun p ↦ f p.1 p.2 := by
    rw [hjoint]
    exact Measure.rnDeriv_withDensity (μ ⊗ₘ η)
      (hf.comp (measurable_fst.prodMk measurable_snd))
  calc
    (∫⁻ x, ENNReal.ofReal
        (klFun (((μ ⊗ₘ κ).rnDeriv (μ ⊗ₘ η) x).toReal)) ∂μ ⊗ₘ η) =
        ∫⁻ x, ENNReal.ofReal (klFun ((f x.1 x.2).toReal)) ∂μ ⊗ₘ η := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with x hx
      rw [hx]
    _ = ∫⁻ z, kernelConditionalKL κ η z ∂μ := by
      rw [Measure.lintegral_compProd]
      · rfl
      · fun_prop

end

end TomographyOracleCore
