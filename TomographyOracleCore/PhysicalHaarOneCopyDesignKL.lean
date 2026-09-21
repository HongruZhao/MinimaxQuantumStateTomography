import TomographyOracleCore.PhysicalHaarOneCopyKL
import TomographyOracleCore.SharedHaarTensorization
import TomographyOracleCore.KernelConditionalKL
import TomographyOracleCore.UnitaryStandardBorel

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open MatrixReduction PhysicalPOVM
open scoped ENNReal

noncomputable section

namespace PhysicalPOVM.DominatedPOVM

variable {k m : ℕ} {Outcome : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- The fixed-POVM Haar KL integrand is integrable, not merely bounded after
integration.  This is the real-valued bridge needed to pass to the
seed-integrated extended-real conditional KL. -/
theorem integrable_toReal_klDiv_orientedHardProjector_orientedHardReference
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    Integrable
      (fun U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
        (klDiv
          (M.bornMeasure (orientedHardProjectorDensityOperator
            U P b hm hb.le hbquarter))
          (M.bornMeasure (orientedHardReferenceDensityOperator
            k b hk hb.le hbquarter U))).toReal)
      (unitaryHaarProbability (k + 2)) := by
  letI : IsFiniteMeasure M.base := M.base_finite
  let G : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) × Outcome → ℝ :=
    fun x ↦ orientedPOVMKLDensityIntegrand
      M P b hm hk hb.le hbquarter x.2 x.1
  have hG : Integrable G
      ((unitaryHaarProbability (k + 2)).prod M.base) := by
    exact integrable_orientedPOVMKLDensityIntegrand_prod
      M P b hm hk hb hbquarter
  apply hG.integral_prod_left.congr
  filter_upwards with U
  exact (toReal_klDiv_orientedHardProjector_orientedHardReference_eq_integral
    M P b hm hk hb hbquarter U).symm

end PhysicalPOVM.DominatedPOVM

namespace PhysicalPOVM.RandomizedNonadaptiveDesign

variable {k m T : ℕ} {Seed Outcome : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- Exact one-shot shared-Haar KL budget for every public-seed randomized
nonadaptive physical design.  The proof uses only the jointly measurable Born
kernels exposed by `shot_measurable`; it does not require measurability of the
seed-indexed POVMs' individual dominating measures or effect densities. -/
theorem klDiv_sharedOrientationShotKernel_orientedHardProjector_le
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (t : Fin T) :
    klDiv
        (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design
            (fun U ↦ orientedHardProjectorDensityOperator
              U P b hm hb.le hbquarter)
            (measurable_orientedHardProjectorDensityOperator
              P b hm hb.le hbquarter) t)
        (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design
            (orientedHardReferenceDensityOperator
              k b hk hb.le hbquarter)
            (measurable_orientedHardReferenceDensityOperator
              k b hk hb.le hbquarter) t) ≤
      ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ))) := by
  letI : IsProbabilityMeasure design.seed := design.seed_probability
  let stateP := fun U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
    orientedHardProjectorDensityOperator U P b hm hb.le hbquarter
  let stateQ := orientedHardReferenceDensityOperator
    k b hk hb.le hbquarter
  have hstateP : Measurable stateP :=
    measurable_orientedHardProjectorDensityOperator P b hm hb.le hbquarter
  have hstateQ : Measurable stateQ :=
    measurable_orientedHardReferenceDensityOperator k b hk hb.le hbquarter
  let κ := sharedOrientationShotKernel design stateP hstateP t
  let η := sharedOrientationShotKernel design stateQ hstateQ t
  letI : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  letI : IsMarkovKernel η := by dsimp [η]; infer_instance
  have hac : ∀ z, κ z ≪ η z := by
    intro z
    let M := design.measurement t z.2
    change
      (sharedOrientationShotKernel design stateP hstateP t) z ≪
        (sharedOrientationShotKernel design stateQ hstateQ t) z
    rw [sharedOrientationShotKernel_apply, sharedOrientationShotKernel_apply]
    change M.bornMeasure (stateP z.1) ≪ M.bornMeasure (stateQ z.1)
    unfold DominatedPOVM.bornMeasure bornMeasureFrom
    exact withDensity_absolutelyContinuous_withDensity M.base _ _
      (DominatedPOVM.measurable_bornDensityFrom M (stateQ z.1)).aemeasurable
      (by
        simpa only [stateQ] using
          (DominatedPOVM.orientedHardReferenceBornDensity_ae_ne_zero
            M hk b hb hbquarter z.1))
  change klDiv
      (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ κ)
      (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ η) ≤ _
  rw [klDiv_compProd_same_eq_lintegral_kernelConditionalKL
    ((unitaryHaarProbability (k + 2)).prod design.seed) κ η hac]
  rw [lintegral_prod_symm]
  · calc
      (∫⁻ s, ∫⁻ U, kernelConditionalKL κ η (U, s)
          ∂unitaryHaarProbability (k + 2) ∂design.seed) ≤
          ∫⁻ _s, ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ))) ∂design.seed := by
            apply lintegral_mono
            intro s
            let M := design.measurement t s
            let fiberKL := fun U : unitary
                (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
              klDiv
                (M.bornMeasure (orientedHardProjectorDensityOperator
                  U P b hm hb.le hbquarter))
                (M.bornMeasure (orientedHardReferenceDensityOperator
                  k b hk hb.le hbquarter U))
            have hcond : ∀ U, kernelConditionalKL κ η (U, s) = fiberKL U := by
              intro U
              rw [kernelConditionalKL_eq_klDiv κ η (U, s) (hac (U, s))]
              rfl
            have hfinite : ∀ᵐ U ∂unitaryHaarProbability (k + 2),
                fiberKL U ≠ ∞ := by
              simpa only [fiberKL, M] using
                (DominatedPOVM.ae_klDiv_orientedHardProjector_orientedHardReference_ne_top
                  M P b hm hk hb hbquarter)
            have hint : Integrable (fun U ↦ (fiberKL U).toReal)
                (unitaryHaarProbability (k + 2)) := by
              simpa only [fiberKL, M] using
                (DominatedPOVM.integrable_toReal_klDiv_orientedHardProjector_orientedHardReference
                  M P b hm hk hb hbquarter)
            calc
              (∫⁻ U, kernelConditionalKL κ η (U, s)
                  ∂unitaryHaarProbability (k + 2)) =
                  ∫⁻ U, fiberKL U ∂unitaryHaarProbability (k + 2) := by
                    exact lintegral_congr hcond
              _ = ∫⁻ U, ENNReal.ofReal (fiberKL U).toReal
                    ∂unitaryHaarProbability (k + 2) := by
                  apply lintegral_congr_ae
                  filter_upwards [hfinite] with U hU
                  exact (ENNReal.ofReal_toReal hU).symm
              _ = ENNReal.ofReal
                    (∫ U, (fiberKL U).toReal
                      ∂unitaryHaarProbability (k + 2)) := by
                  symm
                  apply ofReal_integral_eq_lintegral_ofReal hint
                  filter_upwards with U
                  exact ENNReal.toReal_nonneg
              _ ≤ ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ))) := by
                  apply ENNReal.ofReal_le_ofReal
                  simpa only [fiberKL, M] using
                    (DominatedPOVM.integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le
                      M P b hm hk hb hbquarter)
      _ = ENNReal.ofReal (8 * b ^ 2 / (3 * (m : ℝ))) := by simp
  · exact (measurable_kernelConditionalKL κ η).aemeasurable

end PhysicalPOVM.RandomizedNonadaptiveDesign

end

end TomographyOracleCore
