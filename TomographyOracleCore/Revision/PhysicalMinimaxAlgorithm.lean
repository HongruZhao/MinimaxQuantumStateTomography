import TomographyOracleCore.Revision.PhysicalMinimaxRates

/-!
# Physical risk interface for an actual Candidate 2 algorithm

The function `solve` is an actual map from an empirical matrix to a density
operator. The generic bridge assumes its displayed fitting guarantee; a
verified implementation supplies that theorem. No solver contract is
postulated and no computational claim is made into an axiom here.
-/

namespace TomographyOracleCore.Revision.PhysicalMinimax

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- Realize an arbitrary actual matrix solver on the finite sample support.
The off-support extension does not affect any physical Born experiment. -/
def algorithmSampleEstimator (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) := by
  classical
  exact if sample ∈ possibleSamples U T then solve (empiricalForwardMatrix sample)
    else DensityGrid.basisDensityOperator ⟨0, hD⟩

theorem measurable_algorithmSampleEstimator (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D)) :
    Measurable (algorithmSampleEstimator hD U T solve) := by
  classical
  apply (measurable_const (a := DensityGrid.basisDensityOperator (⟨0, hD⟩ : Fin D))).measurable_of_countable_ne
  apply (finite_possibleSamples U T).countable.mono
  intro sample hs
  by_contra hsample
  exact hs (by simp [algorithmSampleEstimator, hsample])

theorem algorithmSampleEstimator_eq (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ)
    (hsample : sample ∈ possibleSamples U T) :
    algorithmSampleEstimator hD U T solve sample = solve (empiricalForwardMatrix sample) := by
  simp [algorithmSampleEstimator, hsample]

/-- A genuine physical Markov estimator for the supplied matrix algorithm. -/
def algorithmPhysicalEstimator (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D)) : Estimator D T where
  kernel := Kernel.deterministic
    (algorithmSampleEstimator hD U T solve ∘
      decodeAllMatrixPOVMExperiment (finiteUnitaryProjectivePOVM D hD U) T)
    ((measurable_algorithmSampleEstimator hD U T solve).comp
      (measurable_decodeAllMatrixPOVMExperiment _ T))
  markov := by infer_instance

/-- Literal matrix trace error of the algorithm. -/
def algorithmTraceError (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D))
    (rho : DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  hermitianTraceNorm ((algorithmSampleEstimator hD U T solve sample).matrix - rho.matrix)
    ((algorithmSampleEstimator hD U T solve sample).sub_isHermitian rho)

theorem algorithmTraceError_nonneg (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D))
    (rho : DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) :
    0 ≤ algorithmTraceError hD U T solve rho sample := hermitianTraceNorm_nonneg _ _

theorem algorithmTraceError_le_two (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D))
    (rho : DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) :
    algorithmTraceError hD U T solve rho sample ≤ 2 :=
  density_hermitianTraceNorm_sub_le_two _ _

/-- Physical risk transport for every actual matrix algorithm. -/
theorem algorithmPhysicalEstimator_risk_le_product_integral (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (solve : Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D))
    (rho : DensityOperator (Fin D)) :
    statewiseExpectedTraceRisk
      (constantMatrixPOVMPhysicalDesign (finiteUnitaryProjectivePOVM D hD U) T)
      (algorithmPhysicalEstimator hD U T solve) rho ≤
    ENNReal.ofReal (∫ sample, algorithmTraceError hD U T solve rho sample
      ∂Measure.pi (fun _ : Fin T =>
        (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho)) := by
  let M := finiteUnitaryProjectivePOVM D hD U
  let design := constantMatrixPOVMPhysicalDesign M T
  let decode := decodeAllMatrixPOVMExperiment M T
  let estimate := algorithmSampleEstimator hD U T solve ∘ decode
  let realLoss := algorithmTraceError hD U T solve rho ∘ decode
  have hdecode := measurePreserving_decodeAllMatrixPOVMExperiment M T rho
  have hi := integrable_productBorn_real hD U T rho (algorithmTraceError hD U T solve rho)
  have hiobs : Integrable realLoss (design.experimentKernel rho) :=
    hdecode.integrable_comp_of_integrable hi
  have hbind :
      (∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂(Kernel.deterministic estimate
          ((measurable_algorithmSampleEstimator hD U T solve).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) ∘ₖ
          design.experimentKernel) rho) ≤
      ∫⁻ observed, ∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂Kernel.deterministic estimate
          ((measurable_algorithmSampleEstimator hD U T solve).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) observed
        ∂design.experimentKernel rho := Measure.lintegral_bind_le _ _ _
  have hinner :
      (∫⁻ observed, ∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂Kernel.deterministic estimate
          ((measurable_algorithmSampleEstimator hD U T solve).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) observed
        ∂design.experimentKernel rho) =
      ∫⁻ observed, ENNReal.ofReal (realLoss observed)
        ∂design.experimentKernel rho := by
    apply lintegral_congr
    intro observed
    simp only [Kernel.deterministic_apply, lintegral_dirac]
    rfl
  have hofReal := ofReal_integral_eq_lintegral_ofReal hiobs
    (ae_of_all _ fun observed => algorithmTraceError_nonneg hD U T solve rho (decode observed))
  have hint : (∫ observed, realLoss observed ∂design.experimentKernel rho) =
      ∫ sample, algorithmTraceError hD U T solve rho sample
        ∂Measure.pi (fun _ : Fin T => M.bornMeasure rho) := by
    have himap : AEStronglyMeasurable (algorithmTraceError hD U T solve rho)
        (Measure.map decode (design.experimentKernel rho)) := by
      rw [hdecode.map_eq]
      exact hi.aestronglyMeasurable
    exact (integral_map hdecode.measurable.aemeasurable himap).symm.trans
      (congrArg (fun mu => ∫ sample, algorithmTraceError hD U T solve rho sample ∂mu)
        hdecode.map_eq)
  change (∫⁻ sigma, hermitianTraceLoss rho sigma
    ∂(Kernel.deterministic estimate
      ((measurable_algorithmSampleEstimator hD U T solve).comp
        (measurable_decodeAllMatrixPOVMExperiment M T)) ∘ₖ design.experimentKernel) rho) ≤ _
  exact hbind.trans (hinner.trans (hofReal.symm.trans (congrArg ENNReal.ofReal hint))).le

end
end TomographyOracleCore.Revision.PhysicalMinimax
