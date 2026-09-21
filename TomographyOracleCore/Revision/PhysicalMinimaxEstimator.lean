import TomographyOracleCore.Candidate2DeterministicOracle
import TomographyOracleCore.DensityGrid
import TomographyOracleCore.PhysicalDensityMeasurable
import TomographyOracleCore.PhysicalConstantMatrixPOVMPrefixLaw

/-!
# Candidate 2: actual fitting existence and a measurable physical estimator

The minimizer below is selected by compactness. This is an existence proof,
not a computational solver or a claim about its running time. Restricting
the arbitrary selection to the finite support of the actual measurement
experiment makes it measurable without a measurable-selection axiom.
-/

namespace TomographyOracleCore.Revision.PhysicalMinimax

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators Matrix.Norms.L2Operator ENNReal

noncomputable section

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- The literal empirical calibrated matrix `(D+1) mean(P_t) - I`. -/
def empiricalForwardMatrix {T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  (((D + 1 : ℕ) : ℝ) / (T : ℝ)) • (∑ t, sample t) - 1

/-- The operator-norm fitting objective for the full calibrated channel. -/
def forwardObjective (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) : ℝ :=
  matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix)

theorem continuous_forwardObjective
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) :
    Continuous (forwardObjective U Q) := by
  have hmatrix : Continuous
      (DensityOperator.matrix : DensityOperator (Fin D) → Matrix (Fin D) (Fin D) ℂ) :=
    (show Isometry (DensityOperator.matrix :
      DensityOperator (Fin D) → Matrix (Fin D) (Fin D) ℂ) from fun _ _ => rfl).continuous
  have hchannel := (finiteUnitaryFullCalibratedLinearChannel U).continuous_of_finiteDimensional
  exact (continuous_const.sub (hchannel.comp hmatrix)).norm

/-- Compact density matrices ensure an exact best forward fit. No fitting
or optimization hypothesis is assumed. -/
theorem exists_forwardMinimizer (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) :
    ∃ sigma : DensityOperator (Fin D), ∀ rho : DensityOperator (Fin D),
      forwardObjective U Q sigma ≤ forwardObjective U Q rho := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  letI : Nonempty (DensityOperator (Fin D)) := DensityGrid.densityOperator_nonempty
  obtain ⟨sigma, _, hsigma⟩ :=
    DensityCompact.isCompact_univ_densityOperator.exists_isMinOn
      Set.univ_nonempty (continuous_forwardObjective U Q).continuousOn
  exact ⟨sigma, fun rho => hsigma (Set.mem_univ rho)⟩

/-- A chosen exact minimizer. It is not asserted to be computable. -/
def forwardMinimizer (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) :=
  (exists_forwardMinimizer hD U Q).choose

theorem forwardMinimizer_le (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    forwardObjective U Q (forwardMinimizer hD U Q) ≤ forwardObjective U Q rho :=
  (exists_forwardMinimizer hD U Q).choose_spec rho

/-- Finite set of all possible matrix-valued sample transcripts. Repeated
ensemble descriptions of the same projector cause no ambiguity. -/
def possibleSamples (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ) :
    Set (Fin T → Matrix (Fin D) (Fin D) ℂ) :=
  Set.range (fun labels : Fin T → E × Fin D =>
    fun t => finiteUnitaryMeasurementProjector (U (labels t).1) (labels t).2)

theorem finite_possibleSamples
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ) :
    (possibleSamples U T).Finite := Set.finite_range _

/-- Extend the exact minimizer from the finite physical support by a fixed
density matrix. Only its physical-support values matter to the experiment. -/
def sampleEstimator (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) := by
  classical
  exact if sample ∈ possibleSamples U T then
    forwardMinimizer hD U (empiricalForwardMatrix sample)
  else DensityGrid.basisDensityOperator ⟨0, hD⟩

theorem measurable_sampleEstimator (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ) :
    Measurable (sampleEstimator hD U T) := by
  classical
  apply (measurable_const (a := DensityGrid.basisDensityOperator (⟨0, hD⟩ : Fin D))).measurable_of_countable_ne
  apply (finite_possibleSamples U T).countable.mono
  intro sample hs
  by_contra hsample
  exact hs (by simp [sampleEstimator, hsample])

theorem sampleEstimator_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ)
    (hsample : sample ∈ possibleSamples U T)
    (rho : DensityOperator (Fin D)) :
    forwardObjective U (empiricalForwardMatrix sample)
      (sampleEstimator hD U T sample) ≤
    forwardObjective U (empiricalForwardMatrix sample) rho := by
  simpa [sampleEstimator, hsample] using
    forwardMinimizer_le hD U (empiricalForwardMatrix sample) rho

/-- Every one-copy physical Born outcome lies in the finite projector
support, even when several ensemble labels produce the same projector. -/
theorem ae_mem_projectorSupport (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    ∀ᵐ P ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure rho,
      P ∈ Set.range (fun label : E × Fin D =>
        finiteUnitaryMeasurementProjector (U label.1) label.2) := by
  let S := Set.range (fun label : E × Fin D =>
    finiteUnitaryMeasurementProjector (U label.1) label.2)
  have hS : MeasurableSet S := (Set.finite_range _).measurableSet
  have hbase : ∀ᵐ P ∂finiteUnitaryProjectivePOVMBase U, P ∈ S := by
    unfold finiteUnitaryProjectivePOVMBase
    apply Measure.ae_smul_measure
    simp only [ae_finsetSum_measure_iff, Finset.mem_univ, forall_const]
    intro e b
    exact (ae_dirac_iff hS).2 ⟨(e, b), rfl⟩
  have hac : (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho ≪
      finiteUnitaryProjectivePOVMBase U := by
    change bornMeasureFrom (finiteUnitaryProjectivePOVMBase U)
      (finiteUnitaryProjectivePOVMEffect (D := D)) rho ≪ _
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le hbase

/-- The literal independent product Born law is supported on the finite
sample set used to make the estimator measurable. -/
theorem ae_mem_possibleSamples (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (rho : DensityOperator (Fin D)) :
    ∀ᵐ sample ∂Measure.pi (fun _ : Fin T =>
      (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho),
      sample ∈ possibleSamples U T := by
  classical
  letI : IsProbabilityMeasure ((finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) :=
    (finiteUnitaryProjectivePOVM D hD U).born_probability rho
  have hcoord : ∀ t : Fin T,
      ∀ᵐ sample ∂Measure.pi (fun _ : Fin T =>
        (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho),
        sample t ∈ Set.range (fun label : E × Fin D =>
          finiteUnitaryMeasurementProjector (U label.1) label.2) := by
    intro t
    exact MeasureTheory.Measure.tendsto_eval_ae_ae.eventually
      (ae_mem_projectorSupport hD U rho)
  filter_upwards [Filter.eventually_all.mpr hcoord] with sample hs
  choose labels hlabels using hs
  exact ⟨labels, funext hlabels⟩

/-- Every real sample statistic is integrable under this finite-support
product law. This proves all integrability obligations used below. -/
theorem integrable_productBorn_real (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (rho : DensityOperator (Fin D))
    (f : (Fin T → Matrix (Fin D) (Fin D) ℂ) → ℝ) :
    Integrable f (Measure.pi (fun _ : Fin T =>
      (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho)) := by
  letI : IsProbabilityMeasure ((finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) :=
    (finiteUnitaryProjectivePOVM D hD U).born_probability rho
  have h := IntegrableOn.of_finite (μ := Measure.pi (fun _ : Fin T =>
    (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho))
    (f := f) (finite_possibleSamples U T)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem
    (ae_mem_possibleSamples hD U T rho)] at h

/-- A genuine Markov estimator acting on the existing real-coded physical
transcript of the finite-unitary experiment. -/
def physicalEstimator (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ) : Estimator D T where
  kernel := Kernel.deterministic
    (sampleEstimator hD U T ∘
      decodeAllMatrixPOVMExperiment (finiteUnitaryProjectivePOVM D hD U) T)
    ((measurable_sampleEstimator hD U T).comp
      (measurable_decodeAllMatrixPOVMExperiment _ T))
  markov := by infer_instance

/-- Real trace error of the selected matrix-valued estimator. -/
def sampleTraceError (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (rho : DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  hermitianTraceNorm ((sampleEstimator hD U T sample).matrix - rho.matrix)
    ((sampleEstimator hD U T sample).sub_isHermitian rho)

theorem sampleTraceError_nonneg (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (rho : DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) :
    0 ≤ sampleTraceError hD U T rho sample := hermitianTraceNorm_nonneg _ _

theorem sampleTraceError_le_two (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (rho : DensityOperator (Fin D))
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ) :
    sampleTraceError hD U T rho sample ≤ 2 :=
  density_hermitianTraceNorm_sub_le_two _ _

/-- The selected physical Markov estimator has at most the literal product
Born expectation of its matrix trace error. The decoder, kernel composition,
integrability, and expectation transport are all proved here. -/
theorem physicalEstimator_risk_le_product_integral (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (T : ℕ)
    (rho : DensityOperator (Fin D)) :
    statewiseExpectedTraceRisk
      (constantMatrixPOVMPhysicalDesign (finiteUnitaryProjectivePOVM D hD U) T)
      (physicalEstimator hD U T) rho ≤
    ENNReal.ofReal (∫ sample, sampleTraceError hD U T rho sample
      ∂Measure.pi (fun _ : Fin T =>
        (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho)) := by
  let M := finiteUnitaryProjectivePOVM D hD U
  let design := constantMatrixPOVMPhysicalDesign M T
  let decode := decodeAllMatrixPOVMExperiment M T
  let estimate := sampleEstimator hD U T ∘ decode
  let realLoss := sampleTraceError hD U T rho ∘ decode
  have hdecode := measurePreserving_decodeAllMatrixPOVMExperiment M T rho
  have hi := integrable_productBorn_real hD U T rho (sampleTraceError hD U T rho)
  have hiobs : Integrable realLoss (design.experimentKernel rho) :=
    hdecode.integrable_comp_of_integrable hi
  have hbind :
      (∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂(Kernel.deterministic estimate
          ((measurable_sampleEstimator hD U T).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) ∘ₖ
          design.experimentKernel) rho) ≤
      ∫⁻ observed, ∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂Kernel.deterministic estimate
          ((measurable_sampleEstimator hD U T).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) observed
        ∂design.experimentKernel rho := Measure.lintegral_bind_le _ _ _
  have hinner :
      (∫⁻ observed, ∫⁻ sigma, hermitianTraceLoss rho sigma
        ∂Kernel.deterministic estimate
          ((measurable_sampleEstimator hD U T).comp
            (measurable_decodeAllMatrixPOVMExperiment M T)) observed
        ∂design.experimentKernel rho) =
      ∫⁻ observed, ENNReal.ofReal (realLoss observed)
        ∂design.experimentKernel rho := by
    apply lintegral_congr
    intro observed
    simp only [Kernel.deterministic_apply, lintegral_dirac]
    rfl
  have hofReal := ofReal_integral_eq_lintegral_ofReal hiobs
    (ae_of_all _ fun observed => sampleTraceError_nonneg hD U T rho (decode observed))
  have hint : (∫ observed, realLoss observed ∂design.experimentKernel rho) =
      ∫ sample, sampleTraceError hD U T rho sample
        ∂Measure.pi (fun _ : Fin T => M.bornMeasure rho) := by
    have himap : AEStronglyMeasurable (sampleTraceError hD U T rho)
        (Measure.map decode (design.experimentKernel rho)) := by
      rw [hdecode.map_eq]
      exact hi.aestronglyMeasurable
    exact (integral_map hdecode.measurable.aemeasurable himap).symm.trans
      (congrArg (fun mu => ∫ sample, sampleTraceError hD U T rho sample ∂mu)
        hdecode.map_eq)
  change (∫⁻ sigma, hermitianTraceLoss rho sigma
    ∂(Kernel.deterministic estimate
      ((measurable_sampleEstimator hD U T).comp
        (measurable_decodeAllMatrixPOVMExperiment M T)) ∘ₖ design.experimentKernel) rho) ≤ _
  exact hbind.trans (hinner.trans (hofReal.symm.trans (congrArg ENNReal.ofReal hint))).le

end
end TomographyOracleCore.Revision.PhysicalMinimax
