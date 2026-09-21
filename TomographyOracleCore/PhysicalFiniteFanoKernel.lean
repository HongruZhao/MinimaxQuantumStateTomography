import TomographyOracleCore.FiniteKernelFano
import TomographyOracleCore.PhysicalLowerDecision
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction
open scoped BigOperators ENNReal

namespace PhysicalRisk

/-!
# Physical experiment kernels as finite Fano experiments

An arbitrary physical estimator has a genuine output kernel on density
operators.  Mapping that kernel through any measurable finite decoder gives
the finite Markov experiment consumed by `FiniteKernelFano`.  This removes
normalization, uniform-prior, and Bayes bookkeeping from the remaining
tomography information bound.

No declaration in this file is an axiom.
-/

/-- Run the physical experiment and estimator at each hard state and retain
only the output of a measurable finite decoder. -/
noncomputable def decodedEstimateKernel
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) :
    Kernel (Fin N) (Fin N) :=
  ((estimateKernel design estimator).comap stateOf hstate).map decode

noncomputable instance decodedEstimateKernel_isMarkov
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) :
    IsMarkovKernel
      (decodedEstimateKernel design estimator stateOf hstate decode hdecode) := by
  unfold decodedEstimateKernel
  letI : IsMarkovKernel
      ((estimateKernel design estimator).comap stateOf hstate) :=
    Kernel.IsMarkovKernel.comap _ hstate
  exact Kernel.IsMarkovKernel.map _ hdecode

/-- The canonical uniform finite joint law obtained from a physical
design-estimator pair followed by a finite decoder. -/
noncomputable def finiteDecodedJoint
    {D T N : ℕ} [NeZero N]
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) :
    FiniteUniformJoint (Fin N) (Fin N) :=
  FiniteUniformJoint.ofMarkovKernel
    (decodedEstimateKernel design estimator stateOf hstate decode hdecode)

/-- Exact decoded-error identity for the physical output kernel. -/
theorem finiteDecodedJoint_errorProbability_id_eq
    {D T N : ℕ} [NeZero N]
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) :
    ((finiteDecodedJoint design estimator stateOf hstate decode hdecode).toPosteriorExperiment
        id).errorProbability =
      (N : ℝ)⁻¹ * ∑ a,
        ((estimateKernel design estimator) (stateOf a)).real
          {σ | decode σ ≠ a} := by
  unfold finiteDecodedJoint
  rw [FiniteUniformJoint.ofMarkovKernel_errorProbability_id_eq]
  simp only [Fintype.card_fin]
  congr 1
  apply Finset.sum_congr rfl
  intro a _ha
  rw [decodedEstimateKernel]
  have hwrong : {y : Fin N | y ≠ a} = ({a} : Set (Fin N))ᶜ := by
    ext y
    simp [eq_comm]
  rw [hwrong, measureReal_def,
    Kernel.map_apply' _ hdecode _ (measurableSet_singleton a).compl]
  rfl

/-- `ENNReal` version of the decoded-error identity, in the same arithmetic
form as the physical risk. -/
theorem ofReal_finiteDecodedJoint_errorProbability_id_eq
    {D T N : ℕ} [NeZero N]
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode) :
    ENNReal.ofReal
        (((finiteDecodedJoint design estimator stateOf hstate decode hdecode).toPosteriorExperiment
          id).errorProbability) =
      (N : ENNReal)⁻¹ * ∑ a,
        (estimateKernel design estimator (stateOf a)) {σ | decode σ ≠ a} := by
  rw [finiteDecodedJoint_errorProbability_id_eq]
  have hNnat : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hNnat
  rw [ENNReal.ofReal_mul (inv_nonneg.mpr hNreal.le)]
  rw [ENNReal.ofReal_inv_of_pos hNreal, ENNReal.ofReal_natCast]
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply congrArg ((N : ENNReal)⁻¹ * ·)
    apply Finset.sum_congr rfl
    intro a _ha
    rw [measureReal_def, ENNReal.ofReal_toReal]
    exact measure_ne_top _ _
  · intro a _ha
    exact measureReal_nonneg

/-- A decoded-error event on one hard state is controlled by its expected
physical trace loss whenever decoder error forces loss at least `radius`.
The proof integrates the measurable error-event indicator, so it does not
require a separate measurability hypothesis for the trace loss. -/
theorem ofReal_radius_mul_wrongProbability_le_statewiseExpectedTraceRisk
    {D T N : ℕ}
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (radius : ℝ) (a : Fin N)
    (hforces : ∀ σ : DensityOperator (Fin D), decode σ ≠ a →
      ENNReal.ofReal radius ≤ hermitianTraceLoss (stateOf a) σ) :
    ENNReal.ofReal radius *
        (estimateKernel design estimator (stateOf a)) {σ | decode σ ≠ a} ≤
      statewiseExpectedTraceRisk design estimator (stateOf a) := by
  let μ := estimateKernel design estimator (stateOf a)
  let loss : DensityOperator (Fin D) → ENNReal :=
    fun σ ↦ hermitianTraceLoss (stateOf a) σ
  let event : Set (DensityOperator (Fin D)) := {σ | decode σ ≠ a}
  have hevent : MeasurableSet event := by
    change MeasurableSet (decode ⁻¹' ({a} : Set (Fin N))ᶜ)
    exact hdecode ((measurableSet_singleton a).compl)
  have hpoint : event.indicator (fun _ ↦ ENNReal.ofReal radius) ≤ loss := by
    intro σ
    by_cases hσ : σ ∈ event
    · simpa [event, loss, hσ] using hforces σ hσ
    · simp [event, hσ]
  calc
    ENNReal.ofReal radius *
        (estimateKernel design estimator (stateOf a)) {σ | decode σ ≠ a} =
      ENNReal.ofReal radius * μ event := rfl
    _ = ∫⁻ σ, event.indicator (fun _ ↦ ENNReal.ofReal radius) σ ∂μ :=
      (lintegral_indicator_const hevent (ENNReal.ofReal radius)).symm
    _ ≤ ∫⁻ σ, loss σ ∂μ := lintegral_mono hpoint
    _ = statewiseExpectedTraceRisk design estimator (stateOf a) := rfl

/-- Complete finite-kernel Fano-to-physical-risk bridge.  Once a measurable
decoder has posterior information at most `log N / 16` and every decoder
error forces trace loss at least `radius`, the actual uniform average
physical risk is at least `11 * radius / 16`.

All probability normalization, posterior construction, KL/entropy identity,
Fano constant, event probability, and Markov conversion are proved here. -/
theorem ofReal_eleven_mul_radius_div_sixteen_le_finiteAverageTraceRisk
    {D T N : ℕ} [NeZero N]
    (hN : 2 ≤ N)
    (design : Design D T) (estimator : Estimator D T)
    (stateOf : Fin N → DensityOperator (Fin D))
    (hstate : Measurable stateOf)
    (decode : DensityOperator (Fin D) → Fin N)
    (hdecode : Measurable decode)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hforces : ∀ (a : Fin N) (σ : DensityOperator (Fin D)),
      decode σ ≠ a →
        ENNReal.ofReal radius ≤ hermitianTraceLoss (stateOf a) σ)
    (hinformation :
      (finiteDecodedJoint design estimator stateOf hstate decode hdecode).posteriorKLSum ≤
        Real.log N / 16)
    (hlogTwo : 4 * Real.log 2 ≤ Real.log N) :
    ENNReal.ofReal (11 * radius / 16) ≤
      finiteAverageTraceRisk design estimator stateOf := by
  let J := finiteDecodedJoint design estimator stateOf hstate decode hdecode
  have hfano : (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment id).errorProbability := by
    apply J.eleven_sixteenths_le_errorProbability_of_posteriorKLSum_proved
    · simpa [Fintype.card_fin] using hN
    · simpa [J, Fintype.card_fin] using hinformation
    · simpa [Fintype.card_fin] using hlogTwo
  have hfanoENN : ENNReal.ofReal ((11 : ℝ) / 16) ≤
      ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) :=
    ENNReal.ofReal_le_ofReal hfano
  have hpoint (a : Fin N) :
      ENNReal.ofReal radius *
          (estimateKernel design estimator (stateOf a))
            {σ | decode σ ≠ a} ≤
        statewiseExpectedTraceRisk design estimator (stateOf a) :=
    ofReal_radius_mul_wrongProbability_le_statewiseExpectedTraceRisk
      design estimator stateOf decode hdecode radius a (hforces a)
  have hsum :
      ENNReal.ofReal radius *
          ∑ a, (estimateKernel design estimator (stateOf a))
            {σ | decode σ ≠ a} ≤
        ∑ a, statewiseExpectedTraceRisk design estimator (stateOf a) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ha ↦ hpoint a
  have havgWrong :
      ENNReal.ofReal radius *
          ((N : ENNReal)⁻¹ *
            ∑ a, (estimateKernel design estimator (stateOf a))
              {σ | decode σ ≠ a}) ≤
        finiteAverageTraceRisk design estimator stateOf := by
    unfold finiteAverageTraceRisk
    simp only [Fintype.card_fin]
    calc
      ENNReal.ofReal radius *
          ((N : ENNReal)⁻¹ *
            ∑ a, (estimateKernel design estimator (stateOf a))
              {σ | decode σ ≠ a}) =
        (N : ENNReal)⁻¹ *
          (ENNReal.ofReal radius *
            ∑ a, (estimateKernel design estimator (stateOf a))
              {σ | decode σ ≠ a}) := by ac_rfl
      _ ≤ (N : ENNReal)⁻¹ *
          ∑ a, statewiseExpectedTraceRisk design estimator (stateOf a) :=
        mul_le_mul' le_rfl hsum
  have herrorENN :
      ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) =
        (N : ENNReal)⁻¹ *
          ∑ a, (estimateKernel design estimator (stateOf a))
            {σ | decode σ ≠ a} := by
    simpa [J] using
      (ofReal_finiteDecodedJoint_errorProbability_id_eq
        design estimator stateOf hstate decode hdecode)
  calc
    ENNReal.ofReal (11 * radius / 16) =
        ENNReal.ofReal radius * ENNReal.ofReal ((11 : ℝ) / 16) := by
      rw [show 11 * radius / 16 = radius * ((11 : ℝ) / 16) by ring,
        ENNReal.ofReal_mul hradius]
    _ ≤ ENNReal.ofReal radius *
        ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) :=
      mul_le_mul' le_rfl hfanoENN
    _ = ENNReal.ofReal radius *
        ((N : ENNReal)⁻¹ *
          ∑ a, (estimateKernel design estimator (stateOf a))
            {σ | decode σ ≠ a}) := by rw [herrorENN]
    _ ≤ finiteAverageTraceRisk design estimator stateOf := havgWrong

end PhysicalRisk

end TomographyOracleCore
