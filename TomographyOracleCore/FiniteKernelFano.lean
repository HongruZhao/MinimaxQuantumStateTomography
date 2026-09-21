import TomographyOracleCore.FiniteFanoBridge
import Mathlib.MeasureTheory.Measure.Real

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-!
# Finite Markov kernels as uniform Fano experiments

This file turns an actual Markov kernel with a finite input label and finite
output alphabet into the finite uniform joint law used by the proved Fano
theorem.  Thus the normalization and uniform-prior bookkeeping are no longer
an assumption at the physical/statistical boundary.

No declaration in this file is an axiom.
-/

namespace FiniteUniformJoint

variable {Label Observation : Type*}
  [Fintype Label] [Nonempty Label]
  [Fintype Observation] [MeasurableSpace Observation]
  [MeasurableSingletonClass Observation]

/-- Joint probability mass obtained by drawing a label uniformly and then
sampling the finite-output Markov kernel. -/
noncomputable def ofMarkovKernel
    [MeasurableSpace Label]
    (κ : Kernel Label Observation) [IsMarkovKernel κ] :
    FiniteUniformJoint Label Observation where
  joint a y :=
    (Fintype.card Label : ℝ)⁻¹ * (κ a).real {y}
  joint_nonneg a y :=
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (measureReal_nonneg)
  joint_sum_one := by
    have hrow (a : Label) : ∑ y, (κ a).real {y} = 1 := by
      have h := MeasureTheory.sum_measureReal_singleton
        (μ := κ a) (Finset.univ : Finset Observation)
      simpa using h
    have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    calc
      (∑ a, ∑ y,
          (Fintype.card Label : ℝ)⁻¹ * (κ a).real {y}) =
          ∑ a, (Fintype.card Label : ℝ)⁻¹ *
            (∑ y, (κ a).real {y}) := by
              apply Finset.sum_congr rfl
              intro a _ha
              rw [Finset.mul_sum]
      _ = ∑ _a : Label, (Fintype.card Label : ℝ)⁻¹ := by
            apply Finset.sum_congr rfl
            intro a _ha
            rw [hrow a, mul_one]
      _ = (Fintype.card Label : ℝ) *
          (Fintype.card Label : ℝ)⁻¹ := by
            simp [nsmul_eq_mul]
      _ = 1 := mul_inv_cancel₀ hcard
  label_marginal_uniform a := by
    have hrow : ∑ y, (κ a).real {y} = 1 := by
      have h := MeasureTheory.sum_measureReal_singleton
        (μ := κ a) (Finset.univ : Finset Observation)
      simpa using h
    rw [← Finset.mul_sum, hrow, mul_one]

@[simp] theorem ofMarkovKernel_joint
    [MeasurableSpace Label]
    (κ : Kernel Label Observation) [IsMarkovKernel κ]
    (a : Label) (y : Observation) :
    (ofMarkovKernel κ).joint a y =
      (Fintype.card Label : ℝ)⁻¹ * (κ a).real {y} :=
  rfl

/-- For the identity decoder, the posterior experiment's error is the
uniform average of the kernel probabilities of outputting a wrong label. -/
theorem ofMarkovKernel_errorProbability_id_eq
    [MeasurableSpace Label] [MeasurableSingletonClass Label]
    (κ : Kernel Label Label) [IsMarkovKernel κ] :
    ((ofMarkovKernel κ).toPosteriorExperiment id).errorProbability =
      (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, (κ a).real {y | y ≠ a} := by
  rw [(ofMarkovKernel κ).errorProbability_eq_one_sub_joint_decode id]
  simp only [ofMarkovKernel_joint, id_eq]
  rw [← Finset.mul_sum]
  have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hwrong (a : Label) :
      (κ a).real {y | y ≠ a} = 1 - (κ a).real {a} := by
    have hset : {y : Label | y ≠ a} = ({a} : Set Label)ᶜ := by
      ext y
      simp [eq_comm]
    rw [hset, measureReal_compl (measurableSet_singleton a)]
    simp
  calc
    1 - (Fintype.card Label : ℝ)⁻¹ *
        ∑ y, (κ y).real {y} =
      (Fintype.card Label : ℝ)⁻¹ *
        ((Fintype.card Label : ℝ) - ∑ y, (κ y).real {y}) := by
          field_simp
    _ = (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, (1 - (κ a).real {a}) := by
          congr 1
          rw [Finset.sum_sub_distrib]
          simp [nsmul_eq_mul]
    _ = (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, (κ a).real {y | y ≠ a} := by
          congr 1
          apply Finset.sum_congr rfl
          intro a _ha
          exact (hwrong a).symm

/-- The finite Fano error lower bound applied directly to a genuine Markov
kernel.  The only remaining premise is the quantitative posterior-KL bound;
normalization, Bayes reconstruction, the entropy identity, and Fano itself
are all discharged internally. -/
theorem eleven_sixteenths_le_errorProbability_of_markovKernel
    [MeasurableSpace Label] [DecidableEq Label]
    (κ : Kernel Label Observation) [IsMarkovKernel κ]
    (decode : Observation → Label)
    (hcard : 2 ≤ Fintype.card Label)
    (hinformation :
      (ofMarkovKernel κ).posteriorKLSum ≤
        Real.log (Fintype.card Label) / 16)
    (hlogTwo : 4 * Real.log 2 ≤ Real.log (Fintype.card Label)) :
    (11 : ℝ) / 16 ≤
      ((ofMarkovKernel κ).toPosteriorExperiment decode).errorProbability := by
  exact (ofMarkovKernel κ).eleven_sixteenths_le_errorProbability_of_posteriorKLSum_proved
    decode hcard hinformation hlogTwo

end FiniteUniformJoint

end TomographyOracleCore
