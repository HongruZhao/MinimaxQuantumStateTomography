import TomographyOracleCore.FiniteKernelFano

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-!
# Finite information-radius identity

For a finite uniform experiment, mutual information is at most the average
relative entropy to any fixed reference distribution.  This file proves the
identity directly from the finite joint law used by `FiniteFanoBridge`; no
information-theoretic assertion is assumed.
-/

namespace FiniteUniformJoint

variable {Label Observation : Type*}
  [Fintype Label] [Nonempty Label] [Fintype Observation]

/-- Average log-likelihood radius of a finite uniform joint law relative to
an arbitrary reference probability vector on the observation alphabet. -/
noncomputable def referenceInformation
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) : ℝ :=
  ∑ y, ∑ a, J.joint a y *
    Real.log (((Fintype.card Label : ℝ) * J.joint a y) / q y)

/-- Relative entropy of the observation marginal from the same reference
probability vector. -/
noncomputable def marginalReferenceInformation
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) : ℝ :=
  ∑ y, J.observationWeight y *
    Real.log (J.observationWeight y / q y)

/-- Elementary Gibbs inequality for finite real probability vectors with a
strictly positive reference vector. -/
theorem finiteReferenceInformation_nonnegative
    (p q : Observation → ℝ)
    (hp : ∀ y, 0 ≤ p y) (hq : ∀ y, 0 < q y)
    (hpsum : ∑ y, p y = 1) (hqsum : ∑ y, q y = 1) :
    0 ≤ ∑ y, p y * Real.log (p y / q y) := by
  have hpoint (y : Observation) :
      p y - q y ≤ p y * Real.log (p y / q y) := by
    by_cases hpzero : p y = 0
    · simp [hpzero, (hq y).le]
    · have hppos : 0 < p y := lt_of_le_of_ne (hp y) (Ne.symm hpzero)
      have hlog := Real.log_le_sub_one_of_pos (div_pos (hq y) hppos)
      have hmul :
          p y * Real.log (q y / p y) ≤ p y * (q y / p y - 1) :=
        mul_le_mul_of_nonneg_left hlog hppos.le
      have hright : p y * (q y / p y - 1) = q y - p y := by
        field_simp [hpzero]
      have hlogneg :
          Real.log (p y / q y) = -Real.log (q y / p y) := by
        rw [Real.log_div hpzero (ne_of_gt (hq y)),
          Real.log_div (ne_of_gt (hq y)) hpzero]
        ring
      rw [hright] at hmul
      rw [hlogneg]
      linarith
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset Observation))
    fun y _hy ↦ hpoint y
  rw [Finset.sum_sub_distrib, hpsum, hqsum, sub_self] at hsum
  exact hsum

/-- Pointwise likelihood factorization behind the information-radius
identity.  Zero joint masses are handled explicitly. -/
theorem joint_log_reference_factorization
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) (hq : ∀ y, 0 < q y)
    (y : Observation) (a : Label) :
    J.joint a y *
        Real.log (((Fintype.card Label : ℝ) * J.joint a y) / q y) =
      J.joint a y *
          Real.log ((Fintype.card Label : ℝ) * J.posterior y a) +
        J.joint a y *
          Real.log (J.observationWeight y / q y) := by
  have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hjoint : J.joint a y = 0
  · simp [hjoint]
  have hweight : J.observationWeight y ≠ 0 := by
    intro hzero
    have hle : J.joint a y ≤ J.observationWeight y := by
      unfold observationWeight
      exact Finset.single_le_sum
        (fun b _hb ↦ J.joint_nonneg b y) (Finset.mem_univ a)
    rw [hzero] at hle
    exact hjoint (le_antisymm hle (J.joint_nonneg a y))
  have hqne : q y ≠ 0 := ne_of_gt (hq y)
  rw [posterior, if_neg hweight]
  rw [Real.log_div (mul_ne_zero hcard hjoint) hqne,
    Real.log_mul hcard hjoint,
    Real.log_mul hcard (div_ne_zero hjoint hweight),
    Real.log_div hjoint hweight,
    Real.log_div hweight hqne]
  ring

/-- Exact information-radius decomposition:
`average KL to q = mutual information + KL(marginal || q)`. -/
theorem referenceInformation_eq_posteriorKLSum_add_marginal
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) (hq : ∀ y, 0 < q y) :
    J.referenceInformation q =
      J.posteriorKLSum + J.marginalReferenceInformation q := by
  unfold referenceInformation posteriorKLSum marginalReferenceInformation
  simp_rw [J.joint_log_reference_factorization q hq]
  simp_rw [Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro y _hy
  rw [← Finset.sum_mul]
  rfl

/-- Information-radius inequality for the finite joint experiment. -/
theorem posteriorKLSum_le_referenceInformation
    (J : FiniteUniformJoint Label Observation)
    (q : Observation → ℝ) (hq : ∀ y, 0 < q y)
    (hqsum : ∑ y, q y = 1) :
    J.posteriorKLSum ≤ J.referenceInformation q := by
  have hmarginal : 0 ≤ J.marginalReferenceInformation q := by
    exact finiteReferenceInformation_nonnegative
      J.observationWeight q J.observationWeight_nonneg hq
        J.observationWeight_sum_one hqsum
  rw [J.referenceInformation_eq_posteriorKLSum_add_marginal q hq]
  linarith

/-- For a Markov kernel, the reference radius is the uniform average of the
ordinary finite-alphabet log-likelihood sums. -/
theorem ofMarkovKernel_referenceInformation_eq
    [MeasurableSpace Label]
    [MeasurableSpace Observation] [MeasurableSingletonClass Observation]
    (kappa : Kernel Label Observation) [IsMarkovKernel kappa]
    (q : Observation → ℝ) :
    (ofMarkovKernel kappa).referenceInformation q =
      (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, ∑ y, (kappa a).real {y} *
          Real.log ((kappa a).real {y} / q y) := by
  unfold referenceInformation
  simp only [ofMarkovKernel_joint]
  have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _hy
  have hinside :
      (Fintype.card Label : ℝ) *
          ((Fintype.card Label : ℝ)⁻¹ * (kappa a).real {y}) / q y =
        (kappa a).real {y} / q y := by
    rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
  rw [hinside]
  ring

/-- Direct finite-kernel information-radius bound.  A uniform per-label KL
bound to one positive reference law controls the posterior information used
by the internally proved Fano theorem. -/
theorem ofMarkovKernel_posteriorKLSum_le
    [MeasurableSpace Label]
    [MeasurableSpace Observation] [MeasurableSingletonClass Observation]
    (kappa : Kernel Label Observation) [IsMarkovKernel kappa]
    (q : Observation → ℝ) (hq : ∀ y, 0 < q y)
    (hqsum : ∑ y, q y = 1)
    (information : ℝ)
    (hlabel : ∀ a, ∑ y, (kappa a).real {y} *
      Real.log ((kappa a).real {y} / q y) ≤ information) :
    (ofMarkovKernel kappa).posteriorKLSum ≤ information := by
  calc
    (ofMarkovKernel kappa).posteriorKLSum ≤
        (ofMarkovKernel kappa).referenceInformation q :=
      posteriorKLSum_le_referenceInformation _ q hq hqsum
    _ = (Fintype.card Label : ℝ)⁻¹ *
        ∑ a, ∑ y, (kappa a).real {y} *
          Real.log ((kappa a).real {y} / q y) :=
      ofMarkovKernel_referenceInformation_eq kappa q
    _ ≤ (Fintype.card Label : ℝ)⁻¹ *
        ∑ _a : Label, information := by
      gcongr with a
      exact hlabel a
    _ = information := by
      have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
        exact_mod_cast Fintype.card_ne_zero
      simp [nsmul_eq_mul, hcard]

end FiniteUniformJoint

end TomographyOracleCore
