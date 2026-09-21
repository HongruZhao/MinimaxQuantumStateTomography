import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

/-!
# Finite Fano inequality from posterior probabilities

Mathlib currently provides Kullback--Leibler divergence and its data-processing
inequality, but no discrete Shannon conditional-entropy or mutual-information
interface.  This file therefore starts from an elementary finite posterior
experiment.  Its hypotheses say exactly that the observation weights and every
posterior row are probability vectors.  From those hypotheses we prove the
finite-label entropy estimate, including the Jensen step, and then derive the
usual Fano lower bound.

No declaration in this file is an axiom.  The remaining bridge for a concrete
statistical model is the standard chain-rule identity
`log |labels| = mutualInformation + conditionalEntropy`.
-/

open scoped BigOperators

/-- Shannon entropy (in nats) of a finite real-valued probability vector.
The definition is meaningful for every vector; probability-vector hypotheses
are supplied to the theorems that use it. -/
noncomputable def finiteShannonEntropy {α : Type*} [Fintype α]
    (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

/-- The exact error-entropy envelope occurring in finite Fano:
`h₂(e) + e log (N-1)`. -/
noncomputable def finiteFanoEnvelope (labelCount : ℕ) (error : ℝ) : ℝ :=
  Real.binEntropy error + error * Real.log (labelCount - 1 : ℕ)

/-- An elementary finite posterior experiment.  `weight y` is the probability
of observation `y`, `posterior y a` is the conditional probability of label
`a`, and `decode y` is the decoded label. -/
structure FinitePosteriorExperiment (Label Observation : Type*)
    [Fintype Label] [Fintype Observation] where
  weight : Observation → ℝ
  posterior : Observation → Label → ℝ
  decode : Observation → Label
  weight_nonneg : ∀ y, 0 ≤ weight y
  weight_sum_one : ∑ y, weight y = 1
  posterior_nonneg : ∀ y a, 0 ≤ posterior y a
  posterior_sum_one : ∀ y, ∑ a, posterior y a = 1

namespace FinitePosteriorExperiment

variable {Label Observation : Type*}
  [Fintype Label] [Fintype Observation]

/-- Average posterior Shannon entropy. -/
noncomputable def conditionalEntropy
    (E : FinitePosteriorExperiment Label Observation) : ℝ :=
  ∑ y, E.weight y * finiteShannonEntropy (E.posterior y)

/-- Average probability that the decoded label is wrong. -/
noncomputable def errorProbability
    (E : FinitePosteriorExperiment Label Observation) : ℝ :=
  ∑ y, E.weight y * (1 - E.posterior y (E.decode y))

end FinitePosteriorExperiment

variable {Label Observation : Type*}
  [Fintype Label] [Fintype Observation]

/-- Uniform spreading maximizes the entropy of a fixed nonnegative mass on a
nonempty finite set. -/
theorem sum_negMulLog_le_negMulLog_sum_add_mul_log_card
    {α : Type*} [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    (∑ a ∈ s, Real.negMulLog (p a)) ≤
      Real.negMulLog (∑ a ∈ s, p a) +
        (∑ a ∈ s, p a) * Real.log s.card := by
  let m : ℝ := s.card
  have hm : 0 < m := by
    dsimp [m]
    exact_mod_cast hs.card_pos
  have hm0 : m ≠ 0 := ne_of_gt hm
  have hweights : ∑ _a ∈ s, m⁻¹ = (1 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    change m * m⁻¹ = 1
    exact mul_inv_cancel₀ hm0
  have hjensen := Real.concaveOn_negMulLog.le_map_sum
    (t := s) (w := fun _a => m⁻¹) (p := p)
    (fun _a _ha => inv_nonneg.mpr hm.le)
    hweights
    (fun a ha => Set.mem_Ici.mpr (hp a ha))
  simp only [smul_eq_mul, Function.comp_apply] at hjensen
  have hleft :
      (∑ a ∈ s, m⁻¹ * Real.negMulLog (p a)) =
        m⁻¹ * (∑ a ∈ s, Real.negMulLog (p a)) := by
    rw [Finset.mul_sum]
  have hright :
      (∑ a ∈ s, m⁻¹ * p a) = m⁻¹ * (∑ a ∈ s, p a) := by
    rw [Finset.mul_sum]
  rw [hleft, hright] at hjensen
  have hscaled := (mul_le_mul_of_nonneg_left hjensen hm.le)
  have hinv : m * m⁻¹ = 1 := mul_inv_cancel₀ hm0
  have hentropyIdentity (x : ℝ) :
      m * Real.negMulLog (m⁻¹ * x) =
        Real.negMulLog x + x * Real.log m := by
    rw [Real.negMulLog_mul]
    simp only [Real.negMulLog, Real.log_inv]
    field_simp [hm0]
    ring
  calc
    (∑ a ∈ s, Real.negMulLog (p a)) =
        m * (m⁻¹ * (∑ a ∈ s, Real.negMulLog (p a))) := by
          symm
          calc
            m * (m⁻¹ * (∑ a ∈ s, Real.negMulLog (p a))) =
                (m * m⁻¹) * (∑ a ∈ s, Real.negMulLog (p a)) := by ring
            _ = _ := by rw [hinv, one_mul]
    _ ≤ m * Real.negMulLog (m⁻¹ * (∑ a ∈ s, p a)) := hscaled
    _ = Real.negMulLog (∑ a ∈ s, p a) +
        (∑ a ∈ s, p a) * Real.log s.card := by
          simpa [m] using hentropyIdentity (∑ a ∈ s, p a)

/-- A probability vector on `Label`, with `correct` distinguished, has entropy
at most `h₂(error) + error log (|Label|-1)`. -/
theorem finiteShannonEntropy_le_finiteFanoEnvelope
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (p : Label → ℝ) (correct : Label)
    (hcard : 2 ≤ Fintype.card Label)
    (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) :
    finiteShannonEntropy p ≤
      finiteFanoEnvelope (Fintype.card Label) (1 - p correct) := by
  let rest : Finset Label := Finset.univ.erase correct
  have hrest : rest.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hcardRest : rest.card = 0 := Finset.card_eq_zero.mpr hEmpty
    have hcardEq : rest.card = Fintype.card Label - 1 := by
      simp [rest]
    omega
  have hrestSum : ∑ a ∈ rest, p a = 1 - p correct := by
    have hsplit := Finset.sum_erase_add (Finset.univ : Finset Label) p
      (Finset.mem_univ correct)
    dsimp [rest]
    linarith [hsum]
  have hrestEntropy :=
    sum_negMulLog_le_negMulLog_sum_add_mul_log_card rest hrest p
      (fun a _ha => hp a)
  rw [hrestSum] at hrestEntropy
  have hcardRest : rest.card = Fintype.card Label - 1 := by
    simp [rest]
  rw [hcardRest] at hrestEntropy
  have hsplitEntropy :
      (∑ a ∈ (Finset.univ : Finset Label).erase correct,
          Real.negMulLog (p a)) + Real.negMulLog (p correct) =
        finiteShannonEntropy p := by
    unfold finiteShannonEntropy
    exact Finset.sum_erase_add (Finset.univ : Finset Label)
      (fun a => Real.negMulLog (p a)) (Finset.mem_univ correct)
  have hcorrect : p correct = 1 - (1 - p correct) := by ring
  unfold finiteFanoEnvelope
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [← hcorrect]
  dsimp [rest] at hrestEntropy
  rw [← hsplitEntropy]
  calc
    (∑ a ∈ (Finset.univ : Finset Label).erase correct,
        Real.negMulLog (p a)) + Real.negMulLog (p correct) ≤
        ((1 - p correct).negMulLog +
          (1 - p correct) * Real.log (Fintype.card Label - 1 : ℕ)) +
            Real.negMulLog (p correct) :=
      add_le_add_left hrestEntropy _
    _ = (1 - p correct).negMulLog + Real.negMulLog (p correct) +
        (1 - p correct) * Real.log (Fintype.card Label - 1 : ℕ) := by
      ring

/-- Every posterior error lies in `[0,1]`. -/
theorem FinitePosteriorExperiment.posteriorError_mem_unitInterval
    (E : FinitePosteriorExperiment Label Observation) (y : Observation) :
    1 - E.posterior y (E.decode y) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · have hle : E.posterior y (E.decode y) ≤ 1 := by
      calc
        E.posterior y (E.decode y) ≤ ∑ a, E.posterior y a :=
          Finset.single_le_sum (fun a _ha => E.posterior_nonneg y a)
            (Finset.mem_univ (E.decode y))
        _ = 1 := E.posterior_sum_one y
    linarith
  · linarith [E.posterior_nonneg y (E.decode y)]

/-- The experiment's average error probability lies in `[0,1]`. -/
theorem FinitePosteriorExperiment.errorProbability_mem_unitInterval
    (E : FinitePosteriorExperiment Label Observation) :
    E.errorProbability ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · unfold FinitePosteriorExperiment.errorProbability
    exact Finset.sum_nonneg fun y _hy =>
      mul_nonneg (E.weight_nonneg y)
        (E.posteriorError_mem_unitInterval y).1
  · have hterm (y : Observation) :
        E.weight y * (1 - E.posterior y (E.decode y)) ≤ E.weight y := by
      nlinarith [E.weight_nonneg y,
        (E.posteriorError_mem_unitInterval y).1,
        (E.posteriorError_mem_unitInterval y).2]
    unfold FinitePosteriorExperiment.errorProbability
    calc
      (∑ y, E.weight y * (1 - E.posterior y (E.decode y))) ≤
          ∑ y, E.weight y := Finset.sum_le_sum fun y _hy => hterm y
      _ = 1 := E.weight_sum_one

/-- Exact finite-posterior Fano entropy inequality.  This proves both entropy
maximization steps: within each posterior error cloud and across observations. -/
theorem FinitePosteriorExperiment.conditionalEntropy_le_finiteFanoEnvelope
    [DecidableEq Label]
    (E : FinitePosteriorExperiment Label Observation)
    (hcard : 2 ≤ Fintype.card Label) :
    E.conditionalEntropy ≤
      finiteFanoEnvelope (Fintype.card Label) E.errorProbability := by
  let err : Observation → ℝ :=
    fun y => 1 - E.posterior y (E.decode y)
  have hrow (y : Observation) :
      finiteShannonEntropy (E.posterior y) ≤
        finiteFanoEnvelope (Fintype.card Label) (err y) :=
    finiteShannonEntropy_le_finiteFanoEnvelope
      (E.posterior y) (E.decode y) hcard
      (E.posterior_nonneg y) (E.posterior_sum_one y)
  have hweightedRows :
      E.conditionalEntropy ≤
        ∑ y, E.weight y *
          finiteFanoEnvelope (Fintype.card Label) (err y) := by
    unfold FinitePosteriorExperiment.conditionalEntropy
    exact Finset.sum_le_sum fun y _hy =>
      mul_le_mul_of_nonneg_left (hrow y) (E.weight_nonneg y)
  have hjensen := Real.strictConcave_binEntropy.concaveOn.le_map_sum
    (t := (Finset.univ : Finset Observation))
    (w := E.weight) (p := err)
    (fun y _hy => E.weight_nonneg y)
    (by simpa using E.weight_sum_one)
    (fun y _hy => E.posteriorError_mem_unitInterval y)
  simp only [smul_eq_mul] at hjensen
  have herrEq : (∑ y, E.weight y * err y) = E.errorProbability := by
    rfl
  rw [herrEq] at hjensen
  have hexpand :
      (∑ y, E.weight y *
        finiteFanoEnvelope (Fintype.card Label) (err y)) =
      (∑ y, E.weight y * Real.binEntropy (err y)) +
        E.errorProbability * Real.log (Fintype.card Label - 1 : ℕ) := by
    unfold finiteFanoEnvelope FinitePosteriorExperiment.errorProbability
    dsimp [err]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    congr 1
    calc
      (∑ y, E.weight y *
          ((1 - E.posterior y (E.decode y)) *
            Real.log (Fintype.card Label - 1 : ℕ))) =
          (∑ y, E.weight y *
            (1 - E.posterior y (E.decode y))) *
              Real.log (Fintype.card Label - 1 : ℕ) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro y _hy
            ring
      _ = _ := rfl
  calc
    E.conditionalEntropy ≤
        ∑ y, E.weight y *
          finiteFanoEnvelope (Fintype.card Label) (err y) := hweightedRows
    _ = (∑ y, E.weight y * Real.binEntropy (err y)) +
        E.errorProbability * Real.log (Fintype.card Label - 1 : ℕ) := hexpand
    _ ≤ Real.binEntropy E.errorProbability +
        E.errorProbability * Real.log (Fintype.card Label - 1 : ℕ) :=
      add_le_add_left hjensen _
    _ = finiteFanoEnvelope (Fintype.card Label) E.errorProbability := by
      rfl

/-- The standard coarse Fano entropy inequality
`H(Label | Observation) ≤ log 2 + P(error) log |Label|`. -/
theorem FinitePosteriorExperiment.conditionalEntropy_le_log_two_add_error_mul_log_card
    [DecidableEq Label]
    (E : FinitePosteriorExperiment Label Observation)
    (hcard : 2 ≤ Fintype.card Label) :
    E.conditionalEntropy ≤
      Real.log 2 + E.errorProbability * Real.log (Fintype.card Label) := by
  have hexact := E.conditionalEntropy_le_finiteFanoEnvelope hcard
  have herrNonneg := E.errorProbability_mem_unitInterval.1
  have hlog :
      Real.log (Fintype.card Label - 1 : ℕ) ≤
        Real.log (Fintype.card Label : ℕ) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < Fintype.card Label - 1 by omega)
    · exact_mod_cast (Nat.sub_le (Fintype.card Label) 1)
  unfold finiteFanoEnvelope at hexact
  calc
    E.conditionalEntropy ≤
        Real.binEntropy E.errorProbability +
          E.errorProbability * Real.log (Fintype.card Label - 1 : ℕ) := hexact
    _ ≤ Real.log 2 + E.errorProbability * Real.log (Fintype.card Label : ℕ) :=
      add_le_add Real.binEntropy_le_log_two
        (mul_le_mul_of_nonneg_left hlog herrNonneg)

/-- Genuine finite-posterior Fano theorem.  If `information` is related to the
posterior experiment by the uniform-label entropy chain rule, the decoding
error obeys the exact q-ary Fano inequality. -/
theorem FinitePosteriorExperiment.fano_exact
    [DecidableEq Label]
    (E : FinitePosteriorExperiment Label Observation)
    (information : ℝ)
    (hcard : 2 ≤ Fintype.card Label)
    (hchain :
      Real.log (Fintype.card Label) = information + E.conditionalEntropy) :
    Real.log (Fintype.card Label) - information ≤
      finiteFanoEnvelope (Fintype.card Label) E.errorProbability := by
  rw [hchain]
  simpa only [add_sub_cancel_left] using
    E.conditionalEntropy_le_finiteFanoEnvelope hcard

/-- The familiar finite Fano lower bound
`P(error) ≥ 1 - (I + log 2) / log |Label|`. -/
theorem FinitePosteriorExperiment.fano_errorProbability_lower
    [DecidableEq Label]
    (E : FinitePosteriorExperiment Label Observation)
    (information : ℝ)
    (hcard : 2 ≤ Fintype.card Label)
    (hchain :
      Real.log (Fintype.card Label) = information + E.conditionalEntropy) :
    1 - (information + Real.log 2) /
        Real.log (Fintype.card Label) ≤ E.errorProbability := by
  have hcond := E.conditionalEntropy_le_log_two_add_error_mul_log_card hcard
  have hlogPos : 0 < Real.log (Fintype.card Label) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Fintype.card Label by omega)
  have hineq :
      Real.log (Fintype.card Label) ≤ information + Real.log 2 +
        E.errorProbability * Real.log (Fintype.card Label) := by
    calc
      Real.log (Fintype.card Label) =
          information + E.conditionalEntropy := hchain
      _ ≤ information +
          (Real.log 2 + E.errorProbability * Real.log (Fintype.card Label)) :=
        add_le_add_right hcond information
      _ = _ := by ring
  have hrearranged :
      Real.log (Fintype.card Label) - (information + Real.log 2) ≤
        E.errorProbability * Real.log (Fintype.card Label) := by
    linarith
  have hquotient :
      (Real.log (Fintype.card Label) - (information + Real.log 2)) /
          Real.log (Fintype.card Label) ≤ E.errorProbability :=
    (div_le_iff₀ hlogPos).2 hrearranged
  convert hquotient using 1 <;> field_simp [hlogPos.ne'] <;> ring

end TomographyOracleCore
