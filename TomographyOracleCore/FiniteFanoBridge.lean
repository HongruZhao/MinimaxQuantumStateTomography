import TomographyOracleCore.FiniteFano
import TomographyOracleCore.FanoConstants

namespace TomographyOracleCore

/-!
# A finite joint-law bridge to the posterior Fano theorem

`FiniteFano` proves Fano's inequality for a normalized family of posterior
rows.  This file constructs those rows from a genuine finite joint
distribution.  Zero-probability observations are assigned the uniform
posterior; because their observation weight is zero, this choice has no effect
on conditional entropy or decoding error.

The Fano conclusion below can be used in either of two ways.

* One may bound the entropy-chain information
  `log |Label| - H(Label | Observation)` directly.
* One may supply a KL-form information bound together with the single explicit
  identity saying that the chosen KL expression equals that entropy-chain
  information.  This equality is the remaining KL/entropy bridge; no
  tomography lower bound is hidden in it.

No declaration in this file is an axiom.
-/

open scoped BigOperators

/-- A finite joint probability distribution whose label marginal is uniform.
The redundant total-mass field makes normalization of the constructed
observation distribution completely explicit. -/
structure FiniteUniformJoint (Label Observation : Type*)
    [Fintype Label] [Fintype Observation] where
  joint : Label → Observation → ℝ
  joint_nonneg : ∀ a y, 0 ≤ joint a y
  joint_sum_one : ∑ a, ∑ y, joint a y = 1
  label_marginal_uniform :
    ∀ a, ∑ y, joint a y = (Fintype.card Label : ℝ)⁻¹

namespace FiniteUniformJoint

variable {Label Observation : Type*}
  [Fintype Label] [Fintype Observation]

/-- Observation marginal of a finite joint law. -/
noncomputable def observationWeight
    (J : FiniteUniformJoint Label Observation) (y : Observation) : ℝ :=
  ∑ a, J.joint a y

/-- Posterior probability obtained by Bayes normalization.  On a
zero-probability observation we use the uniform vector. -/
noncomputable def posterior
    (J : FiniteUniformJoint Label Observation) (y : Observation) (a : Label) : ℝ :=
  if J.observationWeight y = 0 then
    (Fintype.card Label : ℝ)⁻¹
  else
    J.joint a y / J.observationWeight y

theorem observationWeight_nonneg
    (J : FiniteUniformJoint Label Observation) (y : Observation) :
    0 ≤ J.observationWeight y := by
  unfold observationWeight
  exact Finset.sum_nonneg fun a _ha => J.joint_nonneg a y

theorem observationWeight_sum_one
    (J : FiniteUniformJoint Label Observation) :
    ∑ y, J.observationWeight y = 1 := by
  unfold observationWeight
  rw [Finset.sum_comm]
  exact J.joint_sum_one

theorem posterior_nonneg
    (J : FiniteUniformJoint Label Observation) (y : Observation) (a : Label) :
    0 ≤ J.posterior y a := by
  unfold posterior
  split_ifs with hzero
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact div_nonneg (J.joint_nonneg a y) (J.observationWeight_nonneg y)

theorem posterior_sum_one
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (y : Observation) :
    ∑ a, J.posterior y a = 1 := by
  by_cases hzero : J.observationWeight y = 0
  · simp only [posterior, hzero, if_pos, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    exact mul_inv_cancel₀ hcard
  · simp only [posterior, hzero, if_false]
    rw [← Finset.sum_div]
    change J.observationWeight y / J.observationWeight y = 1
    exact div_self hzero

/-- Bayes reconstruction: the observation marginal times the constructed
posterior is exactly the original joint mass, including on zero-mass
observations. -/
theorem observationWeight_mul_posterior
    (J : FiniteUniformJoint Label Observation) (y : Observation) (a : Label) :
    J.observationWeight y * J.posterior y a = J.joint a y := by
  by_cases hzero : J.observationWeight y = 0
  · have hle : J.joint a y ≤ J.observationWeight y := by
      unfold observationWeight
      exact Finset.single_le_sum
        (fun b _hb => J.joint_nonneg b y) (Finset.mem_univ a)
    have hjointZero : J.joint a y = 0 := by
      linarith [J.joint_nonneg a y]
    simp [posterior, hzero, hjointZero]
  · simp only [posterior, hzero, if_false]
    exact mul_div_cancel₀ _ hzero

/-- Averaging the posterior against the observation marginal recovers the
uniform label marginal of the joint distribution. -/
theorem weighted_posterior_sum_eq_uniform
    (J : FiniteUniformJoint Label Observation) (a : Label) :
    ∑ y, J.observationWeight y * J.posterior y a =
      (Fintype.card Label : ℝ)⁻¹ := by
  simp_rw [J.observationWeight_mul_posterior]
  exact J.label_marginal_uniform a

/-- The finite posterior experiment canonically induced by a finite uniform
joint law and a decoder. -/
noncomputable def toPosteriorExperiment
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label) :
    FinitePosteriorExperiment Label Observation where
  weight := J.observationWeight
  posterior := J.posterior
  decode := decode
  weight_nonneg := J.observationWeight_nonneg
  weight_sum_one := J.observationWeight_sum_one
  posterior_nonneg := J.posterior_nonneg
  posterior_sum_one := J.posterior_sum_one

/-- The posterior experiment's decoding error is exactly one minus the joint
probability assigned to correctly decoded label-observation pairs. -/
theorem errorProbability_eq_one_sub_joint_decode
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label) :
    (J.toPosteriorExperiment decode).errorProbability =
      1 - ∑ y, J.joint (decode y) y := by
  unfold FinitePosteriorExperiment.errorProbability toPosteriorExperiment
  simp_rw [mul_sub, mul_one, J.observationWeight_mul_posterior]
  rw [Finset.sum_sub_distrib, J.observationWeight_sum_one]

/-- Information defined through the entropy chain rule.  This is the quantity
needed by the finite-posterior Fano theorem, independently of any KL formula. -/
noncomputable def entropyChainInformation
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label) : ℝ :=
  Real.log (Fintype.card Label) -
    (J.toPosteriorExperiment decode).conditionalEntropy

theorem entropy_chain
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label) :
    Real.log (Fintype.card Label) =
      J.entropyChainInformation decode +
        (J.toPosteriorExperiment decode).conditionalEntropy := by
  unfold entropyChainInformation
  ring

/-- The explicit finite posterior-KL sum suggested by the joint law.  The
factor `|Label|` is the reciprocal of the uniform label prior. -/
noncomputable def posteriorKLSum
    (J : FiniteUniformJoint Label Observation) : ℝ :=
  ∑ y, ∑ a,
    J.joint a y *
      Real.log ((Fintype.card Label : ℝ) * J.posterior y a)

/-- The one remaining finite KL/entropy identity needed to replace an
entropy-chain information bound by a posterior-KL bound.  It is deliberately a
named proposition, not an axiom or a field of the joint-law structure. -/
def PosteriorKLEntropyIdentity
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label) : Prop :=
  J.posteriorKLSum = J.entropyChainInformation decode

/-- Pointwise logarithmic identity behind the KL/entropy chain rule.  The
zero-posterior branch is handled separately, so no convention about
`0 * log 0` is hidden. -/
theorem joint_mul_log_card_mul_posterior
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation)
    (y : Observation) (a : Label) :
    J.joint a y *
        Real.log ((Fintype.card Label : ℝ) * J.posterior y a) =
      J.observationWeight y * J.posterior y a *
          Real.log (Fintype.card Label) -
        J.observationWeight y * Real.negMulLog (J.posterior y a) := by
  have hcard : (Fintype.card Label : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  by_cases hp : J.posterior y a = 0
  · have hjoint : J.joint a y = 0 := by
      rw [← J.observationWeight_mul_posterior y a, hp, mul_zero]
    simp [hp, hjoint, Real.negMulLog]
  · rw [← J.observationWeight_mul_posterior y a]
    rw [Real.log_mul hcard hp]
    unfold Real.negMulLog
    ring

/-- The posterior KL sum is exactly the entropy-chain information.  Hence the
named bridge proposition above is internally proved for every finite uniform
joint law; it is not an external assumption. -/
theorem posteriorKLEntropyIdentity_proved
    [Nonempty Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label) :
    J.PosteriorKLEntropyIdentity decode := by
  have hrow (y : Observation) :
      (∑ a, (J.observationWeight y * J.posterior y a *
          Real.log (Fintype.card Label) -
        J.observationWeight y * Real.negMulLog (J.posterior y a))) =
      J.observationWeight y * Real.log (Fintype.card Label) -
        J.observationWeight y *
          finiteShannonEntropy (J.posterior y) := by
    rw [Finset.sum_sub_distrib]
    unfold finiteShannonEntropy
    congr 1
    · rw [← Finset.sum_mul, ← Finset.mul_sum,
        J.posterior_sum_one y, mul_one]
    · rw [← Finset.mul_sum]
  unfold PosteriorKLEntropyIdentity posteriorKLSum entropyChainInformation
  simp_rw [J.joint_mul_log_card_mul_posterior]
  rw [Finset.sum_congr rfl (fun y _hy => hrow y)]
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, J.observationWeight_sum_one, one_mul]
  rfl

/-- Fano's lower expression is bounded by the decoding error for the posterior
experiment constructed from the joint distribution. -/
theorem fanoErrorLower_le_errorProbability_of_entropy_chain
    [Nonempty Label] [DecidableEq Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label)
    (information : ℝ)
    (hcard : 2 ≤ Fintype.card Label)
    (hchain :
      Real.log (Fintype.card Label) = information +
        (J.toPosteriorExperiment decode).conditionalEntropy) :
    fanoErrorLower information (Real.log (Fintype.card Label)) ≤
      (J.toPosteriorExperiment decode).errorProbability := by
  simpa only [fanoErrorLower] using
    (J.toPosteriorExperiment decode).fano_errorProbability_lower
      information hcard hchain

/-- The concrete `11/16` conclusion with the entropy chain rule and the
information upper bound both shown as premises. -/
theorem eleven_sixteenths_le_errorProbability_of_entropy_chain
    [Nonempty Label] [DecidableEq Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label)
    (information : ℝ)
    (hcard : 2 ≤ Fintype.card Label)
    (hchain :
      Real.log (Fintype.card Label) = information +
        (J.toPosteriorExperiment decode).conditionalEntropy)
    (hinformation : information ≤ Real.log (Fintype.card Label) / 16)
    (hlogTwo :
      4 * Real.log 2 ≤ Real.log (Fintype.card Label)) :
    (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment decode).errorProbability := by
  have hlogCard : 0 < Real.log (Fintype.card Label) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Fintype.card Label by omega)
  exact
    (fanoErrorLower_ge_eleven_sixteenths information
      (Real.log (Fintype.card Label)) hlogCard hinformation hlogTwo).trans
      (J.fanoErrorLower_le_errorProbability_of_entropy_chain
        decode information hcard hchain)

/-- Fano's lower expression for the canonical entropy-chain information is
bounded by the decoding error. -/
theorem fanoErrorLower_le_errorProbability
    [Nonempty Label] [DecidableEq Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label)
    (hcard : 2 ≤ Fintype.card Label) :
    fanoErrorLower (J.entropyChainInformation decode)
        (Real.log (Fintype.card Label)) ≤
      (J.toPosteriorExperiment decode).errorProbability := by
  exact J.fanoErrorLower_le_errorProbability_of_entropy_chain decode
    (J.entropyChainInformation decode) hcard (J.entropy_chain decode)

/-- The concrete `11/16` finite Fano conclusion from an upper bound on the
entropy-chain information. -/
theorem eleven_sixteenths_le_errorProbability_of_entropyChainInformation
    [Nonempty Label] [DecidableEq Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label)
    (hcard : 2 ≤ Fintype.card Label)
    (hinformation :
      J.entropyChainInformation decode ≤
        Real.log (Fintype.card Label) / 16)
    (hlogTwo :
      4 * Real.log 2 ≤ Real.log (Fintype.card Label)) :
    (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment decode).errorProbability := by
  exact J.eleven_sixteenths_le_errorProbability_of_entropy_chain decode
    (J.entropyChainInformation decode) hcard (J.entropy_chain decode)
    hinformation hlogTwo

/-- The same conclusion from a posterior-KL upper bound.  The exact remaining
bridge is exposed as `PosteriorKLEntropyIdentity`; no statistical or tomography
claim is bundled into this theorem. -/
theorem eleven_sixteenths_le_errorProbability_of_posteriorKLSum
    [Nonempty Label] [DecidableEq Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label)
    (hcard : 2 ≤ Fintype.card Label)
    (hidentity : J.PosteriorKLEntropyIdentity decode)
    (hinformation :
      J.posteriorKLSum ≤ Real.log (Fintype.card Label) / 16)
    (hlogTwo :
      4 * Real.log 2 ≤ Real.log (Fintype.card Label)) :
    (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment decode).errorProbability := by
  apply J.eleven_sixteenths_le_errorProbability_of_entropyChainInformation
    decode hcard
  · rw [← hidentity]
    exact hinformation
  · exact hlogTwo

/-- Fully internal finite KL-to-Fano bridge: no entropy-chain identity remains
as a theorem premise. -/
theorem eleven_sixteenths_le_errorProbability_of_posteriorKLSum_proved
    [Nonempty Label] [DecidableEq Label]
    (J : FiniteUniformJoint Label Observation) (decode : Observation → Label)
    (hcard : 2 ≤ Fintype.card Label)
    (hinformation :
      J.posteriorKLSum ≤ Real.log (Fintype.card Label) / 16)
    (hlogTwo :
      4 * Real.log 2 ≤ Real.log (Fintype.card Label)) :
    (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment decode).errorProbability := by
  exact J.eleven_sixteenths_le_errorProbability_of_posteriorKLSum decode
    hcard (J.posteriorKLEntropyIdentity_proved decode) hinformation hlogTwo

end FiniteUniformJoint

end TomographyOracleCore
