import TomographyOracleCore.Revision.MaximumPairMoments
import TomographyOracleCore.Revision.PeakySelfConsistency
import TomographyOracleCore.Revision.SparseUniformEnergy
import TomographyOracleCore.Revision.SparseDirectionalEnergy
import TomographyOracleCore.Candidate2PeakySparseReduction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.PeakyUniformEnvelope

open MeasureTheory PeriodicForwardCovariance PeriodicForwardCovariance.PeakySpread
open MaximumPairInner MaximumPairMoments SparseRecursionWeights SparseUniformEnergy
open SparseDirectionalEnergy SparseBadPartitionFraction PeakySelfConsistency
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]

def baseEnergy (q : ℝ) {N : ℕ} (X : Fin N → E) : ℝ :=
  q + amplification N * maximumPair X

def goodPeakyEnvelope (q kappa s lambda : ℝ) {N : ℕ} (X : Fin N → E) : ℝ :=
  uniformEnergyConstant ^ 2 * (baseEnergy q X +
    2 * (kappa ^ 2 * s) * Real.sqrt (N : ℝ) * Real.sqrt (lambda * baseEnergy q X) +
    lambda * (kappa ^ 2 * s) ^ 2 * (N : ℝ)) / (N : ℝ)

def peakyEnvelope (q kappa s lambda : ℝ) {N : ℕ} (X : Fin N → E) : ℝ :=
  goodPeakyEnvelope q kappa s lambda X +
    (globalFailure kappa s N).indicator (fun _ => q) X

theorem baseEnergy_nonneg {q : ℝ} (hq : 0 ≤ q) {N : ℕ} (X : Fin N → E) :
    0 ≤ baseEnergy q X := by
  have ha : 0 ≤ amplification N := le_trans (by norm_num) (amplification_ge_one N)
  exact add_nonneg hq (mul_nonneg ha (maximumPair_nonneg X))

theorem goodPeakyEnvelope_nonneg {q kappa s lambda : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hlambda : 0 ≤ lambda) {N : ℕ} (X : Fin N → E) :
    0 ≤ goodPeakyEnvelope q kappa s lambda X := by
  have hb := baseEnergy_nonneg hq X
  unfold goodPeakyEnvelope
  positivity

theorem peakyEnvelope_nonneg {q kappa s lambda : ℝ} (hq : 0 ≤ q) (hs : 0 ≤ s)
    (hlambda : 0 ≤ lambda) {N : ℕ} (X : Fin N → E) :
    0 ≤ peakyEnvelope q kappa s lambda X :=
  add_nonneg (goodPeakyEnvelope_nonneg hq hs hlambda X)
    (Set.indicator_nonneg (fun _ _ => hq) X)

theorem continuous_baseEnergy (q : ℝ) {N : ℕ} :
    Continuous (baseEnergy q : (Fin N → E) → ℝ) :=
  continuous_const.add (continuous_const.mul continuous_maximumPair)

theorem continuous_goodPeakyEnvelope (q kappa s lambda : ℝ) {N : ℕ} :
    Continuous (goodPeakyEnvelope q kappa s lambda : (Fin N → E) → ℝ) := by
  unfold goodPeakyEnvelope
  have hb := continuous_baseEnergy (E := E) (N := N) q
  fun_prop

theorem measurable_peakyEnvelope (q kappa s lambda : ℝ) {N : ℕ} :
    Measurable (peakyEnvelope q kappa s lambda : (Fin N → E) → ℝ) :=
  (continuous_goodPeakyEnvelope q kappa s lambda).measurable.add
    (measurable_const.indicator (measurableSet_globalFailure kappa s N))

theorem directionalPeakyMean_le_fixedNorm {N : ℕ} (hN : 0 < N) (lambda : ℝ)
    {q : ℝ} (X : Fin N → E) (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u : E) (hu : ‖u‖ ≤ 1) : directionalPeakyMean lambda X u ≤ q := by
  have hpoint (i : Fin N) : peakyTerm lambda (directionalSquares X u i) ≤ q := by
    apply (peakyTerm_le_self (directionalSquares_nonneg X u i)).trans
    have hi := abs_real_inner_le_norm (X i) u
    have hmul := mul_le_mul_of_nonneg_left hu (norm_nonneg (X i))
    have hb : |⟪X i, u⟫_ℝ| ≤ ‖X i‖ := hi.trans (by simpa using hmul)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    dsimp [directionalSquares]
    nlinarith [hfixed i, sq_abs ⟪X i, u⟫_ℝ]
  unfold directionalPeakyMean peakyMean empiricalMean
  calc
    _ ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, q :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hpoint i)) (by positivity)
    _ = q := by simp [show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne']

theorem exceedance_card_le_lambda_sum {N : ℕ} (lambda : ℝ) (X : Fin N → E) (u : E) :
    ((directionalExceedanceSet lambda X u).card : ℝ) ≤
      lambda * ∑ i ∈ directionalExceedanceSet lambda X u, directionalSquares X u i := by
  classical
  calc
    _ = ∑ _i ∈ directionalExceedanceSet lambda X u, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ directionalExceedanceSet lambda X u, lambda * directionalSquares X u i := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Finset.mem_filter.mp hi).2.le
    _ = _ := by rw [Finset.mul_sum]

theorem directionalPeakyMean_le_goodEnvelope {N : ℕ} (hN : 0 < N)
    {q kappa s lambda : ℝ} (hq : 0 ≤ q) (hkappa : 0 < kappa) (hs : 0 < s)
    (hlambda : 0 < lambda) (X : Fin N → E) (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (hgood : X ∉ globalFailure kappa s N) (u : E) (hu : ‖u‖ ≤ 1) :
    directionalPeakyMean lambda X u ≤ goodPeakyEnvelope q kappa s lambda X := by
  let I := directionalExceedanceSet lambda X u
  have henergy : (∑ i ∈ I, directionalSquares X u i) ≤ uniformEnergyConstant *
      (baseEnergy q X + kappa ^ 2 * s * Real.sqrt ((N : ℝ) * (I.card : ℝ))) := by
    exact (directional_energy_le_sparseNorm_sq X I u hu).trans
      (sparseNorm_sq_le_uniform X hkappa hs (maximumPair_nonneg X) hq
        (abs_inner_le_maximumPair X) hfixed hgood I.card (by simpa using Finset.card_le_univ I))
  have h := peaky_scalar_bound (Nat.cast_pos.mpr hN) (Nat.cast_nonneg I.card)
    hlambda uniformEnergyConstant_ge_one (baseEnergy_nonneg hq X)
    (mul_nonneg (sq_nonneg kappa) hs.le) henergy (exceedance_card_le_lambda_sum lambda X u)
  rw [directionalPeakyMean_eq_inv_mul_sum_exceedanceSet]
  simpa only [goodPeakyEnvelope, I, div_eq_mul_inv, mul_comm] using h

/-- One measurable envelope controls the peaky process simultaneously over
the whole unit ball, including on the exceptional sparse-energy event. -/
theorem directionalPeakyMean_le_envelope {N : ℕ} (hN : 0 < N)
    {q kappa s lambda : ℝ} (hq : 0 ≤ q) (hkappa : 0 < kappa) (hs : 0 < s)
    (hlambda : 0 < lambda) (X : Fin N → E) (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (u : E) (hu : ‖u‖ ≤ 1) : directionalPeakyMean lambda X u ≤ peakyEnvelope q kappa s lambda X := by
  classical
  by_cases hgood : X ∈ globalFailure kappa s N
  · rw [peakyEnvelope, Set.indicator_of_mem hgood]
    exact (directionalPeakyMean_le_fixedNorm hN lambda X hfixed u hu).trans
      (le_add_of_nonneg_left (goodPeakyEnvelope_nonneg hq hs.le hlambda.le X))
  · rw [peakyEnvelope, Set.indicator_of_notMem hgood, add_zero]
    exact directionalPeakyMean_le_goodEnvelope hN hq hkappa hs hlambda X hfixed hgood u hu

theorem integrable_baseEnergy {mu : Measure E} [IsProbabilityMeasure mu]
    {q : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q) {N : ℕ} :
    Integrable (baseEnergy q : (Fin N → E) → ℝ) (Measure.pi (fun _ : Fin N => mu)) :=
  (integrable_const q).add ((integrable_maximumPair hfixed hq).const_mul (amplification N))

theorem integrable_sqrt_lambda_baseEnergy {mu : Measure E} [IsProbabilityMeasure mu]
    {q lambda : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q) (hlambda : 0 ≤ lambda) {N : ℕ} :
    Integrable (fun X : Fin N → E => Real.sqrt (lambda * baseEnergy q X))
      (Measure.pi (fun _ : Fin N => mu)) := by
  apply (integrable_const (Real.sqrt (lambda * (q + amplification N * q)))).mono'
    (continuous_const.mul (continuous_baseEnergy q)).sqrt.aestronglyMeasurable
  filter_upwards [ae_sample_fixedNorm hfixed] with X hX
  change ‖Real.sqrt (lambda * baseEnergy q X)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply Real.sqrt_le_sqrt
  apply mul_le_mul_of_nonneg_left _ hlambda
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (maximumPair_le_fixedNorm X hq hX)
    (le_trans (by norm_num) (amplification_ge_one N)))

theorem integrable_goodPeakyEnvelope {mu : Measure E} [IsProbabilityMeasure mu]
    {q kappa s lambda : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    (hlambda : 0 ≤ lambda) {N : ℕ} :
    Integrable (goodPeakyEnvelope q kappa s lambda : (Fin N → E) → ℝ)
      (Measure.pi (fun _ : Fin N => mu)) :=
  (((integrable_baseEnergy hfixed hq).add
    ((integrable_sqrt_lambda_baseEnergy hfixed hq hlambda).const_mul
      (2 * (kappa ^ 2 * s) * Real.sqrt (N : ℝ)))).add
    (integrable_const (lambda * (kappa ^ 2 * s) ^ 2 * (N : ℝ)))).const_mul
      (uniformEnergyConstant ^ 2) |>.div_const (N : ℝ)

theorem integrable_peakyEnvelope {mu : Measure E} [IsProbabilityMeasure mu]
    {q kappa s lambda : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    (hlambda : 0 ≤ lambda) {N : ℕ} :
    Integrable (peakyEnvelope q kappa s lambda : (Fin N → E) → ℝ)
      (Measure.pi (fun _ : Fin N => mu)) :=
  (integrable_goodPeakyEnvelope hfixed hq hlambda).add
    ((integrable_const q).indicator (measurableSet_globalFailure kappa s N))

end
end TomographyOracleCore.Revision.PeakyUniformEnvelope
