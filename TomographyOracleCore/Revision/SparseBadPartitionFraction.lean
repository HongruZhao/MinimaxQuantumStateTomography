import TomographyOracleCore.Revision.SparsePartitionFailure
import TomographyOracleCore.Revision.SparsePartitionDecoupling
import TomographyOracleCore.Revision.FiniteAverageIntegration

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseBadPartitionFraction

open MeasureTheory PeriodicForwardCovariance SparseCoefficientGeometry SparseSampleSuprema
open SparsePartitionDecoupling SparsePartitionFailure FiniteProbabilityAverage FiniteAverageIntegration
open BernoulliSmallBall
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def badFraction (kappa s : ℝ) {N : ℕ} (X : Fin N → E) : ℝ :=
  average (fairLaw N) (fun omega =>
    (partitionFailure kappa s (selectedIndices omega)).indicator (fun _ => (1 : ℝ)) X)

theorem badFraction_nonneg (kappa s : ℝ) {N : ℕ} (X : Fin N → E) : 0 ≤ badFraction kappa s X := by
  apply average_nonneg
  intro omega
  exact Set.indicator_nonneg (fun _ _ => zero_le_one) _

theorem badFraction_le_one (kappa s : ℝ) {N : ℕ} (X : Fin N → E) : badFraction kappa s X ≤ 1 := by
  rw [← average_const (fairLaw N) 1]
  apply average_mono
  intro omega
  classical
  by_cases h : X ∈ partitionFailure kappa s (selectedIndices omega) <;> simp [Set.indicator, h]

theorem measurable_badFraction (kappa s : ℝ) {N : ℕ} :
    Measurable (badFraction kappa s : (Fin N → E) → ℝ) :=
  measurable_average _ _ (fun omega => measurable_const.indicator (measurableSet_partitionFailure _ _ _))

theorem integrable_badFraction (mu : Measure E) [IsProbabilityMeasure mu]
    (kappa s : ℝ) {N : ℕ} :
    Integrable (badFraction kappa s : (Fin N → E) → ℝ) (Measure.pi (fun _ : Fin N => mu)) :=
  integrable_average _ _ (fun omega => (integrable_const 1).indicator (measurableSet_partitionFailure _ _ _))

theorem integral_badFraction_le [CompleteSpace E] {mu : Measure E} [IsProbabilityMeasure mu]
    {N : ℕ} (hN : 0 < N) {q kappa : ℝ}
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hkappa : 0 < kappa)
    (hL6 : HasL6L2Marginals mu kappa) (hs : 0 < ‖populationCovariance mu‖) :
    (∫ X : Fin N → E, badFraction kappa ‖populationCovariance mu‖ X
      ∂Measure.pi (fun _ : Fin N => mu)) ≤ 2 / (N : ℝ) ^ 3 := by
  unfold badFraction
  rw [integral_average _ _ (fun omega =>
    (integrable_const 1).indicator (measurableSet_partitionFailure _ _ _))]
  rw [← average_const (fairLaw N) (2 / (N : ℝ) ^ 3)]
  apply average_mono
  intro omega
  rw [integral_indicator (measurableSet_partitionFailure _ _ _)]
  simpa using measureReal_partitionFailure_le (ι := Fin N) (by simpa using hN)
    hfixed hkappa hL6 hs (selectedIndices omega)

def globalFailure (kappa s : ℝ) (N : ℕ) : Set (Fin N → E) := {X | (1 / 8 : ℝ) ≤ badFraction kappa s X}

theorem measurableSet_globalFailure (kappa s : ℝ) (N : ℕ) :
    MeasurableSet (globalFailure (E := E) kappa s N) :=
  measurableSet_le measurable_const (measurable_badFraction kappa s)

theorem measureReal_globalFailure_le [CompleteSpace E] {mu : Measure E} [IsProbabilityMeasure mu]
    {N : ℕ} (hN : 0 < N) {q kappa : ℝ}
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hkappa : 0 < kappa)
    (hL6 : HasL6L2Marginals mu kappa) (hs : 0 < ‖populationCovariance mu‖) :
    (Measure.pi (fun _ : Fin N => mu)).real (globalFailure kappa ‖populationCovariance mu‖ N) ≤
      16 / (N : ℝ) ^ 3 := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (badFraction_nonneg kappa ‖populationCovariance mu‖ (N := N)))
    (integrable_badFraction mu kappa ‖populationCovariance mu‖ (N := N)) (1 / 8)
  have hi := integral_badFraction_le hN hfixed hkappa hL6 hs
  change (1 / 8 : ℝ) * (Measure.pi (fun _ : Fin N => mu)).real
    (globalFailure kappa ‖populationCovariance mu‖ N) ≤ _ at hm
  rw [div_eq_mul_inv] at hi ⊢
  linarith

theorem average_cross_le_of_good_partitions {N k : ℕ} (X : Fin N → E) (kappa s : ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hgood : ∀ I : Finset (Fin N), X ∉ partitionFailure kappa s I → crossNorm X k I ≤ B) :
    averageCrossNorm X k ≤ B + badFraction kappa s X * sparseNorm X k ^ 2 := by
  have hpoint (omega : Fin N → Bool) : crossNorm X k (selectedIndices omega) ≤
      B + (partitionFailure kappa s (selectedIndices omega)).indicator (fun _ => (1 : ℝ)) X *
        sparseNorm X k ^ 2 := by
    classical
    by_cases h : X ∈ partitionFailure kappa s (selectedIndices omega)
    · simp only [Set.indicator_of_mem h, one_mul]
      linarith [crossNorm_le_sparseNorm_sq X k (selectedIndices omega)]
    · simp only [Set.indicator_of_notMem h, zero_mul, add_zero]
      exact hgood _ h
  have h := average_mono (fairLaw N) hpoint
  rw [average_add, FiniteProbabilityAverage.average_const, average_mul_const] at h
  exact h

theorem sparse_energy_le_of_good_fraction {N k : ℕ} (X : Fin N → E) (kappa s : ℝ)
    {q B : ℝ} (hq : 0 ≤ q) (hB : 0 ≤ B) (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (hgood : ∀ I : Finset (Fin N), X ∉ partitionFailure kappa s I → crossNorm X k I ≤ B)
    (hfrac : badFraction kappa s X ≤ 1 / 8) :
    sparseNorm X k ^ 2 ≤ 2 * q + 8 * B := by
  have h1 := sparseNorm_sq_le_diagonal_add_average_cross X k hq hfixed
  have h2 := average_cross_le_of_good_partitions X kappa s hB hgood
  have h3 := mul_le_mul_of_nonneg_right hfrac (sq_nonneg (sparseNorm X k))
  nlinarith

end
end TomographyOracleCore.Revision.SparseBadPartitionFraction
