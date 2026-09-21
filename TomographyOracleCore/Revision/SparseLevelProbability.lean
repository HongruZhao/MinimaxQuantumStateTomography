import TomographyOracleCore.Revision.SparseDyadicScales
import TomographyOracleCore.Revision.SparseNetFailure
import TomographyOracleCore.Revision.SparseCoefficientNets

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseLevelProbability

open MeasureTheory PeriodicForwardCovariance SparseCoefficientGeometry SparseSampleSuprema
open SparseConditionalRows SparseDeterministicRecurrence SparseNetFailure SparseCoefficientNets
open SparseEntropyRate SparseNetConstants SparseDyadicScales FixedNormSixthTail
open scoped BigOperators InnerProductSpace ENNReal
noncomputable section
variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def chosenNet (I : Finset ι) (h : ℕ) (hh : h ≤ Fintype.card ι) : Finset (ι → ℝ) :=
  Classical.choose (exists_sparse_net I hh (by norm_num [netRadius] : 0 < netRadius))

theorem chosenNet_spec (I : Finset ι) (h : ℕ) (hh : h ≤ Fintype.card ι) :
    (∀ v ∈ chosenNet I h hh, Admissible h I v) ∧
    (∀ y, Admissible h I y → ∃ v ∈ chosenNet I h hh,
      coefficientNorm (fun i => y i - v i) ≤ netRadius ∧
      (support (fun i => y i - v i)).card ≤ h) ∧
    ((chosenNet I h hh).card : ℝ) ≤ (Fintype.card ι).choose h * (1 + 2 / netRadius) ^ h :=
  Classical.choose_spec (exists_sparse_net I hh (by norm_num [netRadius] : 0 < netRadius))

def levelNet (I : Finset ι) (j : ℕ) (hN : size j ≤ Fintype.card ι) : Finset (ι → ℝ) :=
  chosenNet I (block j) ((block_le_size j).trans hN)

def levelThreshold (kappa s : ℝ) (N j : ℕ) : ℝ := marginalThreshold kappa s ((N : ℝ) / size j)

def levelFailure (kappa s : ℝ) (I : Finset ι) (j : ℕ) : Set (ι → E) :=
  if hN : size j ≤ Fintype.card ι then
    netFailure I (levelNet I j hN) (8 * block j) (levelThreshold kappa s (Fintype.card ι) j)
  else ∅

theorem measurableSet_levelFailure (kappa s : ℝ) (I : Finset ι) (j : ℕ) :
    MeasurableSet (levelFailure (E := E) kappa s I j) := by
  classical
  unfold levelFailure
  split_ifs
  · exact measurableSet_netFailure _ _ _ _
  · exact MeasurableSet.empty

theorem measureReal_levelFailure_le [CompleteSpace E] {mu : Measure E} [IsProbabilityMeasure mu]
    {q kappa : ℝ} (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hkappa : 0 < kappa)
    (hL6 : HasL6L2Marginals mu kappa) (hs : 0 < ‖populationCovariance mu‖)
    (I : Finset ι) (j : ℕ) :
    (Measure.pi (fun _ : ι => mu)).real (levelFailure kappa ‖populationCovariance mu‖ I j) ≤
      1 / (Fintype.card ι : ℝ) ^ 4 := by
  classical
  by_cases hN : size j ≤ Fintype.card ι
  · rw [levelFailure, dif_pos hN]
    have hsize : (0 : ℝ) < size j := by exact_mod_cast size_pos j
    have hNR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast (size_pos j).trans_le hN
    have hL : 0 < (Fintype.card ι : ℝ) / size j := by positivity
    have ht : 0 < levelThreshold kappa ‖populationCovariance mu‖ (Fintype.card ι) j :=
      marginalThreshold_pos hkappa hs hL
    have htail : ∀ v : E, mu {x | levelThreshold kappa ‖populationCovariance mu‖
        (Fintype.card ι) j * ‖v‖ < |⟪x, v⟫_ℝ|} ≤
        ENNReal.ofReal (marginalTailRate ((Fintype.card ι : ℝ) / size j)) := by
      intro v
      have h := measure_marginal_tail_le hfixed hL6 ht v
      rw [levelThreshold, sixth_tail_rate hkappa hs hL] at h
      exact h
    have hspec := chosenNet_spec I (block j) ((block_le_size j).trans hN)
    have hprob := measureReal_netFailure_le mu I (levelNet I j hN) (8 * block j)
      (levelThreshold kappa ‖populationCovariance mu‖ (Fintype.card ι) j)
      (fun v hv => (hspec.1 v hv).2.2) (marginalTailRate_pos hL).le htail
    calc
      _ ≤ ((levelNet I j hN).card : ℝ) * (Fintype.card ι).choose (8 * block j) *
          marginalTailRate ((Fintype.card ι : ℝ) / size j) ^ (8 * block j) := hprob
      _ ≤ ((Fintype.card ι).choose (block j) * (1 + 2 / netRadius) ^ block j) *
          (Fintype.card ι).choose (8 * block j) *
          marginalTailRate ((Fintype.card ι : ℝ) / size j) ^ (8 * block j) := by
        apply mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hspec.2.2 (Nat.cast_nonneg _))
          (pow_nonneg (marginalTailRate_pos hL).le _)
      _ ≤ (1 / (256 * ((Fintype.card ι : ℝ) / size j) ^ 2)) ^ block j := by
        simpa only [size, Nat.cast_mul, Nat.cast_ofNat] using
          sparse_net_entropy_bound (block_pos j) hN
      _ ≤ _ := dyadic_rate_le_inv_four j hN
  · rw [levelFailure, dif_neg hN]
    simp only [measureReal_empty]
    positivity

theorem good_level_rows {kappa s : ℝ} {I : Finset ι} {j : ℕ}
    (hN : size j ≤ Fintype.card ι) {X : ι → E} (hX : X ∉ levelFailure kappa s I j)
    {v : ι → ℝ} (hv : v ∈ levelNet I j hN) :
    (largeRows X v Iᶜ (levelThreshold kappa s (Fintype.card ι) j * ‖synthesis X v‖)).card <
      8 * block j := by
  rw [levelFailure, dif_pos hN] at hX
  exact largeRows_card_lt_of_not_mem hX hv

end
end TomographyOracleCore.Revision.SparseLevelProbability
