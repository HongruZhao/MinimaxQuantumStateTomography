import TomographyOracleCore.Revision.SparseRecursionWeights
import TomographyOracleCore.Revision.SparseNetStep
import TomographyOracleCore.Revision.SparsePartitionFailure

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.SparseGoodPartitionBound

open SparseCoefficientGeometry SparseSampleSuprema SparseDeterministicRecurrence SparseNetStep
open SparseNetConstants SparseEntropyRate SparseDyadicScales SparseRecursionWeights
open SparseLevelProbability SparsePartitionFailure
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- 2^39 from the net step times 15 from the marginal threshold. -/
def recursionConstant : ℝ := 8246337208320
def crossConstant : ℝ := 32 * recursionConstant

theorem uniform_level_net_count {N J j : ℕ} (X : Fin N → E) (I : Finset (Fin N))
    {kappa s : ℝ} (hkappa : 0 < kappa) (hs : 0 < s)
    (hjJ : j ≤ J) (hJN : size J ≤ N)
    (hlevel : X ∉ levelFailure kappa s I j) :
    ∀ v ∈ levelNet I j (by simpa using (size_mono hjJ).trans hJN),
      (largeRows X v Iᶜ (levelThreshold kappa s N j * sparseNorm X (size J))).card < 8 * block j := by
  have hjN : size j ≤ N := (size_mono hjJ).trans hJN
  have hjN' : size j ≤ Fintype.card (Fin N) := by simpa using hjN
  have hNR : (0 : ℝ) < N := by exact_mod_cast (size_pos j).trans_le hjN
  have hsizeR : (0 : ℝ) < size j := by exact_mod_cast size_pos j
  have ht : 0 < levelThreshold kappa s N j := marginalThreshold_pos hkappa hs (by positivity)
  have hspec := chosenNet_spec I (block j) ((block_le_size j).trans hjN')
  intro v hv
  have hvnorm : ‖synthesis X v‖ ≤ sparseNorm X (size J) :=
    synthesis_norm_le_sparseNorm ((hspec.1 v hv).mono ((block_le_size j).trans (size_mono hjJ))
      (Finset.Subset.refl _))
  have hcount := good_level_rows hjN' hlevel hv
  simp only [Fintype.card_fin] at hcount
  exact lt_of_le_of_lt (Finset.card_le_card (largeRows_antitone_threshold X v Iᶜ
    (mul_le_mul_of_nonneg_left hvnorm ht.le))) hcount

/-- All dyadic cross norms on a good partition have the sharp sparse-energy
shape. The norm of the sparse synthesis remains on the right for the later
self-consistency step. -/
theorem crossNorm_le_on_good_partition {N : ℕ} (X : Fin N → E) (I : Finset (Fin N))
    {kappa s M : ℝ} (hkappa : 0 < kappa) (hs : 0 < s) (hM : 0 ≤ M)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M)
    (hgood : X ∉ partitionFailure kappa s I) (J : ℕ) (hJN : size J ≤ N) :
    crossNorm X (size J) I ≤ crossConstant *
      (amplification N * M + kappa * Real.sqrt s * signalWeight N J * sparseNorm X (size J)) := by
  let F := sparseNorm X (size J)
  have hF := sparseNorm_nonneg X (size J)
  have hD : 0 ≤ recursionConstant := by norm_num [recursionConstant]
  have hH : 0 ≤ kappa * Real.sqrt s := by positivity
  have hNR : (0 : ℝ) < N := by exact_mod_cast (size_pos J).trans_le hJN
  by_cases hF0 : F = 0
  · have hc := crossNorm_le_sparseNorm_sq X (size J) I
    change crossNorm X (size J) I ≤ F ^ 2 at hc
    norm_num only [hF0, zero_pow (by omega : 2 ≠ 0)] at hc
    apply hc.trans
    have ha : 0 ≤ amplification N := le_trans (by norm_num) (amplification_ge_one N)
    change 0 ≤ crossConstant * (amplification N * M + kappa * Real.sqrt s * signalWeight N J * F)
    rw [hF0]
    dsimp [crossConstant]
    simpa only [mul_zero, add_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 32) hD) (mul_nonneg ha hM)
  have hFp : 0 < F := lt_of_le_of_ne hF (Ne.symm hF0)
  have hzero : crossNorm X (size 0) I ≤ recursionConstant * M := by
    have h := crossNorm_le_card_mul_pair_bound (size 0) I hM hentry
    norm_num [size, block] at h
    norm_num [recursionConstant, size, block]
    nlinarith
  have hstep : ∀ j < J, crossNorm X (size (j + 1)) I ≤
      (17 / 16 : ℝ) * crossNorm X (size j) I + recursionConstant * M +
        recursionConstant * (kappa * Real.sqrt s) * signalWeight N (j + 1) * F := by
    intro j hj
    have hjJ : j + 1 ≤ J := by omega
    have hjN : size (j + 1) ≤ N := (size_mono hjJ).trans hJN
    have hjN' : size (j + 1) ≤ Fintype.card (Fin N) := by simpa using hjN
    have hlevels := good_partition_levels hgood (j + 1) hjN'
    have hspecL := chosenNet_spec I (block (j + 1)) ((block_le_size (j + 1)).trans hjN')
    have hspecR := chosenNet_spec Iᶜ (block (j + 1)) ((block_le_size (j + 1)).trans hjN')
    have hsizeR : (0 : ℝ) < size (j + 1) := by exact_mod_cast size_pos (j + 1)
    have ht : 0 < levelThreshold kappa s N (j + 1) := marginalThreshold_pos hkappa hs (by positivity)
    let tau := levelThreshold kappa s N (j + 1) * F
    have hcountL := uniform_level_net_count X I hkappa hs hjJ hJN hlevels.1
    have hcountR := uniform_level_net_count X Iᶜ hkappa hs hjJ hJN hlevels.2
    simp only [compl_compl] at hcountR
    have hrec := crossNorm_step (X := X) (block_pos (j + 1)) (by simpa [size] using hjN')
      I hM (mul_pos ht hFp) hentry (levelNet I (j + 1) hjN') (levelNet Iᶜ (j + 1) hjN')
      hspecL.1 hspecL.2.1 hspecR.1 hspecR.2.1 hcountL hcountR
    have hhalf : 32768 * block (j + 1) = size j := by rw [block_succ]; unfold size; ring
    rw [hhalf] at hrec
    have hid : Real.sqrt (size (j + 1) : ℝ) * tau =
        15 * (kappa * Real.sqrt s) * signalWeight N (j + 1) * F := by
      dsimp [tau, levelThreshold, marginalThreshold, signalWeight]
      calc
        _ = 15 * (kappa * Real.sqrt s) *
            (Real.sqrt (size (j + 1) : ℝ) * Real.sqrt (Real.sqrt ((N : ℝ) / size (j + 1)))) * F := by ring
        _ = _ := by rw [sqrt_ratio_scale hsizeR]
    have hhid : Real.sqrt (65536 * (block (j + 1) : ℝ)) *
        (levelThreshold kappa s N (j + 1) * F) =
        15 * (kappa * Real.sqrt s) * signalWeight N (j + 1) * F := by
      simpa only [size, Nat.cast_mul, Nat.cast_ofNat] using hid
    change crossNorm X (size (j + 1)) I ≤ _ at hrec
    dsimp [recursionConstant]
    nlinarith
  have hr := recursion_bound (fun j => crossNorm X (size j) I) (signalWeight N) J
    hD hM hH hF (signalWeight_nonneg N) (signalWeight_growth N) hzero hstep
  have hamp := mul_le_mul_of_nonneg_right (level_amplification_le hJN) hM
  have hmult := mul_le_mul_of_nonneg_left hamp (by positivity : 0 ≤ 32 * recursionConstant)
  change crossNorm X (size J) I ≤ 32 * recursionConstant *
    (amplification N * M + kappa * Real.sqrt s * signalWeight N J * F)
  nlinarith

end
end TomographyOracleCore.Revision.SparseGoodPartitionBound
