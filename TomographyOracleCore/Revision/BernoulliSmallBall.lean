import TomographyOracleCore.Revision.BernoulliFourthMoment

namespace TomographyOracleCore.Revision.BernoulliSmallBall

open FiniteProbabilityAverage BernoulliFiniteAverage BernoulliFourthMoment
open scoped BigOperators
noncomputable section

theorem selectedSum_smallBall (p : ℝ) (hp : p ∈ Set.Icc 0 1) (hp0 : 0 < p)
    (hphalf : p ≤ 1 / 2) {k : ℕ} (a : Fin k → ℝ)
    (hmean : ∑ i, a i ≠ 0) (hcoeff : ∀ i, |a i| ≤ p * |∑ j, a j|) :
    1 / 512 ≤ probability (bernoulliLaw p hp k)
      {omega | p * |∑ i, a i| / 2 ≤ |selectedSum a omega|} := by
  let P := bernoulliLaw p hp k
  let Q := average P (fun omega => selectedSum a omega ^ 2)
  let F := average P (fun omega => selectedSum a omega ^ 4)
  let s := {omega | Q / 2 ≤ selectedSum a omega ^ 2}
  have hQlow : p ^ 2 * (∑ i, a i) ^ 2 ≤ Q := by
    dsimp [Q, P]
    rw [average_selectedSum_sq]
    have hnon : 0 ≤ p * (1 - p) * ∑ i, a i ^ 2 :=
      mul_nonneg (mul_nonneg hp.1 (by linarith [hp.2]))
        (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    linarith
  have hQ : 0 < Q := lt_of_lt_of_le (mul_pos (sq_pos_of_pos hp0) (sq_pos_of_ne_zero hmean)) hQlow
  have hF : F ≤ 128 * Q ^ 2 := average_selectedSum_fourth_le_second_sq p hp hphalf a hcoeff
  have hpz : Q ^ 2 ≤ 4 * F * probability P s := probability_sq_ge_half_average_sq P (selectedSum a)
  have hprob : 1 / 512 ≤ probability P s := by
    have h := mul_le_mul_of_nonneg_right hF (probability_nonneg P s)
    have hcancel : Q ^ 2 * 1 ≤ Q ^ 2 * (512 * probability P s) := by nlinarith
    have h : 1 ≤ 512 * probability P s := by
      by_contra hx
      have hneg := mul_pos (sq_pos_of_pos hQ) (sub_pos.mpr (lt_of_not_ge hx))
      nlinarith
    linarith
  refine hprob.trans (probability_mono P ?_)
  intro omega homega
  change Q / 2 ≤ selectedSum a omega ^ 2 at homega
  change p * |∑ i, a i| / 2 ≤ |selectedSum a omega|
  have hsq : (p * |∑ i, a i| / 2) ^ 2 ≤ |selectedSum a omega| ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_abs (∑ i, a i)]
  exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).1 hsq

def selectedIndices {k : ℕ} (omega : Fin k → Bool) : Finset (Fin k) :=
  Finset.univ.filter fun i => omega i = true

theorem selectedSum_one_eq_card {k : ℕ} (omega : Fin k → Bool) :
    selectedSum (fun _ => 1) omega = ((selectedIndices omega).card : ℝ) := by
  simp only [selectedSum, one_mul, selectedIndices, Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases h : omega i <;> simp [bitValue, h]

theorem average_selected_card (p : ℝ) (hp : p ∈ Set.Icc 0 1) (k : ℕ) :
    average (bernoulliLaw p hp k) (fun omega => ((selectedIndices omega).card : ℝ)) = p * k := by
  simp_rw [← selectedSum_one_eq_card]
  rw [average_selectedSum]
  simp

theorem selected_card_tail {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {k : ℕ} (hk : 0 < k) :
    probability (bernoulliLaw (delta / 2048) (by constructor <;> linarith) k)
      {omega | delta * k < ((selectedIndices omega).card : ℝ)} ≤ 1 / 2048 := by
  have hp : delta / 2048 ∈ Set.Icc 0 1 := by constructor <;> linarith
  have h := markov (bernoulliLaw (delta / 2048) hp k)
    (f := fun omega => ((selectedIndices omega).card : ℝ))
    (fun _ => Nat.cast_nonneg _) (a := delta * k) (by positivity)
  rw [average_selected_card] at h
  have hdk : 0 < delta * (k : ℝ) := by positivity
  nlinarith

/-- A single realization has small rank and preserves a fixed fraction of
the coordinates whose Bernoulli sums satisfy the elementary small-ball bound. -/
theorem exists_sparse_selection_preserving_rows
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (a : Fin m → Fin k → ℝ) (I : Finset (Fin m)) {t : ℝ}
    (hI : (m : ℝ) / 2 ≤ I.card)
    (hrow : ∀ i ∈ I,
      1 / 512 ≤ probability (bernoulliLaw (delta / 2048) (by constructor <;> linarith) k)
        {omega | t ≤ |selectedSum (a i) omega|}) :
    ∃ omega : Fin k → Bool,
      ((selectedIndices omega).card : ℝ) ≤ delta * k ∧
      (m : ℝ) / 2048 ≤ ((I.filter fun i => t ≤ |selectedSum (a i) omega|).card : ℝ) := by
  classical
  have hp : delta / 2048 ∈ Set.Icc 0 1 := by constructor <;> linarith
  let P := bernoulliLaw (delta / 2048) hp k
  let bad := {omega : Fin k → Bool | delta * k < ((selectedIndices omega).card : ℝ)}
  let good := fun i => {omega : Fin k → Bool | t ≤ |selectedSum (a i) omega|}
  let f : (Fin k → Bool) → ℝ := fun omega =>
    ∑ i ∈ I, ((good i \ bad).indicator (fun _ => (1 : ℝ))) omega
  have havg : (m : ℝ) / 2048 ≤ average P f := by
    have heq : average P f = ∑ i ∈ I, probability P (good i \ bad) := by
      unfold average f probability
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      rfl
    rw [heq]
    calc
      _ ≤ (I.card : ℝ) * (1 / 1024) := by linarith
      _ = ∑ _i ∈ I, (1 / 1024 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        have hsmall := hrow i hi
        have htail := selected_card_tail hdelta hdelta1 hk
        have hdiff := probability_sub_le_diff P (good i) bad
        change 1 / 512 ≤ probability P (good i) at hsmall
        change probability P bad ≤ 1 / 2048 at htail
        linarith
  obtain ⟨omega, homega⟩ := exists_average_le P f
  have hfpos : 0 < f omega := lt_of_lt_of_le (by positivity : (0 : ℝ) < (m : ℝ) / 2048)
    (havg.trans homega)
  have hnotbad : omega ∉ bad := by
    intro hb
    have hz : f omega = 0 := by
      unfold f
      apply Finset.sum_eq_zero
      intro i _
      exact Set.indicator_of_notMem (by simp [hb]) _
    rw [hz] at hfpos
    exact lt_irrefl _ hfpos
  refine ⟨omega, le_of_not_gt hnotbad, ?_⟩
  have heq : f omega = ((I.filter fun i => t ≤ |selectedSum (a i) omega|).card : ℝ) := by
    unfold f
    simp only [Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : t ≤ |selectedSum (a i) omega|
    · have hmem : omega ∈ good i := hi
      simp only [Set.indicator_of_mem (show omega ∈ good i \ bad from ⟨hmem, hnotbad⟩),
        if_pos hi, Nat.cast_one]
    · have hmem : omega ∉ good i := hi
      simp only [Set.indicator_of_notMem (show omega ∉ good i \ bad from fun h => hmem h.1),
        if_neg hi, Nat.cast_zero]
  rw [← heq]
  exact havg.trans homega

end
end TomographyOracleCore.Revision.BernoulliSmallBall
