import TomographyOracleCore.Revision.BernoulliSmallBall

namespace TomographyOracleCore.Revision.ElementarySparsifying

open FiniteProbabilityAverage BernoulliFiniteAverage BernoulliSmallBall
open scoped BigOperators
noncomputable section

theorem selectedSum_mask {k : ℕ} (a : Fin k → ℝ) (J : Finset (Fin k))
    (omega : Fin k → Bool) :
    selectedSum (fun j => if j ∈ J then 0 else a j) omega =
      ∑ j ∈ selectedIndices omega \ J, a j := by
  classical
  simp only [selectedSum, selectedIndices, Finset.sdiff_eq_filter,
    Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ J <;> cases h : omega j <;> simp [hj, h, bitValue]

theorem sum_heavy_add_light {k : ℕ} (a : Fin k → ℝ) (J : Finset (Fin k)) :
    (∑ j ∈ J, a j) + (∑ j, if j ∈ J then 0 else a j) = ∑ j, a j := by
  classical
  have hJ : (∑ j ∈ J, a j) = ∑ j, if j ∈ J then a j else 0 := by
    rw [← Finset.sum_filter]
    simp
  rw [hJ, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ∈ J <;> simp [hj]

theorem heavy_coordinate_card {k : ℕ} (y : Fin k → ℝ)
    (hy : (∑ j, y j ^ 2) ≤ 1) {b : ℝ} (hb : 0 < b) :
    (((Finset.univ.filter fun j => b < |y j|).card : ℝ) * b ^ 2) ≤ 1 := by
  classical
  let J := Finset.univ.filter fun j => b < |y j|
  calc
    _ = ∑ _j ∈ J, b ^ 2 := by simp [J]
    _ ≤ ∑ j ∈ J, y j ^ 2 := by
      apply Finset.sum_le_sum
      intro j hj
      have h := (Finset.mem_filter.mp hj).2
      have hs := (sq_le_sq₀ hb.le (abs_nonneg (y j))).2 h.le
      simpa only [sq_abs] using hs
    _ ≤ ∑ j, y j ^ 2 := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _ _ _ => sq_nonneg _)
    _ ≤ 1 := hy

/-- An elementary coordinate-sparsification theorem. The proof uses only
finite Bernoulli averages, their exact second/fourth moments, and a
second-moment lower bound. There is no anti-concentration premise.

The constants are deliberately generous: the eventual covariance theorem
requires existence of universal constants rather than their optimal values. -/
theorem exists_sparse_coordinates
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m)
    {delta a : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (ha : 0 < a)
    (T : Fin m → Fin k → ℝ) (y : Fin k → ℝ)
    (hy : (∑ j, y j ^ 2) ≤ 1)
    (hfull : ∀ i, a ≤ |∑ j, T i j * y j|)
    (hentry : ∀ i j, |T i j| ≤ delta * Real.sqrt (delta * k) * a / 16384) :
    ∃ J : Finset (Fin k), (J.card : ℝ) ≤ delta * k ∧
      (m : ℝ) / 2048 ≤
        ((Finset.univ.filter fun i => delta * a / 8192 ≤ |∑ j ∈ J, T i j * y j|).card : ℝ) := by
  classical
  have hdk : 0 < delta * (k : ℝ) := by positivity
  have hr : 0 < Real.sqrt (delta * k) := Real.sqrt_pos.mpr hdk
  let b := 2 / Real.sqrt (delta * k)
  have hb : 0 < b := by dsimp [b]; positivity
  let heavy := Finset.univ.filter fun j => b < |y j|
  have hheavy : 4 * (heavy.card : ℝ) ≤ delta * k := by
    have h := heavy_coordinate_card y hy hb
    have hb2 : b ^ 2 = 4 / (delta * k) := by
      dsimp [b]
      rw [div_pow, Real.sq_sqrt hdk.le]
      norm_num
    change (heavy.card : ℝ) * b ^ 2 ≤ 1 at h
    rw [hb2] at h
    have h' := (div_le_iff₀ hdk).1
      (show 4 * (heavy.card : ℝ) / (delta * k) ≤ 1 by
        convert h using 1 <;> ring)
    nlinarith
  let H := Finset.univ.filter fun i => a / 2 ≤ |∑ j ∈ heavy, T i j * y j|
  have ht : delta * a / 8192 ≤ a / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hdelta1 ha.le]
  by_cases hH : (m : ℝ) / 2 ≤ H.card
  · refine ⟨heavy, by linarith, ?_⟩
    have hsub : H ⊆ Finset.univ.filter fun i =>
        delta * a / 8192 ≤ |∑ j ∈ heavy, T i j * y j| := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht.trans (Finset.mem_filter.mp hi).2⟩
    have hc : (H.card : ℝ) ≤ ((Finset.univ.filter fun i =>
        delta * a / 8192 ≤ |∑ j ∈ heavy, T i j * y j|).card : ℝ) :=
      by exact_mod_cast Finset.card_le_card hsub
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ))]
  let I := Finset.univ \ H
  have hI : (m : ℝ) / 2 ≤ I.card := by
    have hc : (I.card : ℝ) + H.card = m := by
      have hnat : I.card + H.card = m := by
        simpa only [I, Finset.card_univ, Fintype.card_fin] using
          Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H)
      exact_mod_cast hnat
    linarith
  let light := fun i j => if j ∈ heavy then (0 : ℝ) else T i j * y j
  have hmean : ∀ i ∈ I, a / 2 ≤ |∑ j, light i j| := by
    intro i hi
    have hiH : i ∉ H := (Finset.mem_sdiff.mp hi).2
    have hsmall : |∑ j ∈ heavy, T i j * y j| < a / 2 := by
      exact not_le.mp (fun h => hiH (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have htri := abs_add_le (∑ j ∈ heavy, T i j * y j) (∑ j, light i j)
    have heq := sum_heavy_add_light (fun j => T i j * y j) heavy
    change (∑ j ∈ heavy, T i j * y j) + (∑ j, light i j) = _ at heq
    rw [heq] at htri
    linarith [hfull i]
  have hcoeff : ∀ i ∈ I, ∀ j, |light i j| ≤ (delta / 2048) * |∑ r, light i r| := by
    intro i hi j
    by_cases hj : j ∈ heavy
    · simp only [light, if_pos hj, abs_zero]
      positivity
    have hyj : |y j| ≤ b := le_of_not_gt
      (fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hbound := mul_le_mul (hentry i j) hyj (abs_nonneg _)
      (by positivity : 0 ≤ delta * Real.sqrt (delta * k) * a / 16384)
    have heq : (delta * Real.sqrt (delta * k) * a / 16384) * b = delta * a / 8192 := by
      dsimp [b]
      field_simp
      ring
    rw [heq] at hbound
    have hM := mul_le_mul_of_nonneg_left (hmean i hi) hdelta.le
    simp only [light, if_neg hj, abs_mul]
    nlinarith
  have hrow : ∀ i ∈ I,
      1 / 512 ≤ probability (bernoulliLaw (delta / 2048) (by constructor <;> linarith) k)
        {omega | delta * a / 8192 ≤ |selectedSum (light i) omega|} := by
    intro i hi
    have hM : ∑ j, light i j ≠ 0 := by
      have habs : 0 < |∑ j, light i j| := lt_of_lt_of_le (by linarith) (hmean i hi)
      exact abs_pos.mp habs
    have hs := selectedSum_smallBall (delta / 2048) (by constructor <;> linarith)
      (by positivity) (by linarith) (light i) hM (hcoeff i hi)
    refine hs.trans (probability_mono _ ?_)
    intro omega homega
    have hM' := mul_le_mul_of_nonneg_left (hmean i hi) hdelta.le
    change (delta / 2048) * |∑ j, light i j| / 2 ≤ |selectedSum (light i) omega| at homega
    change delta * a / 8192 ≤ |selectedSum (light i) omega|
    nlinarith
  obtain ⟨omega, hcard, hgood⟩ := exists_sparse_selection_preserving_rows hk hm
    hdelta hdelta1 light I hI hrow
  let J := selectedIndices omega \ heavy
  refine ⟨J, ?_, ?_⟩
  · have hc : (J.card : ℝ) ≤ ((selectedIndices omega).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : J ⊆ selectedIndices omega)
    exact hc.trans hcard
  · have heq (i : Fin m) : selectedSum (light i) omega = ∑ j ∈ J, T i j * y j :=
      selectedSum_mask (fun j => T i j * y j) heavy omega
    simp_rw [heq] at hgood
    have hc : ((I.filter fun i => delta * a / 8192 ≤ |∑ j ∈ J, T i j * y j|).card : ℝ) ≤
        ((Finset.univ.filter fun i => delta * a / 8192 ≤ |∑ j ∈ J, T i j * y j|).card : ℝ) := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ I))
    exact hgood.trans hc

end
end TomographyOracleCore.Revision.ElementarySparsifying
