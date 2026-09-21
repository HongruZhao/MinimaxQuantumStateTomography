import TomographyOracleCore.DecayHardTail

namespace TomographyOracleCore

/-!
# Finite scalar hard spectrum

This is the finite list underlying the scalar tail in `DecayHardTail`: two
equal head eigenvalues followed by `m` equal tail eigenvalues.  Matrix
realization and spectral ordering for an actual density operator are separate
later tasks.
-/

noncomputable def hardSpectrumHead (b : ℝ) : ℝ :=
  (1 - b) / 2

noncomputable def hardSpectrumTailEntry (m : ℕ) (b : ℝ) : ℝ :=
  b / (m : ℝ)

/-- The nonzero part of the paper's hard spectrum. -/
noncomputable def hardSpectrumList (m : ℕ) (b : ℝ) : List ℝ :=
  [hardSpectrumHead b, hardSpectrumHead b] ++
    List.replicate m (hardSpectrumTailEntry m b)

@[simp] theorem hardSpectrumList_length (m : ℕ) (b : ℝ) :
    (hardSpectrumList m b).length = m + 2 := by
  simp [hardSpectrumList]

/-- The `m` repeated tail entries carry total mass `b`. -/
theorem hardSpectrumTailBlock_sum
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) :
    (List.replicate m (hardSpectrumTailEntry m b)).sum = b := by
  have hmne : (m : ℝ) ≠ 0 := by
    have : 0 < (m : ℝ) := by exact_mod_cast hm
    exact this.ne'
  rw [List.sum_replicate, nsmul_eq_mul]
  unfold hardSpectrumTailEntry
  field_simp [hmne]

/-- The hard spectrum is normalized. -/
theorem hardSpectrumList_sum
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) :
    (hardSpectrumList m b).sum = 1 := by
  simp only [hardSpectrumList, List.sum_append, List.sum_cons, List.sum_nil,
    add_zero]
  rw [hardSpectrumTailBlock_sum m b hm]
  unfold hardSpectrumHead
  ring

theorem hardSpectrumHead_nonnegative
    (b : ℝ) (hb1 : b ≤ 1) :
    0 ≤ hardSpectrumHead b := by
  unfold hardSpectrumHead
  linarith

theorem hardSpectrumTailEntry_nonnegative
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b) :
    0 ≤ hardSpectrumTailEntry m b := by
  unfold hardSpectrumTailEntry
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  exact div_nonneg hb0 hmpos.le

/-- Every entry is nonnegative when `0 ≤ b ≤ 1`. -/
theorem hardSpectrumList_nonnegative
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    ∀ x ∈ hardSpectrumList m b, 0 ≤ x := by
  intro x hx
  rw [hardSpectrumList, List.mem_append] at hx
  rcases hx with hx | hx
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact hardSpectrumHead_nonnegative b hb1
    · exact hardSpectrumHead_nonnegative b hb1
  · rw [List.eq_of_mem_replicate hx]
    exact hardSpectrumTailEntry_nonnegative m b hm hb0

/-- Under the paper's small-tail condition, each head eigenvalue is at least
each repeated tail eigenvalue. -/
theorem hardSpectrum_head_ge_tail
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hbquarter : b ≤ 1 / 4) :
    hardSpectrumTailEntry m b ≤ hardSpectrumHead b := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hhead0 : 0 ≤ hardSpectrumHead b := by
    apply hardSpectrumHead_nonnegative
    norm_num at hbquarter ⊢
    linarith
  have hbhead : b ≤ hardSpectrumHead b := by
    unfold hardSpectrumHead
    norm_num at hbquarter ⊢
    linarith
  unfold hardSpectrumTailEntry
  apply (div_le_iff₀ hmpos).2
  exact hbhead.trans (by nlinarith)

/-- Sum of all entries after discarding the first `s`. -/
noncomputable def hardSpectrumTailSum (m : ℕ) (b : ℝ) (s : ℕ) : ℝ :=
  ((hardSpectrumList m b).drop s).sum

theorem hardSpectrumTailSum_one
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) :
    hardSpectrumTailSum m b 1 = (1 + b) / 2 := by
  change hardSpectrumHead b +
      (List.replicate m (hardSpectrumTailEntry m b)).sum = (1 + b) / 2
  rw [hardSpectrumTailBlock_sum m b hm]
  unfold hardSpectrumHead
  ring

/-- Dropping `k` entries from a constant block leaves `m-k` copies. -/
theorem sum_drop_replicate_real (m k : ℕ) (x : ℝ) :
    ((List.replicate m x).drop k).sum = ((m - k : ℕ) : ℝ) * x := by
  simp [List.sum_replicate, nsmul_eq_mul]

theorem hardSpectrumTailSum_middle
    (m s : ℕ) (b : ℝ) (hs2 : 2 ≤ s) (hsm : s ≤ m + 1) :
    hardSpectrumTailSum m b s =
      b * (((m : ℝ) + 2 - (s : ℝ)) / (m : ℝ)) := by
  have hsrepr : s = (s - 2) + 2 := by omega
  have hdrop :
      (hardSpectrumList m b).drop s =
        List.replicate (m - (s - 2)) (hardSpectrumTailEntry m b) := by
    rw [hsrepr]
    simp [hardSpectrumList]
  unfold hardSpectrumTailSum
  rw [hdrop, List.sum_replicate, nsmul_eq_mul]
  have hnat : m - (s - 2) = m + 2 - s := by omega
  rw [hnat]
  have hle : s ≤ m + 2 := by omega
  rw [Nat.cast_sub hle]
  push_cast
  unfold hardSpectrumTailEntry
  ring

theorem hardSpectrumTailSum_high
    (m s : ℕ) (b : ℝ) (hhigh : m + 2 ≤ s) :
    hardSpectrumTailSum m b s = 0 := by
  unfold hardSpectrumTailSum
  rw [List.drop_eq_nil_of_le]
  · simp
  · simpa using hhigh

/-- The suffix sums of the finite hard spectrum are exactly the piecewise
tail function from `DecayHardTail` at every positive truncation index. -/
theorem hardSpectrumTailSum_eq_hardFamilyTail
    (m s : ℕ) (b : ℝ) (hm : 1 ≤ m) (hs1 : 1 ≤ s) :
    hardSpectrumTailSum m b s = hardFamilyTail m b s := by
  by_cases hsone : s = 1
  · subst s
    rw [hardSpectrumTailSum_one m b hm, hardFamilyTail_one]
  · have hs2 : 2 ≤ s := by omega
    by_cases hsm : s ≤ m + 1
    · rw [hardSpectrumTailSum_middle m s b hs2 hsm,
        hardFamilyTail_middle m s b hs2 hsm]
    · have hhigh : m + 2 ≤ s := by omega
      rw [hardSpectrumTailSum_high m s b hhigh,
        hardFamilyTail_high m s b hhigh]

end TomographyOracleCore
