import TomographyOracleCore.Revision.SparseSampleSuprema

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseNormSplitting

open SparseCoefficientGeometry SparseSampleSuprema
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Splitting the support into two pieces compares adjacent sparsity scales. -/
theorem sparseNorm_le_two_mul {k m : ℕ} (hkm : k ≤ 2 * m) (X : ι → E) :
    sparseNorm X k ≤ 2 * sparseNorm X m := by
  apply sparseNorm_le
  intro y hy
  by_cases hym : (support y).card ≤ m
  · have h := synthesis_norm_le_sparseNorm (X := X) (show Admissible m Finset.univ y from
      ⟨hy.1, hym, hy.2.2⟩)
    linarith [sparseNorm_nonneg X m]
  have hm : m ≤ (support y).card := Nat.le_of_lt (Nat.lt_of_not_ge hym)
  obtain ⟨J, hJsub, hJc⟩ := Finset.exists_subset_card_eq hm
  have hrest : support (restrict Jᶜ y) ⊆ support y \ J := by
    intro i hi
    refine Finset.mem_sdiff.mpr ⟨support_restrict_subset Jᶜ y hi, ?_⟩
    intro hiJ
    have hne := mem_support.mp hi
    simp [restrict, hiJ] at hne
  have hc : (support (restrict Jᶜ y)).card ≤ m := by
    have h := Finset.card_le_card hrest
    rw [Finset.card_sdiff_of_subset hJsub, hJc] at h
    have hys := hy.2.1
    omega
  have hleft := synthesis_norm_le_sparseNorm (X := X) (hy.restrict_card J hJc.le)
  have hyr := hy.restrict Jᶜ
  have hright := synthesis_norm_le_sparseNorm (X := X)
    (show Admissible m Finset.univ (restrict Jᶜ y) from ⟨hyr.1, hc, hyr.2.2⟩)
  rw [← synthesis_restrict_add_compl X y J]
  exact (norm_add_le _ _).trans (by linarith)

end
end TomographyOracleCore.Revision.SparseNormSplitting
