import TomographyOracleCore.Revision.SparseNetQuantileTransfer
import TomographyOracleCore.Revision.FiniteSetSparsification

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseCorrelationSparsification

open SparseCoefficientGeometry SparseSampleSuprema SparseCrossGeometry SparseDeterministicRecurrence
open SparseNetQuantileTransfer FiniteSetSparsification
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def maskedGram (X : ι → E) (I : Finset ι) (i j : ι) : ℝ :=
  if j ∈ I then ⟪X j, X i⟫_ℝ else 0

theorem maskedGram_sum (X : ι → E) (I : Finset ι) (y : ι → ℝ)
    (hy : Supported y I) (i : ι) :
    (∑ j, maskedGram X I i j * y j) = ⟪synthesis X y, X i⟫_ℝ := by
  rw [inner_synthesis_left]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : j ∈ I
  · simp [maskedGram, h, mul_comm]
  · simp [maskedGram, h, hy j h]

theorem maskedGram_restrict_sum (X : ι → E) (I : Finset ι) (y : ι → ℝ)
    (hy : Supported y I) (i : ι) (J : Finset ι) :
    (∑ j ∈ J, maskedGram X I i j * y j) = ⟪synthesis X (restrict J y), X i⟫_ℝ := by
  rw [← maskedGram_sum X I (restrict J y) (supported_restrict_of_supported hy J) i]
  simp [restrict, Finset.sum_filter]

/-- A finite-net count bounds the count for all k-sparse coefficients after
the elementary sparsifying selection. All constants remain explicit here. -/
theorem largeRows_card_lt_of_net {X : ι → E} {k m h r : ℕ} (I : Finset ι)
    (hk : 0 < k) (hkN : k ≤ Fintype.card ι) (hr : 0 < r)
    (hrm : r ≤ m) (hhm : h ≤ m)
    {delta eta tau a M : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (heta : 0 ≤ eta) (ha : 0 < a)
    (hdh : delta * (k : ℝ) ≤ h) (hmr : 2 * (r : ℝ) ≤ (m : ℝ) / 2048)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M)
    (hsmall : M ≤ delta * Real.sqrt (delta * k) * a / 16384)
    (net : Finset (ι → ℝ))
    (hnet : ∀ v ∈ net, Admissible h I v)
    (hcover : ∀ y, Admissible h I y → ∃ v ∈ net,
      coefficientNorm (fun i => y i - v i) ≤ eta ∧
      (support (fun i => y i - v i)).card ≤ h)
    (hgood : ∀ v ∈ net, (largeRows X v Iᶜ tau).card < r)
    (hseparation : tau + eta * crossNorm X m I / Real.sqrt (r : ℝ) < delta * a / 8192)
    (y : ι → ℝ) (hy : Admissible k I y) :
    (largeRows X y Iᶜ a).card < m := by
  by_contra hcount
  have hmc : m ≤ (largeRows X y Iᶜ a).card := Nat.le_of_not_gt hcount
  obtain ⟨R, hRsub, hRc⟩ := Finset.exists_subset_card_eq hmc
  have hRI : R ⊆ Iᶜ := hRsub.trans (Finset.filter_subset _ _)
  have hm : 0 < m := hr.trans_le hrm
  have hfull : ∀ i ∈ R, a ≤ |∑ j, maskedGram X I i j * y j| := by
    intro i hi
    rw [maskedGram_sum X I y hy.2.2]
    exact (Finset.mem_filter.mp (hRsub hi)).2.le
  have hentries : ∀ i ∈ R, ∀ j,
      |maskedGram X I i j| ≤ delta * Real.sqrt (delta * k) * a / 16384 := by
    intro i hi j
    by_cases hj : j ∈ I
    · have hji : j ≠ i := by
        intro heq
        subst j
        exact (Finset.mem_compl.mp (hRI hi)) hj
      simpa [maskedGram, hj] using (hentry j i hji).trans hsmall
    · simp [maskedGram, hj]
      positivity
  obtain ⟨J, hJ, hrows⟩ := exists_sparse_restriction hk hkN R (by simpa [hRc] using hm)
    hdelta hdelta1 ha (maskedGram X I) y hy.1 hy.2.1 hfull hentries
  have hJh : J.card ≤ h := by exact_mod_cast hJ.trans hdh
  let y' := restrict J y
  have hy' : Admissible h I y' := hy.restrict_card J hJh
  let R' := R.filter fun i => delta * a / 8192 ≤ |⟪synthesis X y', X i⟫_ℝ|
  have hR' : 2 * r ≤ R'.card := by
    simp_rw [maskedGram_restrict_sum X I y hy.2.2] at hrows
    change (R.card : ℝ) / 2048 ≤ (R'.card : ℝ) at hrows
    rw [hRc] at hrows
    exact_mod_cast hmr.trans hrows
  have hbound := large_rows_le_net_threshold I hr hrm hhm heta net hnet hcover hgood
    y' hy' R' ((Finset.filter_subset _ _).trans hRI) hR'
    (fun i hi => (Finset.mem_filter.mp hi).2)
  exact (not_lt_of_ge hbound) hseparation

end
end TomographyOracleCore.Revision.SparseCorrelationSparsification
