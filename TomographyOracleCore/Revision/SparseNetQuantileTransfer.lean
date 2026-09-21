import TomographyOracleCore.Revision.SparseDeterministicRecurrence
import TomographyOracleCore.Revision.SparseCoefficientNets

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseNetQuantileTransfer

open SparseCoefficientGeometry SparseSampleSuprema SparseCrossGeometry SparseDeterministicRecurrence
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Passing a count of large correlations from a support-preserving net to
the entire sparse unit ball. The error uses the smaller restricted cross norm. -/
theorem large_rows_le_net_threshold {X : ι → E} {h m r : ℕ} (I : Finset ι)
    (hr : 0 < r) (hrm : r ≤ m) (hhm : h ≤ m)
    {eta tau a : ℝ} (heta : 0 ≤ eta)
    (net : Finset (ι → ℝ))
    (hnet : ∀ v ∈ net, Admissible h I v)
    (hcover : ∀ y, Admissible h I y → ∃ v ∈ net,
      coefficientNorm (fun i => y i - v i) ≤ eta ∧
      (support (fun i => y i - v i)).card ≤ h)
    (hgood : ∀ v ∈ net, (largeRows X v Iᶜ tau).card < r)
    (y : ι → ℝ) (hy : Admissible h I y)
    (R : Finset ι) (hRI : R ⊆ Iᶜ) (hR : 2 * r ≤ R.card)
    (hlarge : ∀ i ∈ R, a ≤ |⟪synthesis X y, X i⟫_ℝ|) :
    a ≤ tau + eta * crossNorm X m I / Real.sqrt (r : ℝ) := by
  have hg0 := crossNorm_nonneg X m I
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hsqrt : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  by_cases hat : a ≤ tau
  · exact hat.trans (by linarith [div_nonneg (mul_nonneg heta hg0) hsqrt.le])
  have hat' : 0 ≤ a - tau := by linarith
  obtain ⟨v, hv, hdist, hsupport⟩ := hcover y hy
  let bad := largeRows X v Iᶜ tau
  have hbad : bad.card < r := hgood v hv
  have hremain : r ≤ (R \ bad).card := by
    have hc : R.card ≤ (R \ bad).card + bad.card := Finset.card_le_card_sdiff_add_card
    omega
  obtain ⟨L, hLsub, hLc⟩ := Finset.exists_subset_card_eq hremain
  have hLI : L ⊆ Iᶜ := (hLsub.trans Finset.sdiff_subset).trans hRI
  let d := fun i => y i - v i
  have hdI : Supported d I := supported_sub hy.2.2 (hnet v hv).2.2
  have hu := restricted_correlations_norm_le (X := X) d (hsupport.trans hhm) hdI
    L (by rw [hLc]; exact hrm) hLI
  have hu' : coefficientNorm (restrict L (fun j => ⟪synthesis X d, X j⟫_ℝ)) ≤
      eta * crossNorm X m I :=
    hu.trans (mul_le_mul_of_nonneg_right hdist hg0)
  have hlower : (r : ℝ) * (a - tau) ^ 2 ≤
      coefficientNorm (restrict L (fun j => ⟪synthesis X d, X j⟫_ℝ)) ^ 2 := by
    rw [coefficientNorm_restrict_sq]
    calc
      _ = ∑ _j ∈ L, (a - tau) ^ 2 := by simp [hLc]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        have hjR := (Finset.mem_sdiff.mp (hLsub hj)).1
        have hjbad := (Finset.mem_sdiff.mp (hLsub hj)).2
        have hvsmall : |⟪synthesis X v, X j⟫_ℝ| ≤ tau := by
          apply le_of_not_gt
          intro h
          exact hjbad (Finset.mem_filter.mpr ⟨hRI hjR, h⟩)
        have hd : synthesis X d = synthesis X y - synthesis X v := synthesis_sub _ _ _
        rw [hd, inner_sub_left]
        have htri := abs_sub_abs_le_abs_sub ⟪synthesis X y, X j⟫_ℝ ⟪synthesis X v, X j⟫_ℝ
        have habs : a - tau ≤ |⟪synthesis X y, X j⟫_ℝ - ⟪synthesis X v, X j⟫_ℝ| := by
          linarith [hlarge j hjR]
        have hs := (sq_le_sq₀ hat' (abs_nonneg _)).mpr habs
        simpa only [sq_abs] using hs
  have hlow : Real.sqrt (r : ℝ) * (a - tau) ≤
      coefficientNorm (restrict L (fun j => ⟪synthesis X d, X j⟫_ℝ)) := by
    apply (sq_le_sq₀ (mul_nonneg hsqrt.le hat') (coefficientNorm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt hrR.le]
    exact hlower
  have hmul := hlow.trans hu'
  have hdiv : a - tau ≤ eta * crossNorm X m I / Real.sqrt (r : ℝ) :=
    (le_div_iff₀ hsqrt).mpr (by nlinarith)
  linarith

end
end TomographyOracleCore.Revision.SparseNetQuantileTransfer
