import TomographyOracleCore.Revision.SparseCrossGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.SparseDeterministicRecurrence

open SparseCoefficientGeometry SparseSampleSuprema SparseCrossGeometry
open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def largeRows (X : ι → E) (y : ι → ℝ) (I : Finset ι) (A : ℝ) : Finset ι :=
  I.filter fun j => A < |⟪synthesis X y, X j⟫_ℝ|

theorem largeRows_antitone_threshold (X : ι → E) (y : ι → ℝ) (I : Finset ι)
    {a b : ℝ} (hab : a ≤ b) : largeRows X y I b ⊆ largeRows X y I a := by
  intro i hi
  have h := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨h.1, hab.trans_lt h.2⟩

theorem tail_cut_bound (X : ι → E) (y z : ι → ℝ) (I : Finset ι)
    {A : ℝ} (hA : 0 ≤ A) (hzI : Supported z I) :
    |⟪synthesis X y, synthesis X z⟫_ℝ| ≤
      |⟪synthesis X y, synthesis X (restrict (largeRows X y I A) z)⟫_ℝ| +
        A * ∑ i, |z i| := by
  let J := largeRows X y I A
  have htail : |⟪synthesis X y, synthesis X (restrict Jᶜ z)⟫_ℝ| ≤ A * ∑ i, |z i| := by
    rw [inner_synthesis_right]
    calc
      _ ≤ ∑ i, |restrict Jᶜ z i * ⟪synthesis X y, X i⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, A * |z i| := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hiJ : i ∈ J
        · simp [restrict, hiJ, mul_nonneg hA (abs_nonneg _)]
        by_cases hiI : i ∈ I
        · have hsmall : |⟪synthesis X y, X i⟫_ℝ| ≤ A := by
            apply le_of_not_gt
            intro h
            exact hiJ (Finset.mem_filter.mpr ⟨hiI, h⟩)
          simp only [restrict, Finset.mem_compl, hiJ, not_false_eq_true, if_true, abs_mul]
          nlinarith [mul_le_mul_of_nonneg_left hsmall (abs_nonneg (z i))]
        · simp [restrict, hiJ, hzI i hiI]
      _ = _ := by rw [Finset.mul_sum]
  have heq := synthesis_restrict_add_compl X z J
  rw [← heq, inner_add_right]
  exact (abs_add_le _ _).trans (by linarith)

/-- The deterministic two-sided support reduction. The hypotheses bound only
the number of large correlations; no sorting or maximizing vector is assumed. -/
theorem crossNorm_recurrence {X : ι → E} {k m : ℕ} (I : Finset ι)
    {A : ℝ} (hA : 0 ≤ A)
    (hleft : ∀ y, Admissible k I y → (largeRows X y Iᶜ A).card ≤ m)
    (hright : ∀ z, Admissible k Iᶜ z → (largeRows X z I A).card ≤ m) :
    crossNorm X k I ≤ crossNorm X m I + 2 * Real.sqrt (k : ℝ) * A := by
  apply crossNorm_le
  intro y z hy hz
  let J := largeRows X y Iᶜ A
  let z' := restrict J z
  have hz'k : Admissible k Iᶜ z' := hz.restrict J
  have hz'm : Admissible m Iᶜ z' := hz.restrict_card J (hleft y hy)
  let L := largeRows X z' I A
  let y' := restrict L y
  have hy'm : Admissible m I y' := hy.restrict_card L (hright z' hz'k)
  have h1 := tail_cut_bound X y z Iᶜ hA hz.2.2
  have h2 := tail_cut_bound X z' y I hA hy.2.2
  have h3 := abs_inner_le_crossNorm (X := X) hy'm hz'm
  have h4 := mul_le_mul_of_nonneg_left (admissible_sum_abs_le hy) hA
  have h5 := mul_le_mul_of_nonneg_left (admissible_sum_abs_le hz) hA
  change |⟪synthesis X y, synthesis X z⟫_ℝ| ≤
    |⟪synthesis X y, synthesis X z'⟫_ℝ| + A * ∑ i, |z i| at h1
  change |⟪synthesis X z', synthesis X y⟫_ℝ| ≤
    |⟪synthesis X z', synthesis X y'⟫_ℝ| + A * ∑ i, |y i| at h2
  rw [← real_inner_comm (synthesis X z') (synthesis X y),
    ← real_inner_comm (synthesis X z') (synthesis X y')] at h2
  nlinarith

theorem disjoint_synthesis_inner_bound {X : ι → E} {I : Finset ι} (y z : ι → ℝ)
    (hy : Supported y I) (hz : Supported z Iᶜ) {M : ℝ} (hM : 0 ≤ M)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M) :
    |⟪synthesis X y, synthesis X z⟫_ℝ| ≤ M * (∑ i, |y i|) * (∑ j, |z j|) := by
  rw [inner_synthesis_left]
  calc
    _ ≤ ∑ i, |y i * ⟪X i, synthesis X z⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |y i| * (M * ∑ j, |z j|) := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases hy0 : y i = 0
      · simp [hy0]
      have hiI : i ∈ I := by by_contra h; exact hy0 (hy i h)
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [inner_synthesis_right]
      calc
        _ ≤ ∑ j, |z j * ⟪X i, X j⟫_ℝ| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, M * |z j| := by
          apply Finset.sum_le_sum
          intro j hj
          by_cases hz0 : z j = 0
          · simp [hz0]
          have hjI : j ∈ Iᶜ := by by_contra h; exact hz0 (hz j h)
          have hij : i ≠ j := by intro h; subst j; exact (Finset.mem_compl.mp hjI) hiI
          rw [abs_mul]
          nlinarith [mul_le_mul_of_nonneg_left (hentry i j hij) (abs_nonneg (z j))]
        _ = _ := by rw [Finset.mul_sum]
    _ = _ := by rw [← Finset.sum_mul]; ring

theorem crossNorm_le_card_mul_pair_bound {X : ι → E} (k : ℕ) (I : Finset ι)
    {M : ℝ} (hM : 0 ≤ M) (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M) :
    crossNorm X k I ≤ (k : ℝ) * M := by
  apply crossNorm_le
  intro y z hy hz
  have h := disjoint_synthesis_inner_bound y z hy.2.2 hz.2.2 hM hentry
  have hprod := mul_le_mul (admissible_sum_abs_le hy) (admissible_sum_abs_le hz)
    (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Real.sqrt_nonneg _)
  rw [← sq, Real.sq_sqrt (Nat.cast_nonneg k)] at hprod
  have hmul := mul_le_mul_of_nonneg_left hprod hM
  nlinarith

end
end TomographyOracleCore.Revision.SparseDeterministicRecurrence
