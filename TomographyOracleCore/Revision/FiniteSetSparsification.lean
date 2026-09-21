import TomographyOracleCore.Revision.SparsifyingFiniteTypes
import TomographyOracleCore.Revision.SparseCoefficientGeometry

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.FiniteSetSparsification

open SparseCoefficientGeometry
open scoped BigOperators
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_subtype_eq_sum_of_zero_outside (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∉ S, f i = 0) : (∑ i : S, f i) = ∑ i, f i := by
  rw [Finset.sum_coe_sort]
  exact Finset.sum_subset (Finset.subset_univ S) (fun i _ hi => hf i hi)

theorem card_subtype_filter (S : Finset ι) (P : ι → Prop) [DecidablePred P] :
    (Finset.univ.filter fun i : S => P i).card = (S.filter P).card := by
  rw [Finset.univ_eq_attach, Finset.filter_attach, Finset.card_map, Finset.card_attach]

/-- Sparsification on a finite set of rows, with the coefficient vector padded
to exactly k coordinates. Padding is by actual zero coordinates. -/
theorem exists_sparse_restriction {k : ℕ} (hk : 0 < k) (hkN : k ≤ Fintype.card ι)
    (R : Finset ι) (hR : 0 < R.card)
    {delta a : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (ha : 0 < a)
    (T : ι → ι → ℝ) (y : ι → ℝ)
    (hy : coefficientNorm y ≤ 1) (hys : (support y).card ≤ k)
    (hfull : ∀ i ∈ R, a ≤ |∑ j, T i j * y j|)
    (hentry : ∀ i ∈ R, ∀ j,
      |T i j| ≤ delta * Real.sqrt (delta * k) * a / 16384) :
    ∃ J : Finset ι, (J.card : ℝ) ≤ delta * k ∧
      (R.card : ℝ) / 2048 ≤
        ((R.filter fun i => delta * a / 8192 ≤ |∑ j ∈ J, T i j * y j|).card : ℝ) := by
  classical
  obtain ⟨S, hysS, _, hSc⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_univ (support y)) hys (by simpa using hkN)
  have hyS : Supported y S := (support_subset_iff _ _).mp hysS
  have hsum (f : ι → ℝ) : (∑ j : S, f j * y j) = ∑ j, f j * y j :=
    sum_subtype_eq_sum_of_zero_outside S (fun j => f j * y j) (fun j hj => by simp [hyS j hj])
  have hy2 : (∑ j : S, y j ^ 2) ≤ 1 := by
    rw [sum_subtype_eq_sum_of_zero_outside S (fun j => y j ^ 2) (fun j hj => by simp [hyS j hj]),
      ← coefficientNorm_sq]
    nlinarith [coefficientNorm_nonneg y]
  obtain ⟨J, hJ, hr⟩ := SparsifyingFiniteTypes.exists_sparse_coordinates
    (κ := S) (ν := R) (by simpa [hSc] using hk) (by simpa using hR)
    hdelta hdelta1 ha (fun i j => T i j) (fun j => y j) hy2
    (fun i => by rw [hsum]; exact hfull i i.property)
    (fun i j => by simpa [hSc] using hentry i i.property j)
  let J' := J.map (Function.Embedding.subtype (fun i => i ∈ S))
  refine ⟨J', by simpa [J', hSc] using hJ, ?_⟩
  have heq (i : ι) : (∑ j ∈ J', T i j * y j) = ∑ j ∈ J, T i j * y j := by
    simp [J', Finset.sum_map]
  simp only [Fintype.card_coe] at hr
  simp_rw [heq]
  rw [← card_subtype_filter R (fun i => delta * a / 8192 ≤ |∑ j ∈ J, T i j * y j|)]
  exact hr

end
end TomographyOracleCore.Revision.FiniteSetSparsification
