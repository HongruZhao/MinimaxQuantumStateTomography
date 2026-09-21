import TomographyOracleCore.Revision.ElementarySparsifying

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.SparsifyingFiniteTypes

open scoped BigOperators
noncomputable section

theorem exists_sparse_coordinates {κ ν : Type*} [Fintype κ] [Fintype ν]
    (hk : 0 < Fintype.card κ) (hm : 0 < Fintype.card ν)
    {delta a : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1) (ha : 0 < a)
    (T : ν → κ → ℝ) (y : κ → ℝ)
    (hy : (∑ j, y j ^ 2) ≤ 1)
    (hfull : ∀ i, a ≤ |∑ j, T i j * y j|)
    (hentry : ∀ i j, |T i j| ≤ delta * Real.sqrt (delta * Fintype.card κ) * a / 16384) :
    ∃ J : Finset κ, (J.card : ℝ) ≤ delta * Fintype.card κ ∧
      (Fintype.card ν : ℝ) / 2048 ≤
        ((Finset.univ.filter fun i => delta * a / 8192 ≤ |∑ j ∈ J, T i j * y j|).card : ℝ) := by
  classical
  let e : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let f : Fin (Fintype.card ν) ≃ ν := (Fintype.equivFin ν).symm
  have hy' : (∑ j, y (e j) ^ 2) ≤ 1 := by rw [e.sum_comp (fun j => y j ^ 2)]; exact hy
  have hfull' : ∀ i, a ≤ |∑ j, T (f i) (e j) * y (e j)| := by
    intro i
    rw [e.sum_comp (fun j => T (f i) j * y j)]
    exact hfull (f i)
  obtain ⟨J, hc, hr⟩ := ElementarySparsifying.exists_sparse_coordinates hk hm hdelta hdelta1 ha
    (fun i j => T (f i) (e j)) (fun j => y (e j)) hy' hfull'
    (fun i j => hentry (f i) (e j))
  refine ⟨J.map e.toEmbedding, by simpa using hc, ?_⟩
  have heq : ((Finset.univ.filter fun i : ν =>
      delta * a / 8192 ≤ |∑ j ∈ J.map e.toEmbedding, T i j * y j|).card : ℝ) =
    ((Finset.univ.filter fun i : Fin (Fintype.card ν) =>
      delta * a / 8192 ≤ |∑ j ∈ J, T (f i) (e j) * y (e j)|).card : ℝ) := by
    simp only [Finset.sum_map, Equiv.toEmbedding_apply]
    congr 1
    have h := congrArg Finset.card (Finset.filter_map (f := f.toEmbedding)
      (s := Finset.univ) (p := fun i : ν =>
        delta * a / 8192 ≤ |∑ j ∈ J, T i (e j) * y (e j)|))
    simpa only [Finset.card_map, Finset.map_univ_equiv, Function.comp_apply,
      Equiv.toEmbedding_apply] using h
  rw [heq]
  exact hr

end
end TomographyOracleCore.Revision.SparsifyingFiniteTypes
