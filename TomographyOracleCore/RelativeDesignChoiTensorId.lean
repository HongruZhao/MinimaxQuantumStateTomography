import TomographyOracleCore.RelativeDesignThreeMomentLocalEPRRepresentation

namespace TomographyOracleCore

universe u v w

open scoped CStarAlgebra BigOperators

noncomputable section

local instance choiTensorIdSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choiTensorIdStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# A common untouched identity factor in finite Choi coordinates

The extra register left untouched by every map contributes one raw EPR
projector to the Choi matrix.  This file packages that operation without
assuming any tensor-product API beyond the explicit finite matrices.
-/

/-- The raw EPR projector is the dimension multiple of its normalized
star-projection. -/
theorem finiteEPRProjector_eq_card_smul_normalized
    {T : Type u} [Fintype T] [Nonempty T] [DecidableEq T] :
    finiteEPRProjector (I := T) =
      (Fintype.card T : ℝ) • finiteNormalizedEPRProjector (T := T) := by
  apply CStarMatrix.ext
  intro ia jb
  unfold finiteNormalizedEPRProjector
  simp only [CStarMatrix.smul_apply, Complex.real_smul, smul_eq_mul]
  have hcard : (Fintype.card T : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp

theorem finiteEPRProjector_nonneg
    {T : Type u} [Fintype T] [Nonempty T] [DecidableEq T] :
    0 ≤ finiteEPRProjector (I := T) := by
  rw [finiteEPRProjector_eq_card_smul_normalized]
  exact smul_nonneg (by positivity)
    (finiteNormalizedEPRProjector_nonneg (T := T))

/-- Positivity of the transported Kronecker product, proved directly from
the C-star factorization of both positive factors. -/
theorem finiteChoiKroneckerReindex_nonneg
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    {G : CStarMatrix (S × S) (S × S) ℂ}
    {E : CStarMatrix (T × T) (T × T) ℂ}
    (hG : 0 ≤ G) (hE : 0 ≤ E) :
    0 ≤ finiteChoiKroneckerReindex e G E := by
  have hzeroLeft (E' : CStarMatrix (T × T) (T × T) ℂ) :
      finiteChoiKroneckerReindex e
          (0 : CStarMatrix (S × S) (S × S) ℂ) E' = 0 := by
    apply CStarMatrix.ext
    intro ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    simp [finiteChoiKroneckerReindex_apply]
  have hzeroRight (G' : CStarMatrix (S × S) (S × S) ℂ) :
      finiteChoiKroneckerReindex e G'
          (0 : CStarMatrix (T × T) (T × T) ℂ) = 0 := by
    apply CStarMatrix.ext
    intro ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    simp [finiteChoiKroneckerReindex_apply]
  have haddLeft
      (G₁ G₂ : CStarMatrix (S × S) (S × S) ℂ)
      (E' : CStarMatrix (T × T) (T × T) ℂ) :
      finiteChoiKroneckerReindex e (G₁ + G₂) E' =
        finiteChoiKroneckerReindex e G₁ E' +
          finiteChoiKroneckerReindex e G₂ E' := by
    apply CStarMatrix.ext
    intro ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    simp [finiteChoiKroneckerReindex_apply, add_mul]
  have haddRight
      (G' : CStarMatrix (S × S) (S × S) ℂ)
      (E₁ E₂ : CStarMatrix (T × T) (T × T) ℂ) :
      finiteChoiKroneckerReindex e G' (E₁ + E₂) =
        finiteChoiKroneckerReindex e G' E₁ +
          finiteChoiKroneckerReindex e G' E₂ := by
    apply CStarMatrix.ext
    intro ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    simp [finiteChoiKroneckerReindex_apply, mul_add]
  have hGmem := StarOrderedRing.nonneg_iff.mp hG
  have hEmem := StarOrderedRing.nonneg_iff.mp hE
  clear hG hE
  rw [StarOrderedRing.nonneg_iff]
  refine AddSubmonoid.closure_induction (fun G hG ↦ ?_) ?_
      (fun G G' hG hG' ih ih' ↦ ?_) hGmem
  · change ∃ X : CStarMatrix (S × S) (S × S) ℂ,
      star X * X = G at hG
    obtain ⟨X, rfl⟩ := hG
    refine AddSubmonoid.closure_induction (fun E hE ↦ ?_) ?_
        (fun E E' hE hE' ih ih' ↦ ?_) hEmem
    · change ∃ Y : CStarMatrix (T × T) (T × T) ℂ,
        star Y * Y = E at hE
      obtain ⟨Y, rfl⟩ := hE
      rw [← finiteChoiKroneckerReindex_mul,
        ← finiteChoiKroneckerReindex_star]
      exact AddSubmonoid.subset_closure (Set.mem_range_self _)
    · rw [hzeroRight]
      exact AddSubmonoid.zero_mem _
    · rw [haddRight]
      exact AddSubmonoid.add_mem _ ih ih'
  · rw [hzeroLeft]
    exact AddSubmonoid.zero_mem _
  · rw [haddLeft]
    exact AddSubmonoid.add_mem _ ih ih'

/-- The transported Choi Kronecker construction is linear in its acted-on
matrix factor. -/
theorem finiteChoiKroneckerReindex_smul_left
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T) (c : ℂ)
    (G : CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
    finiteChoiKroneckerReindex e (c • G) E =
      c • finiteChoiKroneckerReindex e G E := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [finiteChoiKroneckerReindex_apply, mul_assoc]

theorem finiteChoiKroneckerReindex_zero_left
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
    finiteChoiKroneckerReindex e
        (0 : CStarMatrix (S × S) (S × S) ℂ) E = 0 := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [finiteChoiKroneckerReindex_apply]

theorem finiteChoiKroneckerReindex_zero_right
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : CStarMatrix (S × S) (S × S) ℂ) :
    finiteChoiKroneckerReindex e G
        (0 : CStarMatrix (T × T) (T × T) ℂ) = 0 := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [finiteChoiKroneckerReindex_apply]

theorem finiteChoiKroneckerReindex_add_left
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G G' : CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
    finiteChoiKroneckerReindex e (G + G') E =
      finiteChoiKroneckerReindex e G E +
        finiteChoiKroneckerReindex e G' E := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [finiteChoiKroneckerReindex_apply, add_mul]

theorem finiteChoiKroneckerReindex_add_right
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G : CStarMatrix (S × S) (S × S) ℂ)
    (E E' : CStarMatrix (T × T) (T × T) ℂ) :
    finiteChoiKroneckerReindex e G (E + E') =
      finiteChoiKroneckerReindex e G E +
        finiteChoiKroneckerReindex e G E' := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [finiteChoiKroneckerReindex_apply, mul_add]

/-- CP map reconstructed after adjoining a common untouched Choi EPR
factor and transporting through a physical-basis equivalence. -/
def finiteChoiTensorIdCP
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (C : CStarMatrix (S × S) (S × S) ℂ) (hC : 0 ≤ C) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  finiteCPMapOfNonnegativeChoi
    (finiteChoiKroneckerReindex e C (finiteEPRProjector (I := T)))
    (finiteChoiKroneckerReindex_nonneg e hC finiteEPRProjector_nonneg)

@[simp] theorem finiteChoiTensorIdCP_choi
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (C : CStarMatrix (S × S) (S × S) ℂ) (hC : 0 ≤ C) :
    finiteChoiMatrix (finiteChoiTensorIdCP e C hC).toLinearMap =
      finiteChoiKroneckerReindex e C (finiteEPRProjector (I := T)) := by
  apply finiteChoiMatrix_finiteCPMapOfNonnegativeChoi

/-- The two raw EPR delta factors in a composed untouched register contract
to the single raw EPR factor.  This is the finite-coordinate content of
`id ∘ id = id`. -/
theorem finite_sum_four_inactive_delta
    {S : Type v} {T : Type w}
    [Fintype S] [Fintype T] [DecidableEq T]
    (ti ta tj tb : T) (g : S → S → ℂ) :
    (∑ x : S, ∑ x₁ : T, ∑ y : S, ∑ y₁ : T,
      if x₁ = ta ∧ y₁ = tb then
        if ti = x₁ ∧ tj = y₁ then g x y else 0
      else 0) =
      if ti = ta ∧ tj = tb then
        ∑ x : S, ∑ y : S, g x y
      else 0 := by
  have hinner (x y : S) :
      (∑ x₁ : T, ∑ y₁ : T,
        if x₁ = ta ∧ y₁ = tb then
          if ti = x₁ ∧ tj = y₁ then g x y else 0
        else 0) =
        if ti = ta ∧ tj = tb then g x y else 0 := by
    by_cases hi : ti = ta
    · subst ti
      by_cases hj : tj = tb
      · subst tj
        simp [ite_and]
      · simp [ite_and, hj]
    · simp [ite_and, hi]
  calc
    (∑ x : S, ∑ x₁ : T, ∑ y : S, ∑ y₁ : T,
      if x₁ = ta ∧ y₁ = tb then
        if ti = x₁ ∧ tj = y₁ then g x y else 0
      else 0) =
        ∑ x : S, ∑ y : S, ∑ x₁ : T, ∑ y₁ : T,
          if x₁ = ta ∧ y₁ = tb then
            if ti = x₁ ∧ tj = y₁ then g x y else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ x : S, ∑ y : S,
        if ti = ta ∧ tj = tb then g x y else 0 := by
      simp_rw [hinner]
    _ = if ti = ta ∧ tj = tb then
          ∑ x : S, ∑ y : S, g x y
        else 0 := by
      by_cases h : ti = ta ∧ tj = tb <;> simp [h]

/-- Adjoining the same untouched identity factor respects composition. -/
theorem finiteChoiMatrix_comp_finiteChoiTensorIdCP
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (C D : CStarMatrix (S × S) (S × S) ℂ)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    finiteChoiMatrix
        (CompletelyPositiveMap.comp
          (finiteChoiTensorIdCP e C hC)
          (finiteChoiTensorIdCP e D hD)).toLinearMap =
      finiteChoiKroneckerReindex e
        (finiteChoiMatrix
          (CompletelyPositiveMap.comp
            (finiteCPMapOfNonnegativeChoi C hC)
            (finiteCPMapOfNonnegativeChoi D hD)).toLinearMap)
        (finiteEPRProjector (I := T)) := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  unfold finiteChoiTensorIdCP
  rw [finiteChoiMatrix_comp_finiteCPMapOfNonnegativeChoi_apply,
    finiteChoiKroneckerReindex_apply,
    finiteChoiMatrix_comp_finiteCPMapOfNonnegativeChoi_apply]
  simp only [finiteChoiKroneckerReindex_apply, finiteEPRProjector]
  let f : I → I → ℂ := fun x y ↦
    (D ((e i).1, (e x).1) ((e j).1, (e y).1) *
        (if (e i).2 = (e x).2 ∧ (e j).2 = (e y).2 then 1 else 0)) *
      (C ((e x).1, (e a).1) ((e y).1, (e b).1) *
        (if (e x).2 = (e a).2 ∧ (e y).2 = (e b).2 then 1 else 0))
  have hsum : (∑ x : I, ∑ y : I, f x y) =
      ∑ x : S × T, ∑ y : S × T, f (e.symm x) (e.symm y) := by
    apply Fintype.sum_equiv e
    intro x
    apply Fintype.sum_equiv e
    intro y
    simp
  change (∑ x : I, ∑ y : I, f x y) = _
  rw [hsum]
  simp_rw [Fintype.sum_prod_type]
  simpa [f, Finset.mul_sum, Finset.sum_mul] using
    (finite_sum_four_inactive_delta
      (e i).2 (e a).2 (e j).2 (e b).2
      (fun x y ↦
        D ((e i).1, x) ((e j).1, y) *
          C (x, (e a).1) (y, (e b).1)))

end

end TomographyOracleCore
