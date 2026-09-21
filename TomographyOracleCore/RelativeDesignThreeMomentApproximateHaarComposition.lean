import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaar

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

/-!
# Exact composition of the concrete order-three approximate-Haar references

The Choi convention here is `(input, output)`.  It swaps the two displayed
tensor factors of Eq. (B.26), without changing their operator norm or their
two-index representation laws.
-/

/-- The B.26 register permutation in finite-Choi `(input,output)` order. -/
def finiteThreeMomentB26ChoiRegisterPermutation
    (A B C : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    Equiv.Perm (ThreeReplicaABC A B C × ThreeReplicaABC A B C) :=
  ((threeReplicaSlotPermutation A tau).prodCongr
      ((threeReplicaSlotPermutation B sigma).prodCongr
        (threeReplicaSlotPermutation C sigma))).prodCongr
    ((threeReplicaSlotPermutation A tau).prodCongr
      ((threeReplicaSlotPermutation B tau).prodCongr
        (threeReplicaSlotPermutation C sigma)))

/-- The literal B.26 permutation tensor in finite-Choi order. -/
def finiteThreeMomentB26ChoiQ
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ := by
  classical
  exact CStarMatrix.ofMatrix <|
    Matrix.permMatrixHom (R := ℂ)
      (finiteThreeMomentB26ChoiRegisterPermutation A B C sigma tau)

@[simp] theorem finiteThreeMomentB26ChoiQ_apply
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    finiteThreeMomentB26ChoiQ A B C sigma tau (i, a) (j, b) =
      if j = ((threeReplicaSlotPermutation A tau)⁻¹ i.1,
          (threeReplicaSlotPermutation B sigma)⁻¹ i.2.1,
          (threeReplicaSlotPermutation C sigma)⁻¹ i.2.2) ∧
        b = ((threeReplicaSlotPermutation A tau)⁻¹ a.1,
          (threeReplicaSlotPermutation B tau)⁻¹ a.2.1,
          (threeReplicaSlotPermutation C sigma)⁻¹ a.2.2)
      then 1 else 0 := by
  classical
  change ((finiteThreeMomentB26ChoiRegisterPermutation A B C sigma tau)⁻¹.permMatrix ℂ)
    (i, a) (j, b) = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
    finiteThreeMomentB26ChoiRegisterPermutation, Prod.map, eq_comm]

/-- The equality of the two inverse overlap actions is precisely a fixed
point condition for `sigma * tau⁻¹`. -/
theorem threeReplicaOverlap_condition_iff_fixed
    (B : Type*) (sigma tau : Equiv.Perm (Fin 3)) (x : ThreeReplica B) :
    (threeReplicaSlotPermutation B tau).symm x =
        (threeReplicaSlotPermutation B sigma).symm x ↔
      threeReplicaSlotPermutation B (sigma * tau⁻¹) x = x := by
  constructor
  · intro h
    have h' := ((threeReplicaSlotPermutation B sigma).symm_apply_eq).mp h.symm
    symm at h'
    change (threeReplicaSlotPermutation B sigma)
      ((threeReplicaSlotPermutation B tau)⁻¹ x) = x at h'
    rw [← threeReplicaSlotPermutation_inv] at h'
    change (threeReplicaSlotPermutation B sigma *
      threeReplicaSlotPermutation B tau⁻¹) x = x at h'
    rw [← threeReplicaSlotPermutation_mul] at h'
    exact h'
  · intro h
    symm
    apply ((threeReplicaSlotPermutation B sigma).symm_apply_eq).2
    symm
    change (threeReplicaSlotPermutation B sigma)
      ((threeReplicaSlotPermutation B tau)⁻¹ x) = x
    rw [← threeReplicaSlotPermutation_inv]
    change (threeReplicaSlotPermutation B sigma *
      threeReplicaSlotPermutation B tau⁻¹) x = x
    rw [← threeReplicaSlotPermutation_mul]
    exact h

@[simp] theorem card_filter_threeReplicaSlotPermutation_fixed
    (B : Type*) [Fintype B] [DecidableEq B]
    (pi : Equiv.Perm (Fin 3)) :
    (((Finset.univ.filter fun x : ThreeReplica B ↦
      threeReplicaSlotPermutation B pi x = x).card : ℕ) : ℂ) =
      (Fintype.card B : ℂ) ^ finThreeFullCycleCount pi := by
  rw [← Finset.sum_boole]
  simpa using sum_threeReplicaSlotPermutation_fixed_indicator B pi

set_option maxHeartbeats 1200000 in
/-- The internal Choi contraction of one `BC` term and one `AB` term.
Every internal register collapses uniquely except `B`; its remaining fixed
points produce the permutation Gram coefficient. -/
theorem finiteThreeMoment_localChoiTerms_contract
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    (∑ x : ThreeReplicaABC A B C, ∑ y : ThreeReplicaABC A B C,
      (finiteThreeMomentPairQ (threeReplicaABSlotPermutation B C) sigma sigma
          ((i.2.1, i.2.2), (x.2.1, x.2.2))
          ((j.2.1, j.2.2), (y.2.1, y.2.2)) *
        (if i.1 = x.1 ∧ j.1 = y.1 then 1 else 0)) *
      (finiteThreeMomentPairQ (threeReplicaABSlotPermutation A B) tau tau
          ((x.1, x.2.1), (a.1, a.2.1))
          ((y.1, y.2.1), (b.1, b.2.1)) *
        (if x.2.2 = a.2.2 ∧ y.2.2 = b.2.2 then 1 else 0))) =
      (Fintype.card B : ℂ) ^
          finThreeFullCycleCount (sigma * tau⁻¹) *
        finiteThreeMomentB26ChoiQ A B C sigma tau (i, a) (j, b) := by
  classical
  simp_rw [Fintype.sum_prod_type]
  simp only [finiteThreeMomentPairQ_apply,
    finiteThreeMomentPairPermutation, threeReplicaABSlotPermutation]
  rw [finiteThreeMomentB26ChoiQ_apply]
  by_cases hja : j.1 = (threeReplicaSlotPermutation A tau).symm i.1 <;>
    by_cases hjb : j.2.1 = (threeReplicaSlotPermutation B sigma).symm i.2.1 <;>
    by_cases hjc : j.2.2 = (threeReplicaSlotPermutation C sigma).symm i.2.2 <;>
    by_cases hba : b.1 = (threeReplicaSlotPermutation A tau).symm a.1 <;>
    by_cases hbb : b.2.1 = (threeReplicaSlotPermutation B tau).symm a.2.1 <;>
    by_cases hbc : b.2.2 = (threeReplicaSlotPermutation C sigma).symm a.2.2
  all_goals
    simp [hja, hjb, hjc, hba, hbb, hbc, Prod.ext_iff, ite_and,
      threeReplicaOverlap_condition_iff_fixed,
      card_filter_threeReplicaSlotPermutation_fixed]

/-- Raw unnormalized-Choi form of Eq. (B.26). -/
def finiteThreeMomentComposedReferenceRawChoi
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  ∑ sigma : Equiv.Perm (Fin 3), ∑ tau : Equiv.Perm (Fin 3),
    ((((((Fintype.card A * Fintype.card B : ℕ) : ℝ) ^ 3)⁻¹ *
        ((((Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ)) : ℂ) *
      (Fintype.card B : ℂ) ^
        finThreeFullCycleCount (sigma * tau⁻¹)) •
      finiteThreeMomentB26ChoiQ A B C sigma tau

theorem fintype_sum_four_rotate
    {X Y T S : Type*} [Fintype X] [Fintype Y] [Fintype T] [Fintype S]
    (f : S → T → X → Y → ℂ) :
    (∑ x : X, ∑ y : Y, ∑ t : T, ∑ s : S, f s t x y) =
      ∑ s : S, ∑ t : T, ∑ x : X, ∑ y : Y, f s t x y := by
  calc
    (∑ x : X, ∑ y : Y, ∑ t : T, ∑ s : S, f s t x y) =
        ∑ x : X, ∑ y : Y, ∑ s : S, ∑ t : T, f s t x y := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact Finset.sum_comm
    _ = ∑ x : X, ∑ s : S, ∑ y : Y, ∑ t : T, f s t x y := by
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ s : S, ∑ x : X, ∑ y : Y, ∑ t : T, f s t x y :=
      Finset.sum_comm
    _ = ∑ s : S, ∑ x : X, ∑ t : T, ∑ y : Y, f s t x y := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro x hx
      exact Finset.sum_comm
    _ = ∑ s : S, ∑ t : T, ∑ x : X, ∑ y : Y, f s t x y := by
      apply Finset.sum_congr rfl
      intro s hs
      exact Finset.sum_comm

set_option maxHeartbeats 1600000 in
/-- Exact B.26 identity for the composition of the two concrete local
approximate-Haar references, in the repository's raw Choi convention. -/
theorem finiteChoiMatrix_finiteThreeMomentReferenceComposition
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteChoiMatrix
      (CompletelyPositiveMap.comp
        (finiteThreeMomentABReferenceCP A B C)
        (finiteThreeMomentBCReferenceCP A B C)).toLinearMap =
      finiteThreeMomentComposedReferenceRawChoi A B C := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  unfold finiteThreeMomentABReferenceCP finiteThreeMomentBCReferenceCP
  rw [finiteChoiMatrix_comp_finiteCPMapOfNonnegativeChoi_apply]
  unfold finiteThreeMomentComposedReferenceRawChoi
  change (∑ x : ThreeReplicaABC A B C, ∑ y : ThreeReplicaABC A B C,
      finiteThreeMomentBCReferenceChoi A B C (i, x) (j, y) *
        finiteThreeMomentABReferenceChoi A B C (x, a) (y, b)) =
    ∑ sigma : Equiv.Perm (Fin 3), ∑ tau : Equiv.Perm (Fin 3),
      ((((((Fintype.card A * Fintype.card B : ℕ) : ℝ) ^ 3)⁻¹ *
          ((((Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ)) : ℂ) *
        (Fintype.card B : ℂ) ^
          finThreeFullCycleCount (sigma * tau⁻¹)) *
        finiteThreeMomentB26ChoiQ A B C sigma tau (i, a) (j, b)
  simp_rw [finiteThreeMomentABReferenceChoi_apply,
    finiteThreeMomentBCReferenceChoi_apply]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [fintype_sum_four_rotate]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  apply Finset.sum_congr rfl
  intro tau htau
  let cAB : ℂ :=
    (((((Fintype.card A * Fintype.card B : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) : ℂ)
  let cBC : ℂ :=
    (((((Fintype.card B * Fintype.card C : ℕ) : ℝ) ^ 3)⁻¹ : ℝ) : ℂ)
  let F : ThreeReplicaABC A B C → ThreeReplicaABC A B C → ℂ :=
    fun x y ↦
      finiteThreeMomentPairQ
          (threeReplicaABSlotPermutation B C) sigma sigma
            ((i.2.1, i.2.2), (x.2.1, x.2.2))
            ((j.2.1, j.2.2), (y.2.1, y.2.2))
  let eBC : ThreeReplicaABC A B C → ThreeReplicaABC A B C → ℂ :=
    fun x y ↦ if i.1 = x.1 ∧ j.1 = y.1 then 1 else 0
  let G : ThreeReplicaABC A B C → ThreeReplicaABC A B C → ℂ :=
    fun x y ↦
      finiteThreeMomentPairQ
          (threeReplicaABSlotPermutation A B) tau tau
            ((x.1, x.2.1), (a.1, a.2.1))
            ((y.1, y.2.1), (b.1, b.2.1))
  let eAB : ThreeReplicaABC A B C → ThreeReplicaABC A B C → ℂ :=
    fun x y ↦ if x.2.2 = a.2.2 ∧ y.2.2 = b.2.2 then 1 else 0
  simp only [mul_assoc]
  have hscaled :
      (∑ x : ThreeReplicaABC A B C, ∑ y : ThreeReplicaABC A B C,
        cBC * (F x y * (eBC x y * (cAB * (G x y * eAB x y))))) =
      cAB * cBC *
        ∑ x : ThreeReplicaABC A B C, ∑ y : ThreeReplicaABC A B C,
          (F x y * eBC x y) * (G x y * eAB x y) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y hy
    ring
  calc
    _ = cAB * cBC *
        ∑ x : ThreeReplicaABC A B C, ∑ y : ThreeReplicaABC A B C,
          (F x y * eBC x y) * (G x y * eAB x y) := by
      dsimp only [cAB, cBC, F, eBC, G, eAB] at hscaled ⊢
      convert hscaled using 1 <;> push_cast <;> rfl
    _ = _ := by
      dsimp only [F, eBC, G, eAB]
      rw [finiteThreeMoment_localChoiTerms_contract]
      dsimp only [cAB, cBC]
      ring

end

end TomographyOracleCore
