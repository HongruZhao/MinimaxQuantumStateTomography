import TomographyOracleCore.Revision.PauliOmegaBlocks
import TomographyOracleCore.BinaryCliffordPeriodicFinEnsemble

namespace TomographyOracleCore.Revision.FourthBoundaryReindex

open FourthVectorBoundary PauliOmegaBlocks FourthLocalEmbedding
open scoped BigOperators InnerProductSpace
noncomputable section

local instance (K : ℕ) : DecidableEq (PauliBinaryWord K) :=
  fun a b => Fintype.decidablePiFintype a b

variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

def vectorReindex (e : α ≃ β) : EuclideanSpace ℂ α ≃ₗᵢ[ℂ] EuclideanSpace ℂ β :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp]
theorem vectorReindex_apply (e : α ≃ β) (u : EuclideanSpace ℂ α) (x : β) :
    vectorReindex e u x = u (e.symm x) := rfl

theorem reindex_matrix_action (e : α ≃ β) (A : Matrix α α ℂ)
    (u : EuclideanSpace ℂ α) :
    (Matrix.reindexAlgEquiv ℂ ℂ e A).toEuclideanLin (vectorReindex e u) =
      vectorReindex e (A.toEuclideanLin u) := by
  ext x
  change (∑ y : β, A (e.symm x) (e.symm y) * u (e.symm y)) =
    ∑ y : α, A (e.symm x) y * u y
  exact Equiv.sum_comp e.symm (fun y : α => A (e.symm x) y * u y)

theorem inner_reindex (e : α ≃ β) (A : Matrix α α ℂ)
    (u : EuclideanSpace ℂ α) :
    ⟪vectorReindex e u,
      (Matrix.reindexAlgEquiv ℂ ℂ e A).toEuclideanLin (vectorReindex e u)⟫_ℂ =
      ⟪u, A.toEuclideanLin u⟫_ℂ := by
  rw [reindex_matrix_action]
  exact (vectorReindex e).inner_map_map u (A.toEuclideanLin u)

theorem vectorFourth_reindex (e : α ≃ β) (u : EuclideanSpace ℂ α) :
    vectorFourth (vectorReindex e u) =
      vectorReindex (fourthMapEquiv e) (vectorFourth u) := by
  ext x
  rfl

theorem fourth_inner_reindex (e : α ≃ β)
    (A : Matrix (FourthIndex α) (FourthIndex α) ℂ) (u : EuclideanSpace ℂ α) :
    ⟪vectorFourth (vectorReindex e u),
      (Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e) A).toEuclideanLin
        (vectorFourth (vectorReindex e u))⟫_ℂ =
      ⟪vectorFourth u, A.toEuclideanLin (vectorFourth u)⟫_ℂ := by
  rw [vectorFourth_reindex]
  exact inner_reindex _ _ _

theorem reindex_pullback (e : α ≃ β) (A : Matrix β β ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ e (A.submatrix e e) = A := by
  ext x y
  change A (e (e.symm x)) (e (e.symm y)) = A x y
  simp

set_option maxHeartbeats 1000000 in
/-- The concrete bound for an arbitrary set of exceptional blocks. -/
theorem selectedOmega_unitary_bound
    {J : Type*} [Fintype J] [DecidableEq J]
    (p : J → Prop) [DecidablePred p] (K : ℕ)
    (U : Matrix.unitaryGroup (FourthIndex (J → PauliBinaryWord K)) ℂ)
    (hcomm : selectedOmega p K * U.val = U.val * selectedOmega p K)
    (u : EuclideanSpace ℂ (J → PauliBinaryWord K)) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u, (selectedOmega p K * U.val).toEuclideanLin (vectorFourth u)⟫_ℂ‖ ≤ 1 := by
  letI : DecidableEq ({j // ¬p j} → PauliBinaryWord K) :=
    fun a b => Fintype.decidablePiFintype a b
  let e := selectedWordEquiv p K
  let R := Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e)
  let U' := reindexUnitary (fourthMapEquiv e) U
  let u' := vectorReindex e u
  have hMul (A B : Matrix (FourthIndex (J → PauliBinaryWord K))
      (FourthIndex (J → PauliBinaryWord K)) ℂ) : R (A * B) = R A * R B := by
    change (A * B).submatrix (fourthMapEquiv e).symm (fourthMapEquiv e).symm =
      A.submatrix (fourthMapEquiv e).symm (fourthMapEquiv e).symm *
        B.submatrix (fourthMapEquiv e).symm (fourthMapEquiv e).symm
    exact (Matrix.submatrix_mul_equiv A B _ (fourthMapEquiv e).symm _).symm
  have hU' : U'.val = R U.val := by
    unfold U' R reindexUnitary
    rfl
  have hu' : ‖u'‖ = 1 := by rw [(vectorReindex e).norm_map, hu]
  have hR : R (selectedOmega p K) =
      localPauliFourthOmega (β := {j // ¬p j} → PauliBinaryWord K)
        (Fintype.card {j // p j} * K) := by
    rw [selectedOmega_eq_local_union]
    change Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e)
      ((localPauliFourthOmega (β := {j // ¬p j} → PauliBinaryWord K)
        (Fintype.card {j // p j} * K)).submatrix (fourthMapEquiv e) (fourthMapEquiv e)) = _
    exact reindex_pullback (fourthMapEquiv e) _
  have hc : localPauliFourthOmega (β := {j // ¬p j} → PauliBinaryWord K)
      (Fintype.card {j // p j} * K) * U'.val = U'.val *
        localPauliFourthOmega (β := {j // ¬p j} → PauliBinaryWord K)
          (Fintype.card {j // p j} * K) := by
    have h := congrArg R hcomm
    rw [hU']
    simpa only [hMul, hR] using h
  have hb := localPauliFourthOmega_unitary_bound_of_commute
    (Fintype.card {j // p j} * K) U' hc u' hu'
  have he := fourth_inner_reindex e (selectedOmega p K * U.val) u
  change ⟪vectorFourth u', (R (selectedOmega p K * U.val)).toEuclideanLin
    (vectorFourth u')⟫_ℂ = _ at he
  rw [hMul, hR] at he
  rw [hU'] at hb
  exact (congrArg norm he).symm.trans_le hb

end
end TomographyOracleCore.Revision.FourthBoundaryReindex
