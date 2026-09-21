import TomographyOracleCore.RelativeDesignLocalHaarReferenceCP
import TomographyOracleCore.RelativeDesignThreeMomentGlobalHaarReference

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance globalHaarCPSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance globalHaarCPStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Concrete global Haar/reference CP comparison

The Choi representation of a genuine global Haar third twirl uses the same
replica permutation on `A`, `B`, and `C` within each Choi copy.  This is
different off the diagonal from the crossed representation used to calculate
the pairwise-reference composition in B.26.  Their diagonal terms coincide,
which is exactly what is needed because the approximate-Haar reference is the
diagonal permutation sum.
-/

/-- Simultaneous permutation of the three replica slots on every physical
factor of `A ⊗ B ⊗ C`. -/
def threeReplicaABCSlotPermutation
    (A B C : Type*) (sigma : Equiv.Perm (Fin 3)) :
    Equiv.Perm (ThreeReplicaABC A B C) :=
  (threeReplicaSlotPermutation A sigma).prodCongr
    ((threeReplicaSlotPermutation B sigma).prodCongr
      (threeReplicaSlotPermutation C sigma))

theorem threeReplicaABCSlotPermutation_mul
    (A B C : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    threeReplicaABCSlotPermutation A B C (sigma * tau) =
      threeReplicaABCSlotPermutation A B C sigma *
        threeReplicaABCSlotPermutation A B C tau := by
  ext x <;> rfl

theorem threeReplicaABCSlotPermutation_inv
    (A B C : Type*) (sigma : Equiv.Perm (Fin 3)) :
    threeReplicaABCSlotPermutation A B C sigma⁻¹ =
      (threeReplicaABCSlotPermutation A B C sigma)⁻¹ := by
  ext x <;> rfl

/-- The uniform two-copy permutation representation occurring in the Choi
matrix of the genuine global Haar third twirl. -/
def finiteThreeMomentGlobalHaarChoiQ
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
      (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ :=
  finiteThreeMomentPairQ
    (threeReplicaABCSlotPermutation A B C) sigma tau

theorem finiteThreeMomentGlobalHaarChoiQ_mul
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    finiteThreeMomentGlobalHaarChoiQ A B C sigma tau *
        finiteThreeMomentGlobalHaarChoiQ A B C sigma' tau' =
      finiteThreeMomentGlobalHaarChoiQ A B C
        (sigma * sigma') (tau * tau') := by
  exact finiteThreeMomentPairQ_mul
    (threeReplicaABCSlotPermutation A B C)
    (threeReplicaABCSlotPermutation_mul A B C)
    sigma tau sigma' tau'

theorem finiteThreeMomentGlobalHaarChoiQ_star
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (finiteThreeMomentGlobalHaarChoiQ A B C sigma tau) =
      finiteThreeMomentGlobalHaarChoiQ A B C sigma⁻¹ tau⁻¹ := by
  exact finiteThreeMomentPairQ_star
    (threeReplicaABCSlotPermutation A B C)
    (threeReplicaABCSlotPermutation_inv A B C) sigma tau

theorem finiteThreeMomentGlobalHaarChoiQ_norm_le_one
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖finiteThreeMomentGlobalHaarChoiQ A B C sigma tau‖ ≤ 1 := by
  classical
  have hone : finiteThreeMomentGlobalHaarChoiQ A B C 1 1 = 1 := by
    have hrhoOne : threeReplicaABCSlotPermutation A B C 1 = 1 := by
      ext x <;> rfl
    have hpairOne : finiteThreeMomentPairPermutation
        (threeReplicaABCSlotPermutation A B C) 1 1 = 1 := by
      unfold finiteThreeMomentPairPermutation
      rw [hrhoOne]
      rfl
    apply CStarMatrix.ext
    intro u v
    change finiteThreeMomentPairQ
      (threeReplicaABCSlotPermutation A B C) 1 1 u v = _
    rw [finiteThreeMomentPairQ_apply]
    rw [hpairOne]
    rw [CStarMatrix.one_apply]
    simp [eq_comm]
  have hunit : finiteThreeMomentGlobalHaarChoiQ A B C sigma tau ∈
      unitary (CStarMatrix
        (ThreeReplicaABC A B C × ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C × ThreeReplicaABC A B C) ℂ) := by
    constructor
    · rw [finiteThreeMomentGlobalHaarChoiQ_star,
        finiteThreeMomentGlobalHaarChoiQ_mul]
      simpa using hone
    · rw [finiteThreeMomentGlobalHaarChoiQ_star,
        finiteThreeMomentGlobalHaarChoiQ_mul]
      simpa using hone
  exact le_of_eq (CStarRing.norm_of_mem_unitary hunit)

/-- On diagonal permutation pairs the genuine global-Haar representation and
the crossed B.26 representation agree literally. -/
theorem finiteThreeMomentGlobalHaarChoiQ_diagonal_eq_B26
    (A B C : Type*) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (sigma : Equiv.Perm (Fin 3)) :
    finiteThreeMomentGlobalHaarChoiQ A B C sigma sigma =
      finiteThreeMomentB26ChoiQ A B C sigma sigma := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  change finiteThreeMomentPairQ
      (threeReplicaABCSlotPermutation A B C) sigma sigma
      (i, a) (j, b) = _
  rw [finiteThreeMomentPairQ_apply,
    finiteThreeMomentB26ChoiQ_apply]
  simp [finiteThreeMomentPairPermutation,
    threeReplicaABCSlotPermutation, Prod.ext_iff]

/-- The existing concrete global reference is also the diagonal frame map for
the genuine global-Haar representation. -/
theorem finiteThreeMomentGlobalReferenceRawChoi_eq_globalHaarApproximate
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteThreeMomentGlobalReferenceRawChoi A B C =
      finiteThreeMomentApproximateHaarRawChoi
        (Fintype.card A * Fintype.card B * Fintype.card C)
        (finiteThreeMomentGlobalHaarChoiQ A B C) := by
  unfold finiteThreeMomentGlobalReferenceRawChoi
    finiteThreeMomentApproximateHaarRawChoi
  congr 1
  apply Finset.sum_congr rfl
  intro sigma hsigma
  exact (finiteThreeMomentGlobalHaarChoiQ_diagonal_eq_B26
    A B C sigma).symm

/-- Replica-coordinate transport from a `K`-qubit global physical basis to
the subsystem-major `A,B,C` basis. -/
def pauliHaarABCReplicaEquiv
    (K : ℕ) (A B C : Type u)
    (idxABC : PauliBinaryWord K ≃ (A × B) × C) :
    TripleIndex (PauliBinaryWord K) ≃ ThreeReplicaABC A B C :=
  (tripleIndexCongr idxABC).trans (tripleIndexABCEquiv A B C)

/-- Exact global Haar third twirl, implemented by the finite Clifford exact
third design and transported to the common B.26 basis. -/
def finiteThreeMomentABCHaarCP
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idxABC : PauliBinaryWord K ≃ (A × B) × C) :
    CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ :=
  CompletelyPositiveMap.reindexEquiv
    (pauliHaarABCReplicaEquiv K A B C idxABC)
    (pauliHaarThirdTwirlCP K)

@[simp] theorem pauliHaarABCReplicaEquiv_A_apply
    (K : ℕ) (A B C : Type u)
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (x : TripleIndex (PauliBinaryWord K)) (q : Fin 3) :
    (pauliHaarABCReplicaEquiv K A B C idxABC x).1 q =
      (idxABC
        (tripleIndexEquivThreeReplica (PauliBinaryWord K) x q)).1.1 := by
  fin_cases q <;> rfl

@[simp] theorem pauliHaarABCReplicaEquiv_B_apply
    (K : ℕ) (A B C : Type u)
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (x : TripleIndex (PauliBinaryWord K)) (q : Fin 3) :
    (pauliHaarABCReplicaEquiv K A B C idxABC x).2.1 q =
      (idxABC
        (tripleIndexEquivThreeReplica (PauliBinaryWord K) x q)).1.2 := by
  fin_cases q <;> rfl

@[simp] theorem pauliHaarABCReplicaEquiv_C_apply
    (K : ℕ) (A B C : Type u)
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (x : TripleIndex (PauliBinaryWord K)) (q : Fin 3) :
    (pauliHaarABCReplicaEquiv K A B C idxABC x).2.2 q =
      (idxABC
        (tripleIndexEquivThreeReplica (PauliBinaryWord K) x q)).2 := by
  fin_cases q <;> rfl

theorem card_ABC_eq_two_pow_of_pauliEquiv
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    (idxABC : PauliBinaryWord K ≃ (A × B) × C) :
    Fintype.card A * Fintype.card B * Fintype.card C = 2 ^ K := by
  calc
    Fintype.card A * Fintype.card B * Fintype.card C =
        Fintype.card ((A × B) × C) := by simp
    _ = Fintype.card (PauliBinaryWord K) := (Fintype.card_congr idxABC).symm
    _ = 2 ^ K := by simp [PauliBinaryWord]

/-- The global replica basis change intertwines the literal tuple and
subsystem-major representations of slot permutations. -/
theorem pauliHaarABCReplicaEquiv_intertwine
    (K : ℕ) (A B C : Type u)
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (sigma : Equiv.Perm (Fin 3))
    (x : TripleIndex (PauliBinaryWord K)) :
    pauliHaarABCReplicaEquiv K A B C idxABC
        (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x) =
      threeReplicaABCSlotPermutation A B C sigma
        (pauliHaarABCReplicaEquiv K A B C idxABC x) := by
  apply Prod.ext
  · funext q
    change
      (pauliHaarABCReplicaEquiv K A B C idxABC
        (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x)).1 q =
      (pauliHaarABCReplicaEquiv K A B C idxABC x).1 (sigma⁻¹ q)
    rw [pauliHaarABCReplicaEquiv_A_apply,
      tripleIndexEquivThreeReplica_slotPermutation_apply]
    exact (pauliHaarABCReplicaEquiv_A_apply
      K A B C idxABC x (sigma⁻¹ q)).symm
  · apply Prod.ext
    · funext q
      change
        (pauliHaarABCReplicaEquiv K A B C idxABC
          (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x)).2.1 q =
        (pauliHaarABCReplicaEquiv K A B C idxABC x).2.1 (sigma⁻¹ q)
      rw [pauliHaarABCReplicaEquiv_B_apply,
        tripleIndexEquivThreeReplica_slotPermutation_apply]
      exact (pauliHaarABCReplicaEquiv_B_apply
        K A B C idxABC x (sigma⁻¹ q)).symm
    · funext q
      change
        (pauliHaarABCReplicaEquiv K A B C idxABC
          (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x)).2.2 q =
        (pauliHaarABCReplicaEquiv K A B C idxABC x).2.2 (sigma⁻¹ q)
      rw [pauliHaarABCReplicaEquiv_C_apply,
        tripleIndexEquivThreeReplica_slotPermutation_apply]
      exact (pauliHaarABCReplicaEquiv_C_apply
        K A B C idxABC x (sigma⁻¹ q)).symm

/-- Each uniform global Haar permutation-Choi term transports to its common
subsystem-major coordinate presentation. -/
theorem pauliHaarABCPermutationQ_reindex_apply
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau
        ((pauliHaarABCReplicaEquiv K A B C idxABC).symm i,
          (pauliHaarABCReplicaEquiv K A B C idxABC).symm a)
        ((pauliHaarABCReplicaEquiv K A B C idxABC).symm j,
          (pauliHaarABCReplicaEquiv K A B C idxABC).symm b) =
      finiteThreeMomentGlobalHaarChoiQ A B C sigma tau
        (i, a) (j, b) := by
  exact finiteThreeMomentPairQ_reindex_apply
    (pauliHaarABCReplicaEquiv K A B C idxABC)
    (tripleIndexSlotPermutation (PauliBinaryWord K))
    (threeReplicaABCSlotPermutation A B C)
    (pauliHaarABCReplicaEquiv_intertwine K A B C idxABC)
    sigma tau i a j b

/-- Literal Weingarten Choi identity for the concrete global Haar third
twirl.  The off-diagonal representation is the uniform global one. -/
theorem finiteThreeMomentABCHaarCP_choi
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (hD : 3 ≤ 2 ^ K) :
    finiteChoiMatrix
        (finiteThreeMomentABCHaarCP K A B C idxABC).toLinearMap =
      finiteThreeMomentWeingartenRawChoi
        (Fintype.card A * Fintype.card B * Fintype.card C)
        (finiteThreeMomentGlobalHaarChoiQ A B C) := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  unfold finiteThreeMomentABCHaarCP
  rw [finiteChoiMatrix_reindexEquiv_apply]
  rw [finiteChoiMatrix_pauliHaarThirdTwirlCP_eq_weingarten K hD]
  rw [← card_ABC_eq_two_pow_of_pauliEquiv K A B C idxABC]
  unfold finiteThreeMomentWeingartenRawChoi
  simp only [CStarMatrix.smul_apply, cstarMatrix_fintypeSum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro sigma hsigma
  apply Finset.sum_congr rfl
  intro tau htau
  exact congrArg
    (fun z : ℂ ↦
      (normalizedWeingartenThree
        (Fintype.card A * Fintype.card B * Fintype.card C)
        sigma tau : ℂ) • z)
    (pauliHaarABCPermutationQ_reindex_apply
      K A B C idxABC sigma tau i a j b)

/-- Concrete B.21 comparison between the actual global Haar third twirl and
the existing global diagonal reference. -/
theorem relativeCPApproximation_finiteThreeMomentABCHaar_reference
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (hD : 18 ≤ Fintype.card A * Fintype.card B * Fintype.card C) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card A * Fintype.card B *
        Fintype.card C : ℕ) : ℝ) - 9))
      (finiteThreeMomentABCHaarCP K A B C idxABC).toLinearMap
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap := by
  apply relativeCPApproximation_haar_of_weingartenChoi
    (Fintype.card A * Fintype.card B * Fintype.card C) hD
    (finiteThreeMomentGlobalHaarChoiQ A B C)
    (finiteThreeMomentGlobalHaarChoiQ_norm_le_one A B C)
    (finiteThreeMomentGlobalHaarChoiQ_mul A B C)
    (finiteThreeMomentGlobalHaarChoiQ_star A B C)
    (finiteThreeMomentABCHaarCP K A B C idxABC)
    (finiteThreeMomentGlobalReferenceCP A B C)
  · apply finiteThreeMomentABCHaarCP_choi
    rw [← card_ABC_eq_two_pow_of_pauliEquiv K A B C idxABC]
    omega
  · rw [finiteThreeMomentGlobalReferenceCP_choi,
      finiteThreeMomentGlobalReferenceRawChoi_eq_globalHaarApproximate]

/-- Concrete B.22 orientation from the global reference to actual Haar. -/
theorem relativeCPApproximation_finiteThreeMomentGlobalReference_haar
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idxABC : PauliBinaryWord K ≃ (A × B) × C)
    (hD : 18 ≤ Fintype.card A * Fintype.card B * Fintype.card C) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card A * Fintype.card B *
        Fintype.card C : ℕ) : ℝ) - 18))
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap
      (finiteThreeMomentABCHaarCP K A B C idxABC).toLinearMap := by
  apply relativeCPApproximation_reference_of_weingartenChoi
    (Fintype.card A * Fintype.card B * Fintype.card C) hD
    (finiteThreeMomentGlobalHaarChoiQ A B C)
    (finiteThreeMomentGlobalHaarChoiQ_norm_le_one A B C)
    (finiteThreeMomentGlobalHaarChoiQ_mul A B C)
    (finiteThreeMomentGlobalHaarChoiQ_star A B C)
    (finiteThreeMomentABCHaarCP K A B C idxABC)
    (finiteThreeMomentGlobalReferenceCP A B C)
  · apply finiteThreeMomentABCHaarCP_choi
    rw [← card_ABC_eq_two_pow_of_pauliEquiv K A B C idxABC]
    omega
  · rw [finiteThreeMomentGlobalReferenceCP_choi,
      finiteThreeMomentGlobalReferenceRawChoi_eq_globalHaarApproximate]

end

end TomographyOracleCore
