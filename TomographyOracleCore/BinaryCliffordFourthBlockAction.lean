import TomographyOracleCore.BinaryCliffordFourthReplicaReindex

namespace TomographyOracleCore

open scoped BigOperators

noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-!
# Physical fourth-copy action in block-replica coordinates

This file transports the pointwise Pauli-coset fourth-copy action through
the explicit equivalence between four binary words and one four-bit replica
index per qubit.  The resulting unitary and conjugation action are literal
matrices on the same index type as the thirty sector matrices.

Only coordinate transport is proved.  The Pauli-coset ensemble is not given
a group structure, and no sector-invariance statement is made.
-/

/-- Reindexing by the four-word/block-replica equivalence as a complex
matrix algebra equivalence. -/
def fourthCopyBlockReplicaReindexAlgEquiv (K : ℕ) :
    Matrix (FourthIndex (PauliBinaryWord K))
        (FourthIndex (PauliBinaryWord K)) ℂ ≃ₐ[ℂ]
      Matrix (QubitFourthBlockReplicaIndex K)
        (QubitFourthBlockReplicaIndex K) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (fourthIndexPauliBinaryWordEquiv K)

/-- The algebra reindex commutes exactly with conjugate transpose. -/
theorem fourthCopyBlockReplicaReindexAlgEquiv_conjTranspose
    (K : ℕ)
    (A : Matrix (FourthIndex (PauliBinaryWord K))
      (FourthIndex (PauliBinaryWord K)) ℂ) :
    fourthCopyBlockReplicaReindexAlgEquiv K A.conjTranspose =
      (fourthCopyBlockReplicaReindexAlgEquiv K A).conjTranspose := by
  ext i j
  simp [fourthCopyBlockReplicaReindexAlgEquiv,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.conjTranspose_apply]

/-- The literal fourth-copy Pauli-coset Clifford unitary, reindexed onto
the block-replica coordinates used by the sector matrices. -/
noncomputable def pauliCosetCliffordTensorFourthBlock
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (QubitFourthBlockReplicaIndex K) ℂ := by
  refine ⟨fourthCopyBlockReplicaReindexAlgEquiv K
      (pauliCosetCliffordTensorFourth K e).1, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [← fourthCopyBlockReplicaReindexAlgEquiv_conjTranspose]
  rw [← map_mul]
  have hU :
      (pauliCosetCliffordTensorFourth K e).1 *
          (pauliCosetCliffordTensorFourth K e).1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp
        (pauliCosetCliffordTensorFourth K e).2)
  rw [hU]
  simp

@[simp]
theorem pauliCosetCliffordTensorFourthBlock_val
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    (pauliCosetCliffordTensorFourthBlock K e).1 =
      fourthCopyBlockReplicaMatrixEquiv K ℂ
        (pauliCosetCliffordTensorFourth K e).1 :=
  rfl

/-- Pointwise fourth-copy Clifford conjugation directly on block-replica
matrices. -/
noncomputable def pauliCosetCliffordFourthBlockAction
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix (QubitFourthBlockReplicaIndex K)
        (QubitFourthBlockReplicaIndex K) ℂ →ₗ[ℂ]
      Matrix (QubitFourthBlockReplicaIndex K)
        (QubitFourthBlockReplicaIndex K) ℂ :=
  unitaryMatrixConjugationLinearMap
    (pauliCosetCliffordTensorFourthBlock K e)

@[simp]
theorem pauliCosetCliffordFourthBlockAction_apply
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (X : Matrix (QubitFourthBlockReplicaIndex K)
      (QubitFourthBlockReplicaIndex K) ℂ) :
    pauliCosetCliffordFourthBlockAction K e X =
      ((pauliCosetCliffordTensorFourthBlock K e).1 * X) *
        (pauliCosetCliffordTensorFourthBlock K e).1.conjTranspose :=
  rfl

/-- Exact commuting square: conjugating and then reindexing is identical to
reindexing first and conjugating by the reindexed fourth-copy unitary. -/
theorem pauliCosetCliffordFourthBlockAction_reindex
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (X : Matrix (FourthIndex (PauliBinaryWord K))
      (FourthIndex (PauliBinaryWord K)) ℂ) :
    pauliCosetCliffordFourthBlockAction K e
        (fourthCopyBlockReplicaMatrixEquiv K ℂ X) =
      fourthCopyBlockReplicaMatrixEquiv K ℂ
        (pauliCosetCliffordFourthAction K e X) := by
  rw [pauliCosetCliffordFourthBlockAction_apply,
    pauliCosetCliffordTensorFourthBlock_val,
    pauliCosetCliffordFourthAction_apply]
  change
    ((fourthCopyBlockReplicaReindexAlgEquiv K
          (pauliCosetCliffordTensorFourth K e).1 *
        fourthCopyBlockReplicaReindexAlgEquiv K X) *
      (fourthCopyBlockReplicaReindexAlgEquiv K
          (pauliCosetCliffordTensorFourth K e).1).conjTranspose) =
    fourthCopyBlockReplicaReindexAlgEquiv K
      (((pauliCosetCliffordTensorFourth K e).1 * X) *
        (pauliCosetCliffordTensorFourth K e).1.conjTranspose)
  rw [← fourthCopyBlockReplicaReindexAlgEquiv_conjTranspose,
    ← map_mul, ← map_mul]

/-- Entrywise form of the commuting square for an arbitrary matrix already
written in block-replica coordinates. -/
theorem pauliCosetCliffordFourthBlockAction_entry_reindex
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (X : Matrix (QubitFourthBlockReplicaIndex K)
      (QubitFourthBlockReplicaIndex K) ℂ)
    (row column : QubitFourthBlockReplicaIndex K) :
    pauliCosetCliffordFourthBlockAction K e X row column =
      pauliCosetCliffordFourthAction K e
          ((fourthCopyBlockReplicaMatrixEquiv K ℂ).symm X)
          ((fourthIndexPauliBinaryWordEquiv K).symm row)
          ((fourthIndexPauliBinaryWordEquiv K).symm column) := by
  have h := congrFun (congrFun
    (pauliCosetCliffordFourthBlockAction_reindex K e
      ((fourthCopyBlockReplicaMatrixEquiv K ℂ).symm X)) row) column
  rw [(fourthCopyBlockReplicaMatrixEquiv K ℂ).apply_symm_apply] at h
  simpa only [fourthCopyBlockReplicaMatrixEquiv_apply] using h

/-- Fully expanded block-replica entry formula for the physical fourth-copy
conjugation action. -/
theorem pauliCosetCliffordFourthBlockAction_entry
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (X : Matrix (QubitFourthBlockReplicaIndex K)
      (QubitFourthBlockReplicaIndex K) ℂ)
    (row column : QubitFourthBlockReplicaIndex K) :
    pauliCosetCliffordFourthBlockAction K e X row column =
      ∑ intermediate, ∑ source,
        (pauliCosetCliffordTensorFourthBlock K e).1 row source *
          X source intermediate *
          star ((pauliCosetCliffordTensorFourthBlock K e).1
            column intermediate) := by
  rw [pauliCosetCliffordFourthBlockAction_apply]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  simp_rw [Finset.sum_mul]

end

end TomographyOracleCore
