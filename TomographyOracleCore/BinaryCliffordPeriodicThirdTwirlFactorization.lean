import TomographyOracleCore.BinaryCliffordPeriodicCircuit
import TomographyOracleCore.FiniteUnitaryThirdTwirlComposition
import Mathlib.Data.Finset.NoncommProd

namespace TomographyOracleCore

open scoped BigOperators
noncomputable section

/-!
# Exact factorization of the periodic Clifford circuit

This file connects the literal block-tensor circuit to independent local
unitaries.  Both the unshifted and shifted layers are exact products of
single-block embeddings, and the normalized third twirl of the two-layer
product ensemble is the corresponding composition of layer twirls.
-/

/-- Tensoring a family of block unitaries is a monoid homomorphism. -/
noncomputable def blockTensorUnitaryMonoidHom (m K : ℕ) :
    (Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) →*
      Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ where
  toFun := blockTensorUnitary m K
  map_one' := by
    apply Subtype.ext
    exact blockTensorMatrix_one m K
  map_mul' U V := by
    apply Subtype.ext
    exact blockTensorMatrix_mul m K (fun j => (U j).1) (fun j => (V j).1)

/-- One local unitary embedded into one consecutive block of the global register. -/
noncomputable def singleBlockEmbeddedUnitary
    (m K : ℕ) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ :=
  blockTensorUnitaryMonoidHom m K (Pi.mulSingle j U)

theorem singleBlockEmbeddedUnitary_commute
    (m K : ℕ)
    (U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    (i j : Fin m) :
    Commute (singleBlockEmbeddedUnitary m K i (U i))
      (singleBlockEmbeddedUnitary m K j (U j)) := by
  exact (Pi.mulSingle_apply_commute U i j).map
    (blockTensorUnitaryMonoidHom m K)

/-- A consecutive block tensor is exactly the noncommutative product of its
single-block embeddings. -/
theorem blockTensorUnitary_eq_noncommProd_singleBlock
    (m K : ℕ)
    (U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    blockTensorUnitary m K U =
      Finset.univ.noncommProd
        (fun j => singleBlockEmbeddedUnitary m K j (U j))
        (fun i _ j _ _ => singleBlockEmbeddedUnitary_commute m K U i j) := by
  change blockTensorUnitaryMonoidHom m K U = _
  calc
    blockTensorUnitaryMonoidHom m K U =
        blockTensorUnitaryMonoidHom m K
          (Finset.univ.noncommProd
            (fun j => Pi.mulSingle j (U j))
            (fun i _ j _ _ => Pi.mulSingle_apply_commute U i j)) := by
      rw [Finset.noncommProd_mulSingle U]
    _ = _ := Finset.map_noncommProd Finset.univ
      (fun j => Pi.mulSingle j (U j))
      (fun i _ j _ _ => Pi.mulSingle_apply_commute U i j)
      (blockTensorUnitaryMonoidHom m K)

/-- A concrete Pauli-coset block layer is exactly the product of the
independently embedded single-block Clifford choices. -/
theorem blockPauliCosetCliffordUnitary_eq_noncommProd_singleBlock
    (m K : ℕ) (e : Fin m → PauliCosetCliffordEnsemble K) :
    blockPauliCosetCliffordUnitary m K e =
      Finset.univ.noncommProd
        (fun j => singleBlockEmbeddedUnitary m K j
          (pauliCosetCliffordUnitary K (e j)))
        (fun i _ j _ _ => singleBlockEmbeddedUnitary_commute m K
          (fun q => pauliCosetCliffordUnitary K (e q)) i j) := by
  exact blockTensorUnitary_eq_noncommProd_singleBlock m K
    (fun j => pauliCosetCliffordUnitary K (e j))

theorem binaryWordPermutationUnitary_mul_symm
    {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    binaryWordPermutationUnitary σ *
        binaryWordPermutationUnitary σ.symm = 1 := by
  apply Subtype.ext
  ext x y
  change (permutationMatrix (permuteBinaryWord σ) *
      permutationMatrix (permuteBinaryWord σ.symm)) x y =
    (1 : Matrix (PauliBinaryWord N) (PauliBinaryWord N) ℂ) x y
  rw [permutationMatrix_mul_apply]
  simp only [permutationMatrix, Matrix.one_apply]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have hi := congrFun h (σ.symm i)
    simpa using hi
  · intro h
    subst y
    rfl

theorem binaryWordPermutationUnitary_inv
    {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    (binaryWordPermutationUnitary σ)⁻¹ =
      binaryWordPermutationUnitary σ.symm := by
  exact inv_eq_of_mul_eq_one_right
    (binaryWordPermutationUnitary_mul_symm σ)

/-- One consecutive-block unitary, moved onto the shifted block by the
physical qubit-permutation unitary. -/
noncomputable def shiftedSingleBlockEmbeddedUnitary
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ :=
  MulAut.conj (binaryWordPermutationUnitary σ)
    (singleBlockEmbeddedUnitary m K j U)

theorem shiftedSingleBlockEmbeddedUnitary_eq
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    shiftedSingleBlockEmbeddedUnitary m K σ j U =
      binaryWordPermutationUnitary σ *
        (singleBlockEmbeddedUnitary m K j U *
          binaryWordPermutationUnitary σ.symm) := by
  rw [shiftedSingleBlockEmbeddedUnitary, MulAut.conj_apply,
    binaryWordPermutationUnitary_inv, mul_assoc]

theorem shiftedSingleBlockEmbeddedUnitary_commute
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    (i j : Fin m) :
    Commute (shiftedSingleBlockEmbeddedUnitary m K σ i (U i))
      (shiftedSingleBlockEmbeddedUnitary m K σ j (U j)) := by
  exact (singleBlockEmbeddedUnitary_commute m K U i j).map
    (MulAut.conj (binaryWordPermutationUnitary σ))

theorem shiftedBlockPauliCosetCliffordUnitary_eq_conj
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : Fin m → PauliCosetCliffordEnsemble K) :
    shiftedBlockPauliCosetCliffordUnitary m K σ e =
      MulAut.conj (binaryWordPermutationUnitary σ)
        (blockPauliCosetCliffordUnitary m K e) := by
  rw [shiftedBlockPauliCosetCliffordUnitary, MulAut.conj_apply,
    binaryWordPermutationUnitary_inv, mul_assoc]

/-- The shifted block layer is exactly the product of the independently
embedded and physically shifted single-block Clifford choices. -/
theorem shiftedBlockPauliCosetCliffordUnitary_eq_noncommProd_singleBlock
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : Fin m → PauliCosetCliffordEnsemble K) :
    shiftedBlockPauliCosetCliffordUnitary m K σ e =
      Finset.univ.noncommProd
        (fun j => shiftedSingleBlockEmbeddedUnitary m K σ j
          (pauliCosetCliffordUnitary K (e j)))
        (fun i _ j _ _ => shiftedSingleBlockEmbeddedUnitary_commute m K σ
          (fun q => pauliCosetCliffordUnitary K (e q)) i j) := by
  let U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
    fun j => pauliCosetCliffordUnitary K (e j)
  calc
    shiftedBlockPauliCosetCliffordUnitary m K σ e =
        MulAut.conj (binaryWordPermutationUnitary σ)
          (blockTensorUnitary m K U) := by
      rw [shiftedBlockPauliCosetCliffordUnitary_eq_conj]
      rfl
    _ = MulAut.conj (binaryWordPermutationUnitary σ)
        (Finset.univ.noncommProd
          (fun j => singleBlockEmbeddedUnitary m K j (U j))
          (fun i _ j _ _ => singleBlockEmbeddedUnitary_commute m K U i j)) := by
      rw [blockTensorUnitary_eq_noncommProd_singleBlock]
    _ = _ := Finset.map_noncommProd Finset.univ
      (fun j => singleBlockEmbeddedUnitary m K j (U j))
      (fun i _ j _ _ => singleBlockEmbeddedUnitary_commute m K U i j)
      (MulAut.conj (binaryWordPermutationUnitary σ))

/-- Binary computational words, enumerated by the standard finite type of
their exact cardinality.  This local name keeps the factorization module
independent of the much larger physical-channel import graph. -/
noncomputable def factorizationPauliBinaryWordEquivFin (n : ℕ) :
    PauliBinaryWord n ≃ Fin (2 ^ n) :=
  Fintype.equivOfCardEq (by simp [PauliBinaryWord])

theorem factorization_reindexAlgEquiv_conjTranspose
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (idx : α ≃ β) (A : Matrix α α ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ idx A.conjTranspose =
      (Matrix.reindexAlgEquiv ℂ ℂ idx A).conjTranspose := by
  ext i j
  simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.conjTranspose_apply]

/-- Reindex both matrix coordinates of a unitary. -/
noncomputable def factorizationReindexUnitary
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (idx : α ≃ β) (U : Matrix.unitaryGroup α ℂ) :
    Matrix.unitaryGroup β ℂ := by
  refine ⟨Matrix.reindexAlgEquiv ℂ ℂ idx U.1, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [← factorization_reindexAlgEquiv_conjTranspose]
  rw [← map_mul]
  have hU : U.1 * U.1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.2)
  rw [hU]
  simp

/-- Reindexing a unitary is multiplicative. -/
theorem factorizationReindexUnitary_mul
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (idx : α ≃ β) (U V : Matrix.unitaryGroup α ℂ) :
    factorizationReindexUnitary idx (U * V) =
      factorizationReindexUnitary idx U *
        factorizationReindexUnitary idx V := by
  apply Subtype.ext
  exact map_mul (Matrix.reindexAlgEquiv ℂ ℂ idx) U.1 V.1

noncomputable def blockPauliCosetCliffordUnitaryFin
    (m K : ℕ) (e : Fin m → PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  factorizationReindexUnitary
    (factorizationPauliBinaryWordEquivFin (m * K))
    (blockPauliCosetCliffordUnitary m K e)

noncomputable def shiftedBlockPauliCosetCliffordUnitaryFin
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : Fin m → PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  factorizationReindexUnitary
    (factorizationPauliBinaryWordEquivFin (m * K))
    (shiftedBlockPauliCosetCliffordUnitary m K σ e)

/-- Direct standard-index reindexing of the literal periodic circuit. -/
noncomputable def periodicTwoLayerCliffordUnitaryFactorizedFin
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K) :
    Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  factorizationReindexUnitary
    (factorizationPauliBinaryWordEquivFin (m * K))
    (periodicTwoLayerCliffordUnitary m K σ e)

theorem periodicTwoLayerCliffordUnitaryFactorizedFin_eq_mul
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K) :
    periodicTwoLayerCliffordUnitaryFactorizedFin m K σ e =
      blockPauliCosetCliffordUnitaryFin m K e.2 *
        shiftedBlockPauliCosetCliffordUnitaryFin m K σ e.1 := by
  unfold periodicTwoLayerCliffordUnitaryFactorizedFin
  rw [periodicTwoLayerCliffordUnitary,
    factorizationReindexUnitary_mul]
  rfl

set_option maxHeartbeats 1200000 in
/-- The literal finite third twirl of the periodic two-layer circuit is
exactly the composition of the two independently sampled layer twirls. -/
theorem finiteUnitaryThirdTwirlLinearMap_periodicTwoLayer_eq_comp
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) :
    finiteUnitaryThirdTwirlLinearMap
        (periodicTwoLayerCliffordUnitaryFactorizedFin m K σ) =
      (finiteUnitaryThirdTwirlLinearMap
          (blockPauliCosetCliffordUnitaryFin m K)).comp
        (finiteUnitaryThirdTwirlLinearMap
          (shiftedBlockPauliCosetCliffordUnitaryFin m K σ)) := by
  have hunitary : periodicTwoLayerCliffordUnitaryFactorizedFin m K σ =
      fun e => blockPauliCosetCliffordUnitaryFin m K e.2 *
        shiftedBlockPauliCosetCliffordUnitaryFin m K σ e.1 := by
    funext e
    exact periodicTwoLayerCliffordUnitaryFactorizedFin_eq_mul m K σ e
  rw [hunitary]
  exact finiteUnitaryThirdTwirlLinearMap_product
      (U₁ := shiftedBlockPauliCosetCliffordUnitaryFin m K σ)
      (U₂ := blockPauliCosetCliffordUnitaryFin m K)

end
end TomographyOracleCore
