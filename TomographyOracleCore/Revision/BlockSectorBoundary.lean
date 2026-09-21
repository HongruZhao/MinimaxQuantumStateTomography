import TomographyOracleCore.Revision.FourthBoundaryReindex

namespace TomographyOracleCore.Revision.BlockSectorBoundary

open MatrixTensorPi FourthReplicaPermutations FourthSectorDecomposition
open CliffordFourthOmega PauliOmegaProjection PauliOmegaBlocks
open FourthVectorBoundary FourthBoundaryReindex
open scoped BigOperators InnerProductSpace
noncomputable section

local instance (K : ℕ) : DecidableEq (PauliBinaryWord K) :=
  fun a b => Fintype.decidablePiFintype a b

theorem fourthReplicaPermutationMatrix_eq_permutationMatrix
    {α : Type*} [DecidableEq α] (pi : Equiv.Perm (Fin 4)) :
    fourthReplicaPermutationMatrix (ι := α) pi =
      permutationMatrix (permuteFourthTupleEquiv α pi).symm := by
  ext x y
  change (if y = permuteFourthTupleEquiv α pi x then (1 : ℂ) else 0) =
    if x = (permuteFourthTupleEquiv α pi).symm y then 1 else 0
  by_cases h : y = permuteFourthTupleEquiv α pi x
  · subst y
    simp
  · have hn : x ≠ (permuteFourthTupleEquiv α pi).symm y := by
      intro he
      apply h
      rw [he, Equiv.apply_symm_apply]
    simp [h, hn]

def replicaPermutationUnitary
    {α : Type*} [Fintype α] [DecidableEq α] (pi : Equiv.Perm (Fin 4)) :
    Matrix.unitaryGroup (FourthIndex α) ℂ :=
  ⟨fourthReplicaPermutationMatrix pi, by
    rw [fourthReplicaPermutationMatrix_eq_permutationMatrix]
    exact permutationMatrix_mem_unitaryGroup _⟩

theorem replicaPermutation_commute_omega (K : ℕ) (pi : Equiv.Perm (Fin 4)) :
    fourthReplicaPermutationMatrix (ι := PauliBinaryWord K) pi * pauliFourthOmega K =
      pauliFourthOmega K * fourthReplicaPermutationMatrix pi := by
  rw [pauliFourthOmega_eq_scaled_projection, Matrix.mul_smul, Matrix.smul_mul,
    replicaPermutation_commute_projection]

variable {J : Type*} [Fintype J] [DecidableEq J]

def blockReplicaUnitary (K : ℕ) (labels : J → Fin 30) :
    Matrix.unitaryGroup (FourthIndex (J → PauliBinaryWord K)) ℂ :=
  ⟨fourthTensorPi (fun j =>
    fourthReplicaPermutationMatrix (ι := PauliBinaryWord K) (sectorPermutation (labels j))),
    fourthTensorPi_unitary (fun j =>
      replicaPermutationUnitary (α := PauliBinaryWord K) (sectorPermutation (labels j)))⟩

def blockSectors (K : ℕ) (labels : J → Fin 30) :
    Matrix (FourthIndex (J → PauliBinaryWord K)) (FourthIndex (J → PauliBinaryWord K)) ℂ :=
  fourthTensorPi (fun j => wordSector K (labels j))

theorem selectedOmega_commute_blockReplica (K : ℕ) (labels : J → Fin 30) :
    selectedOmega (fun j => (labels j).val < 6) K * (blockReplicaUnitary K labels).val =
      (blockReplicaUnitary K labels).val * selectedOmega (fun j => (labels j).val < 6) K := by
  change fourthTensorPi (fun j => if (labels j).val < 6 then pauliFourthOmega K else 1) *
    fourthTensorPi (fun j => fourthReplicaPermutationMatrix (sectorPermutation (labels j))) =
      fourthTensorPi (fun j => fourthReplicaPermutationMatrix (sectorPermutation (labels j))) *
        fourthTensorPi (fun j => if (labels j).val < 6 then pauliFourthOmega K else 1)
  rw [← fourthTensorPi_mul, ← fourthTensorPi_mul]
  congr 1
  funext j
  split_ifs
  · exact (replicaPermutation_commute_omega K _).symm
  · simp

/-- Every heterogeneous sector tensor has the concrete projection-permutation
form on its actual union of exceptional blocks. -/
theorem blockSectors_eq_selectedOmega_mul_unitary (K : ℕ) (labels : J → Fin 30) :
    blockSectors K labels =
      selectedOmega (fun j => (labels j).val < 6) K * (blockReplicaUnitary K labels).val := by
  change fourthTensorPi (fun j => wordSector K (labels j)) =
    fourthTensorPi (fun j => if (labels j).val < 6 then pauliFourthOmega K else 1) *
      fourthTensorPi (fun j => fourthReplicaPermutationMatrix (sectorPermutation (labels j)))
  rw [← fourthTensorPi_mul]
  congr 1
  funext j
  rw [wordSector_eq_permutation_omega]
  split_ifs
  · exact replicaPermutation_commute_omega K _
  · simp

/-- Arbitrary-entangled boundary bound for every literal tensor of the
thirty Clifford sectors. No boundary, projection, or representation premise
is assumed. -/
theorem norm_blockSectors_expectation_le_one
    (K : ℕ) (labels : J → Fin 30)
    (u : EuclideanSpace ℂ (J → PauliBinaryWord K)) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u, (blockSectors K labels).toEuclideanLin (vectorFourth u)⟫_ℂ‖ ≤ 1 := by
  rw [blockSectors_eq_selectedOmega_mul_unitary]
  exact selectedOmega_unitary_bound _ K (blockReplicaUnitary K labels)
    (selectedOmega_commute_blockReplica K labels) u hu

end
end TomographyOracleCore.Revision.BlockSectorBoundary
