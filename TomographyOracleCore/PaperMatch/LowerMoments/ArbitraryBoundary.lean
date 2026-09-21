import TomographyOracleCore.Revision.PhysicalFourthBoundary

namespace TomographyOracleCore.PaperMatch.LowerMoments

open Revision.FourthVectorBoundary Revision.FourthBoundaryReindex
open Revision.BlockSectorBoundary Revision.FourthSectorDecomposition
open Revision.MatrixTensorPi Revision.PauliOmegaBlocks Revision.PhysicalFourthBoundary
open scoped BigOperators InnerProductSpace
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- Computational bases for blocks of individually specified numbers of qubits. -/
abbrev VariableBlockWords (K : J → ℕ) := (j : J) → PauliBinaryWord (K j)

local instance (K : J → ℕ) : DecidableEq (VariableBlockWords K) := Classical.decEq _

/-- Flatten arbitrary, possibly unequal blocks into their physical qubits. -/
def variableBlockWordEquiv (K : J → ℕ) :
    VariableBlockWords K ≃ ((a : Sigma fun j => Fin (K j)) → PauliBinaryWord 1) where
  toFun x a _ := x a.1 a.2
  invFun x j a := x ⟨j, a⟩ 0
  left_inv x := rfl
  right_inv x := by
    funext a b
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    rfl

/-- The literal tensor product of sector matrices on disjoint blocks. -/
def variableBlockSectors (K : J → ℕ) (labels : J → Fin 30) :
    Matrix (FourthIndex (VariableBlockWords K)) (FourthIndex (VariableBlockWords K)) ℂ :=
  fun x y => ∏ j, wordSector (K j) (labels j)
    (x.1 j, x.2.1 j, x.2.2.1 j, x.2.2.2 j)
    (y.1 j, y.2.1 j, y.2.2.1 j, y.2.2.2 j)

/-- The sector tensor factors over individual qubits, with the same sector
label on all qubits of each block. This is an equality of matrices, not a
hypothesis on their norms. -/
theorem variableBlockSectors_eq_single_qubit_pullback (K : J → ℕ) (labels : J → Fin 30) :
    variableBlockSectors K labels =
      (blockSectors 1 (fun a : Sigma fun j => Fin (K j) => labels a.1)).submatrix
        (fourthMapEquiv (variableBlockWordEquiv K))
        (fourthMapEquiv (variableBlockWordEquiv K)) := by
  classical
  ext x y
  simp only [variableBlockSectors, blockSectors, fourthTensorPi, tensorPi,
    Matrix.submatrix_apply, wordSector_apply, prod_indicator_eq_ite_forall]
  congr 1
  apply propext
  constructor
  · intro h a b
    exact h a.1 a.2
  · intro h j a
    exact h ⟨j, a⟩ 0

/-- The fourth-copy boundary estimate for arbitrary disjoint blocks, including
unequal sizes and test vectors entangled across the blocks. -/
theorem arbitrary_block_boundary (K : J → ℕ) (labels : J → Fin 30)
    (u : EuclideanSpace ℂ (VariableBlockWords K)) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u,
      (variableBlockSectors K labels).toEuclideanLin (vectorFourth u)⟫_ℂ‖ ≤ 1 := by
  classical
  rw [variableBlockSectors_eq_single_qubit_pullback]
  exact norm_pullback_blockSectors_expectation 1 (variableBlockWordEquiv K) _ u hu

end
end TomographyOracleCore.PaperMatch.LowerMoments
