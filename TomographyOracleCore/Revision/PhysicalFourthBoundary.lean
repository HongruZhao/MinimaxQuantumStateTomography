import TomographyOracleCore.Revision.FourthPhysicalSectorCoordinates
import TomographyOracleCore.Revision.FourthSynthesisAdjoint

namespace TomographyOracleCore.Revision.PhysicalFourthBoundary

open FourthVectorBoundary FourthBoundaryReindex BlockSectorBoundary
open FourthPhysicalSectorCoordinates FourthSynthesisAdjoint PauliOmegaBlocks
open CliffordFourthProductProjection
open scoped BigOperators InnerProductSpace
noncomputable section

local instance (K : ℕ) : DecidableEq (PauliBinaryWord K) :=
  fun a b => Fintype.decidablePiFintype a b

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem vectorProjector_conjTranspose (u : EuclideanSpace ℂ α) :
    (vectorProjector u).conjTranspose = vectorProjector u := by
  simp only [vectorProjector, Matrix.conjTranspose_vecMulVec, star_star]

theorem hilbertSchmidt_projector_left (A : Matrix α α ℂ) (u : EuclideanSpace ℂ α) :
    qubitFourthComplexHilbertSchmidt (vectorProjector u) A =
      ⟪u, A.toEuclideanLin u⟫_ℂ := by
  rw [qubitFourthComplexHilbertSchmidt, vectorProjector_conjTranspose,
    Matrix.trace_mul_comm, trace_mul_vectorProjector]

theorem norm_hilbertSchmidt_projector_right (A : Matrix α α ℂ)
    (u : EuclideanSpace ℂ α) :
    ‖qubitFourthComplexHilbertSchmidt A (vectorProjector u)‖ =
      ‖⟪u, A.toEuclideanLin u⟫_ℂ‖ := by
  rw [← hilbertSchmidt_star, norm_star, hilbertSchmidt_projector_left]

theorem norm_pullback_blockSectors_expectation
    {J : Type*} [Fintype J] [DecidableEq J] (K : ℕ)
    (e : α ≃ (J → PauliBinaryWord K)) (labels : J → Fin 30)
    (u : EuclideanSpace ℂ α) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u,
      ((blockSectors K labels).submatrix (fourthMapEquiv e) (fourthMapEquiv e)).toEuclideanLin
        (vectorFourth u)⟫_ℂ‖ ≤ 1 := by
  letI : DecidableEq (J → PauliBinaryWord K) := fun a b => Fintype.decidablePiFintype a b
  have he := fourth_inner_reindex e
    ((blockSectors K labels).submatrix (fourthMapEquiv e) (fourthMapEquiv e)) u
  rw [reindex_pullback] at he
  rw [← he]
  exact norm_blockSectors_expectation_le_one K labels (vectorReindex e u)
    (by rw [(vectorReindex e).norm_map, hu])

theorem norm_physicalBlockSectors_expectation (m K : ℕ) (labels : Fin m → Fin 30)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * K))) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u, (physicalBlockSectors m K labels).toEuclideanLin (vectorFourth u)⟫_ℂ‖ ≤ 1 :=
  norm_pullback_blockSectors_expectation K (binaryWordBlockEquiv m K) labels u hu

theorem physicalShiftedBlockSectors_eq_pullback (m h : ℕ) (labels : Fin m → Fin 30) :
    physicalShiftedBlockSectors m h labels =
      (blockSectors (2 * h) labels).submatrix
        (fourthMapEquiv ((permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h)).symm.trans
          (binaryWordBlockEquiv m (2 * h))))
        (fourthMapEquiv ((permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h)).symm.trans
          (binaryWordBlockEquiv m (2 * h)))) := by
  ext x y
  change unitaryMatrixConjugationLinearMap
    (unitaryTensorFourth ⟨permutationMatrix (permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h)),
      permutationMatrix_mem_unitaryGroup _⟩) (physicalBlockSectors m (2 * h) labels) x y = _
  rw [permutationFourthConjugation_apply]
  rfl

theorem norm_physicalShiftedBlockSectors_boundary (m h : ℕ) (labels : Fin m → Fin 30)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖qubitFourthComplexHilbertSchmidt (physicalShiftedBlockSectors m h labels)
      (vectorProjector (vectorFourth u))‖ ≤ 1 := by
  rw [norm_hilbertSchmidt_projector_right, physicalShiftedBlockSectors_eq_pullback]
  exact norm_pullback_blockSectors_expectation (2 * h) _ labels u hu

end
end TomographyOracleCore.Revision.PhysicalFourthBoundary
