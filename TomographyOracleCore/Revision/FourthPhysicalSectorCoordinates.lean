import TomographyOracleCore.Revision.FourthHalfBlockOverlap
import TomographyOracleCore.Revision.BlockSectorBoundary

namespace TomographyOracleCore.Revision.FourthPhysicalSectorCoordinates

open MatrixTensorPi FourthSectorBlocks FourthHalfBlockGeometry FourthHalfBlockOverlap
open PauliOmegaBlocks CliffordFourthProductProjection FourthSectorDecomposition
open scoped BigOperators
noncomputable section

def physicalBlockSectors (m K : ℕ) (labels : Fin m → Fin 30) :
    Matrix (FourthIndex (PauliBinaryWord (m * K))) (FourthIndex (PauliBinaryWord (m * K))) ℂ :=
  (blockSectorFamily K labels).submatrix
    (fourthMapEquiv (binaryWordBlockEquiv m K)) (fourthMapEquiv (binaryWordBlockEquiv m K))

/-- Ordered blocks in the literal register have the claimed two half-block
sector factors. -/
theorem physicalBlockSectors_eq_half (m h : ℕ) (labels : Fin m → Fin 30) :
    physicalBlockSectors m (2 * h) labels =
      (halfSectors m h labels).submatrix
        (fourthMapEquiv (halfWordEquiv m h)) (fourthMapEquiv (halfWordEquiv m h)) := by
  classical
  ext x y
  change (∏ j : Fin m, wordSector (2 * h) (labels j)
    (fourthPiEquiv (Fin m) (PauliBinaryWord (2 * h))
      (fourthMapEquiv (binaryWordBlockEquiv m (2 * h)) x) j)
    (fourthPiEquiv (Fin m) (PauliBinaryWord (2 * h))
      (fourthMapEquiv (binaryWordBlockEquiv m (2 * h)) y) j)) =
    ∏ jc : Fin m × Fin 2, wordSector h (labels jc.1)
      (fourthPiEquiv (Fin m × Fin 2) (PauliBinaryWord h)
        (fourthMapEquiv (halfWordEquiv m h) x) jc)
      (fourthPiEquiv (Fin m × Fin 2) (PauliBinaryWord h)
        (fourthMapEquiv (halfWordEquiv m h) y) jc)
  simp_rw [wordSector_binary_blocks 2 h]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro c _
  rfl

theorem fourthTensor_permutationMatrix
    {α : Type*} [DecidableEq α] (e : Equiv.Perm α) :
    matrixTensorFour (permutationMatrix e) (permutationMatrix e)
      (permutationMatrix e) (permutationMatrix e) = permutationMatrix (fourthMapEquiv e) := by
  ext x y
  rcases x with ⟨x₁, x₂, x₃, x₄⟩
  rcases y with ⟨y₁, y₂, y₃, y₄⟩
  simp only [matrixTensorFour_apply, permutationMatrix, fourthMapEquiv,
    Equiv.prodCongr_apply, Prod.map_apply, Prod.mk.injEq, ite_and]
  split_ifs <;> simp_all

theorem permutationFourthConjugation_apply
    {α : Type*} [Fintype α] [DecidableEq α] (e : Equiv.Perm α)
    (A : Matrix (FourthIndex α) (FourthIndex α) ℂ) (x y : FourthIndex α) :
    unitaryMatrixConjugationLinearMap
      (unitaryTensorFourth ⟨permutationMatrix e, permutationMatrix_mem_unitaryGroup e⟩) A x y =
        A ((fourthMapEquiv e).symm x) ((fourthMapEquiv e).symm y) := by
  change ((matrixTensorFour (permutationMatrix e) (permutationMatrix e)
      (permutationMatrix e) (permutationMatrix e) * A) *
    (matrixTensorFour (permutationMatrix e) (permutationMatrix e)
      (permutationMatrix e) (permutationMatrix e)).conjTranspose) x y = _
  rw [fourthTensor_permutationMatrix, permutationMatrix_conjTranspose,
    mul_permutationMatrix_apply, permutationMatrix_mul_apply]

def physicalShiftedBlockSectors (m h : ℕ) (labels : Fin m → Fin 30) :
    Matrix (FourthIndex (PauliBinaryWord (m * (2 * h))))
      (FourthIndex (PauliBinaryWord (m * (2 * h)))) ℂ :=
  unitaryMatrixConjugationLinearMap
    (unitaryTensorFourth (binaryWordPermutationUnitary (cyclicQubitShift (m * (2 * h)) h)))
      (physicalBlockSectors m (2 * h) labels)

theorem physicalShiftedBlockSectors_eq_half
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h) (labels : Fin m → Fin 30) :
    physicalShiftedBlockSectors m h labels =
      (shiftedHalfSectors m h labels).submatrix
        (fourthMapEquiv (halfWordEquiv m h)) (fourthMapEquiv (halfWordEquiv m h)) := by
  classical
  ext x y
  rw [physicalShiftedBlockSectors]
  change unitaryMatrixConjugationLinearMap
    (unitaryTensorFourth ⟨permutationMatrix (permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h)),
      permutationMatrix_mem_unitaryGroup _⟩) (physicalBlockSectors m (2 * h) labels) x y = _
  rw [permutationFourthConjugation_apply, physicalBlockSectors_eq_half]
  change (∏ jc : Fin m × Fin 2, wordSector h (labels jc.1)
      (fourthPiEquiv (Fin m × Fin 2) (PauliBinaryWord h)
        (fourthMapEquiv (halfWordEquiv m h)
          ((fourthMapEquiv (permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h))).symm x)) jc)
      (fourthPiEquiv (Fin m × Fin 2) (PauliBinaryWord h)
        (fourthMapEquiv (halfWordEquiv m h)
          ((fourthMapEquiv (permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h))).symm y)) jc)) = _
  have hs (z : FourthIndex (PauliBinaryWord (m * (2 * h)))) (jc : Fin m × Fin 2) :
      fourthPiEquiv (Fin m × Fin 2) (PauliBinaryWord h)
        (fourthMapEquiv (halfWordEquiv m h)
          ((fourthMapEquiv (permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h))).symm z)) jc =
      fourthPiEquiv (Fin m × Fin 2) (PauliBinaryWord h)
        (fourthMapEquiv (halfWordEquiv m h) z) (halfBlockRotation m jc) := by
    apply Prod.ext
    · funext a; exact halfWordEquiv_shift_symm hm hh z.1 jc a
    · apply Prod.ext
      · funext a; exact halfWordEquiv_shift_symm hm hh z.2.1 jc a
      · apply Prod.ext
        · funext a; exact halfWordEquiv_shift_symm hm hh z.2.2.1 jc a
        · funext a; exact halfWordEquiv_shift_symm hm hh z.2.2.2 jc a
  simp_rw [hs]
  change (∏ jc : Fin m × Fin 2, wordSector h (labels jc.1)
    (fourthPiEquiv _ _ (fourthMapEquiv (halfWordEquiv m h) x) (halfBlockRotation m jc))
    (fourthPiEquiv _ _ (fourthMapEquiv (halfWordEquiv m h) y) (halfBlockRotation m jc))) =
      ∏ jc : Fin m × Fin 2, wordSector h (labels ((halfBlockRotation m).symm jc).1)
        (fourthPiEquiv _ _ (fourthMapEquiv (halfWordEquiv m h) x) jc)
        (fourthPiEquiv _ _ (fourthMapEquiv (halfWordEquiv m h) y) jc)
  have hp := Equiv.prod_comp (halfBlockRotation m) (fun jc : Fin m × Fin 2 =>
    wordSector h (labels ((halfBlockRotation m).symm jc).1)
      (fourthPiEquiv _ _ (fourthMapEquiv (halfWordEquiv m h) x) jc)
      (fourthPiEquiv _ _ (fourthMapEquiv (halfWordEquiv m h) y) jc))
  simpa only [Equiv.symm_apply_apply] using hp

theorem physicalSectors_overlap {m h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (sigma tau : Fin m → Fin 30) :
    qubitFourthComplexHilbertSchmidt (physicalShiftedBlockSectors m h sigma)
      (physicalBlockSectors m (2 * h) tau) =
      ∏ j : Fin m,
        (qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) : ℂ) *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) : ℂ) := by
  rw [physicalShiftedBlockSectors_eq_half hm hh, physicalBlockSectors_eq_half,
    FourthTwirlTensorization.submatrix_hilbertSchmidt]
  exact halfSectors_overlap m h sigma tau

end
end TomographyOracleCore.Revision.FourthPhysicalSectorCoordinates
