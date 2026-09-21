import TomographyOracleCore.Revision.FourthPhysicalSectorCoordinates
import TomographyOracleCore.Revision.FourthTwirlTransport
import TomographyOracleCore.Revision.FourthSynthesisTransport
import TomographyOracleCore.Revision.CliffordFourthBasisInput
import TomographyOracleCore.BinaryCliffordPeriodicThirdTwirlFactorization

namespace TomographyOracleCore.Revision.PhysicalFourthProjection

open MatrixTensorPi FourthTwirlTensorization FourthTwirlTransport FourthSynthesisTransport
open FourthPhysicalSectorCoordinates CliffordFourthProductProjection FourthSynthesisAdjoint
open PauliOmegaBlocks CliffordFourthBasisInput CliffordFourthWgRows
open scoped BigOperators
noncomputable section

local instance (K : ℕ) : DecidableEq (PauliBinaryWord K) :=
  fun a b => Fintype.decidablePiFintype a b

theorem blockUnitary_eq_reindex (m K : ℕ) (e : Fin m → PauliCosetCliffordEnsemble K) :
    blockPauliCosetCliffordUnitary m K e =
      reindexUnitary (binaryWordBlockEquiv m K).symm
        (tensorPiUnitary (fun j => pauliCosetCliffordUnitary K (e j))) := by
  apply Subtype.ext
  rfl

def physicalBlockAverage (m K : ℕ) := fourthAverage (blockPauliCosetCliffordUnitary m K)

set_option maxHeartbeats 1000000 in
theorem physicalBlockAverage_eq_synthesis (m : ℕ) {K : ℕ} (hK : 3 ≤ K) :
    physicalBlockAverage m K = familySynthesis (physicalBlockSectors m K) (blockWgMatrix K) := by
  apply LinearMap.ext
  intro X
  let R := Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv (binaryWordBlockEquiv m K).symm)
  obtain ⟨Y, rfl⟩ := R.surjective X
  change fourthAverage (blockPauliCosetCliffordUnitary m K) (R Y) = _
  have hfun : blockPauliCosetCliffordUnitary m K =
      (fun e => reindexUnitary (binaryWordBlockEquiv m K).symm
        (tensorPiUnitary (fun j => pauliCosetCliffordUnitary K (e j)))) :=
    funext (blockUnitary_eq_reindex m K)
  rw [hfun]
  rw [fourthAverage_reindex]
  change R (blockFourthAverage K Y) = _
  rw [blockFourthAverage_eq_synthesis hK]
  exact (familySynthesis_reindex (fourthMapEquiv (binaryWordBlockEquiv m K).symm)
    (blockSectorFamily K) (blockWgMatrix K) Y).symm

theorem physicalBlockAverage_selfAdjoint (m : ℕ) {K : ℕ} (hK : 3 ≤ K)
    (X Y : Matrix (FourthIndex (PauliBinaryWord (m * K)))
      (FourthIndex (PauliBinaryWord (m * K))) ℂ) :
    qubitFourthComplexHilbertSchmidt Y (physicalBlockAverage m K X) =
      qubitFourthComplexHilbertSchmidt (physicalBlockAverage m K Y) X := by
  rw [physicalBlockAverage_eq_synthesis m hK]
  exact familySynthesis_selfAdjoint _ _ (blockWg_star K) X Y

theorem physicalBlockSectors_repeated_diagonal (m K : ℕ)
    (i : Fin m → Fin 30) (b : PauliBinaryWord (m * K)) :
    physicalBlockSectors m K i (repeatedFourth b) (repeatedFourth b) = 1 := by
  change (∏ j : Fin m, FourthSectorDecomposition.wordSector K (i j)
    (repeatedFourth (binaryWordBlockEquiv m K b j))
    (repeatedFourth (binaryWordBlockEquiv m K b j))) = 1
  simp only [wordSector_repeated_diagonal, Finset.prod_const_one]

theorem blockWg_signed_row_sum (m K : ℕ) (i : Fin m → Fin 30) :
    ∑ j : Fin m → Fin 30, blockWgMatrix K i j =
      (cliffordFourthWgSignedRowSum ((2 : ℝ) ^ K) : ℂ) ^ m := by
  change (∑ j : Fin m → Fin 30, ∏ a : Fin m,
    qubitFourthComplexWgMatrix ((2 : ℝ) ^ K) (i a) (j a)) = _
  rw [← Fintype.prod_sum]
  simp only [complexWg_signed_row_sum, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem physicalBlockAverage_basis (m : ℕ) {K : ℕ} (hK : 3 ≤ K)
    (b : PauliBinaryWord (m * K)) :
    physicalBlockAverage m K (Matrix.single (repeatedFourth b) (repeatedFourth b) 1) =
      (cliffordFourthWgSignedRowSum ((2 : ℝ) ^ K) : ℂ) ^ m •
        ∑ i : Fin m → Fin 30, physicalBlockSectors m K i := by
  rw [physicalBlockAverage_eq_synthesis m hK, familySynthesis_apply]
  simp_rw [hilbertSchmidt_single_diagonal, physicalBlockSectors_repeated_diagonal,
    star_one, mul_one, ← Finset.sum_smul, blockWg_signed_row_sum]
  rw [Finset.smul_sum]

def physicalShiftedAverage (m h : ℕ) :=
  fourthAverage (shiftedBlockPauliCosetCliffordUnitary m (2 * h)
    (cyclicQubitShift (m * (2 * h)) h))

theorem physicalShiftedAverage_eq_synthesis (m : ℕ) {h : ℕ} (hh : 3 ≤ 2 * h) :
    physicalShiftedAverage m h =
      familySynthesis (physicalShiftedBlockSectors m h) (blockWgMatrix (2 * h)) := by
  apply LinearMap.ext
  intro X
  let U := binaryWordPermutationUnitary (cyclicQubitShift (m * (2 * h)) h)
  let C := unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
  let Ci := unitaryMatrixConjugationLinearMap (unitaryTensorFourth U⁻¹)
  have hcancel : C (Ci X) = X := by
    change (unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) *
      unitaryMatrixConjugationLinearMap (unitaryTensorFourth U⁻¹)) X = X
    rw [← unitaryMatrixConjugationLinearMap_mul, ← unitaryTensorFourth_mul,
      mul_inv_cancel, unitaryTensorFourth_one, unitaryMatrixConjugationLinearMap_one]
    rfl
  change fourthAverage (fun e => U * (blockPauliCosetCliffordUnitary m (2 * h) e *
    binaryWordPermutationUnitary (cyclicQubitShift (m * (2 * h)) h).symm)) X = _
  rw [← binaryWordPermutationUnitary_inv, fourthAverage_sandwich]
  change C (physicalBlockAverage m (2 * h) (Ci X)) = _
  rw [physicalBlockAverage_eq_synthesis m hh]
  have ht := familySynthesis_conjugation (unitaryTensorFourth U)
    (physicalBlockSectors m (2 * h)) (blockWgMatrix (2 * h)) (Ci X)
  rw [hcancel] at ht
  exact ht.symm

theorem physicalShiftedAverage_selfAdjoint (m : ℕ) {h : ℕ} (hh : 3 ≤ 2 * h)
    (X Y : Matrix (FourthIndex (PauliBinaryWord (m * (2 * h))))
      (FourthIndex (PauliBinaryWord (m * (2 * h)))) ℂ) :
    qubitFourthComplexHilbertSchmidt Y (physicalShiftedAverage m h X) =
      qubitFourthComplexHilbertSchmidt (physicalShiftedAverage m h Y) X := by
  rw [physicalShiftedAverage_eq_synthesis m hh]
  exact familySynthesis_selfAdjoint _ _ (blockWg_star (2 * h)) X Y

end
end TomographyOracleCore.Revision.PhysicalFourthProjection
