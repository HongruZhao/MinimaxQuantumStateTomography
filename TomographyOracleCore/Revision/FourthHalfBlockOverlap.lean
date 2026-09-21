import TomographyOracleCore.Revision.FourthHalfBlockGeometry
import TomographyOracleCore.Revision.CliffordFourthProductProjection

namespace TomographyOracleCore.Revision.FourthHalfBlockOverlap

open MatrixTensorPi FourthTwirlTensorization FourthHalfBlockGeometry
open PhysicalCliffordFourthTwirl FourthSectorDecomposition
open scoped BigOperators
noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective
local instance : Fintype QubitFourthReplicaIndex := Fintype.ofFinite _

theorem wordSector_hilbertSchmidt (K : ℕ) (i j : Fin 30) :
    qubitFourthComplexHilbertSchmidt (wordSector K i) (wordSector K j) =
      (qubitFourthGramMatrix ((2 : ℝ) ^ K) i j : ℂ) := by
  rw [← hilbertSchmidt_fourthReindex, reindex_wordSector, reindex_wordSector]
  exact qubitFourthSectorR_hilbertSchmidt_eq_gramMatrix K i j

def halfSectors (m h : ℕ) (labels : Fin m → Fin 30) :
    Matrix (FourthIndex ((Fin m × Fin 2) → PauliBinaryWord h))
      (FourthIndex ((Fin m × Fin 2) → PauliBinaryWord h)) ℂ :=
  fourthTensorPi (fun jc : Fin m × Fin 2 => wordSector h (labels jc.1))

def shiftedHalfSectors (m h : ℕ) (labels : Fin m → Fin 30) :
    Matrix (FourthIndex ((Fin m × Fin 2) → PauliBinaryWord h))
      (FourthIndex ((Fin m × Fin 2) → PauliBinaryWord h)) ℂ :=
  fourthTensorPi (fun jc : Fin m × Fin 2 =>
    wordSector h (labels ((halfBlockRotation m).symm jc).1))

/-- The exact overlap of neighboring sector tensors has two Gram factors
per block. No independence or separability condition is placed on a state. -/
theorem halfSectors_overlap (m h : ℕ) (sigma tau : Fin m → Fin 30) :
    qubitFourthComplexHilbertSchmidt (shiftedHalfSectors m h sigma) (halfSectors m h tau) =
      ∏ j : Fin m,
        (qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) : ℂ) *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) : ℂ) := by
  rw [shiftedHalfSectors, halfSectors, fourthTensorPi_hilbertSchmidt]
  simp_rw [wordSector_hilbertSchmidt]
  rw [← Equiv.prod_comp (halfBlockRotation m) (fun jc : Fin m × Fin 2 =>
    (qubitFourthGramMatrix ((2 : ℝ) ^ h)
      (sigma ((halfBlockRotation m).symm jc).1) (tau jc.1) : ℂ))]
  simp only [Equiv.symm_apply_apply]
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro j _
  rw [Fin.prod_univ_two, halfBlockRotation_zero, halfBlockRotation_one]

end
end TomographyOracleCore.Revision.FourthHalfBlockOverlap
