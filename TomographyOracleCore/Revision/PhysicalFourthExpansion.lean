import TomographyOracleCore.Revision.PhysicalFourthProjection
import TomographyOracleCore.Revision.PhysicalFourthBoundary
import TomographyOracleCore.Revision.FourthSectorExpansionBound

namespace TomographyOracleCore.Revision.PhysicalFourthExpansion

open FourthPhysicalSectorCoordinates PhysicalFourthProjection PhysicalFourthBoundary
open FourthTwirlTensorization FourthTwirlTransport FourthSynthesisAdjoint
open CliffordFourthProductProjection CliffordFourthBasisInput CliffordFourthWgRows
open FourthSectorExpansionBound FourthVectorBoundary
open scoped BigOperators InnerProductSpace
noncomputable section

theorem physicalSectors_overlap_reverse {m h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (sigma tau : Fin m → Fin 30) :
    qubitFourthComplexHilbertSchmidt (physicalBlockSectors m (2 * h) tau)
      (physicalShiftedBlockSectors m h sigma) =
      ((∏ j : Fin m, qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
        qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) : ℝ) : ℂ) := by
  rw [← hilbertSchmidt_star, physicalSectors_overlap hm hh]
  simp only [star_prod, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_prod, Complex.ofReal_mul]
  apply Finset.prod_congr rfl
  intro j _
  ring

def periodicFourthAverage (m h : ℕ) :=
  fourthAverage (periodicTwoLayerCliffordUnitary m (2 * h)
    (cyclicQubitShift (m * (2 * h)) h))

theorem periodicFourthAverage_eq_composition (m h : ℕ) :
    periodicFourthAverage m h =
      (physicalBlockAverage m (2 * h)).comp (physicalShiftedAverage m h) := by
  exact fourthAverage_product _ _

/-- Exact sector expansion of a computational-basis diagonal of the literal
two-layer fourth average. The coefficient is the signed first-layer row sum. -/
theorem periodicFourthAverage_basis_expansion {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (b : PauliBinaryWord (m * (2 * h)))
    (X : Matrix (FourthIndex (PauliBinaryWord (m * (2 * h))))
      (FourthIndex (PauliBinaryWord (m * (2 * h)))) ℂ) :
    qubitFourthComplexHilbertSchmidt
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1) (periodicFourthAverage m h X) =
      (cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) : ℂ) ^ m *
        sectorExpansion (qubitFourthGramMatrix ((2 : ℝ) ^ h))
          (qubitFourthComplexWgMatrix ((2 : ℝ) ^ (2 * h))) m
          (fun zeta => qubitFourthComplexHilbertSchmidt
            (physicalShiftedBlockSectors m h zeta) X) := by
  rw [periodicFourthAverage_eq_composition, LinearMap.comp_apply,
    physicalBlockAverage_selfAdjoint m hK, physicalBlockAverage_basis m hK,
    qubitFourthComplexHilbertSchmidt_smul_left]
  simp only [star_pow, Complex.star_def, Complex.conj_ofReal]
  congr 1
  rw [qubitFourthComplexHilbertSchmidt_sum_left, physicalShiftedAverage_eq_synthesis m hK,
    familySynthesis_apply]
  simp only [qubitFourthComplexHilbertSchmidt_sum_right,
    qubitFourthComplexHilbertSchmidt_smul_right]
  unfold sectorExpansion
  apply Finset.sum_congr rfl
  intro tau _
  apply Finset.sum_congr rfl
  intro sigma _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro zeta _
  rw [physicalSectors_overlap_reverse hm hh]
  unfold blockWgMatrix
  ring

theorem periodicFourthAverage_basis_norm_bound {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (b : PauliBinaryWord (m * (2 * h)))
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖qubitFourthComplexHilbertSchmidt
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
      (periodicFourthAverage m h (vectorProjector (vectorFourth u)))‖ ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ (2 * m)).trace := by
  have hfour : (4 : ℝ) < 2 ^ (2 * h) := by
    calc
      (4 : ℝ) < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (2 * h) := pow_le_pow_right₀ (by norm_num) hK
  have hs : 0 ≤ cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) := by
    rw [cliffordFourthWgSignedRowSum_eq hfour]
    positivity
  rw [periodicFourthAverage_basis_expansion hm hh hK, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
  have hb := norm_sectorExpansion_le_trace
    (qubitFourthGramMatrix ((2 : ℝ) ^ h))
    (qubitFourthGramMatrix_nonneg (by positivity))
    (qubitFourthGramMatrix_comm ((2 : ℝ) ^ h))
    (qubitFourthComplexWgMatrix ((2 : ℝ) ^ (2 * h)))
    (cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)))
    (complexWg_absolute_row_sum ((2 : ℝ) ^ (2 * h))) hm
    (fun zeta => qubitFourthComplexHilbertSchmidt
      (physicalShiftedBlockSectors m h zeta) (vectorProjector (vectorFourth u)))
    (fun zeta => norm_physicalShiftedBlockSectors_boundary m h zeta u hu)
  exact (mul_le_mul_of_nonneg_left hb (pow_nonneg hs m)).trans_eq (mul_assoc _ _ _).symm

end
end TomographyOracleCore.Revision.PhysicalFourthExpansion
