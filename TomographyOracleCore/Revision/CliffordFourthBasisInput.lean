import TomographyOracleCore.Revision.CliffordFourthProductProjection
import TomographyOracleCore.Revision.CliffordFourthWgRows

namespace TomographyOracleCore.Revision.CliffordFourthBasisInput

open CliffordFourthProductProjection CliffordFourthWgRows FourthSectorDecomposition
open FourthReplicaPermutations CliffordFourthOmega BinaryCliffordNeutralFourth
open scoped BigOperators
noncomputable section

def repeatedFourth {α : Type*} (b : α) : FourthIndex α := (b, b, b, b)

theorem coordinates_repeatedFourth {α : Type*} (b : α) (i : Fin 4) :
    fourthTupleCoordinatesEquiv α (repeatedFourth b) i = b := by
  fin_cases i <;> rfl

theorem permuteFourthTuple_repeated {α : Type*} (pi : Equiv.Perm (Fin 4)) (b : α) :
    permuteFourthTuple pi (repeatedFourth b) = repeatedFourth b := by
  apply (fourthTupleCoordinatesEquiv α).injective
  funext i
  rw [coordinates_permuteFourthTuple, coordinates_repeatedFourth, coordinates_repeatedFourth]

theorem pauliFourthOmega_repeated_diagonal (K : ℕ) (b : PauliBinaryWord K) :
    pauliFourthOmega K (repeatedFourth b) (repeatedFourth b) = 1 := by
  rw [pauliFourthOmega_apply]
  apply if_pos
  simp only [fourthOmegaSupport, fourthWordSum, fourthPauliShiftMatches,
    repeatedFourth, binaryWord_add_self, zero_add, add_zero, and_self]

theorem wordSector_repeated_diagonal (K : ℕ) (i : Fin 30) (b : PauliBinaryWord K) :
    wordSector K i (repeatedFourth b) (repeatedFourth b) = 1 := by
  rw [wordSector_eq_permutation_omega]
  split_ifs
  · rw [fourthReplicaPermutationMatrix_mul, permuteFourthTuple_repeated,
      pauliFourthOmega_repeated_diagonal]
  · simp only [fourthReplicaPermutationMatrix, permuteFourthTuple_repeated, if_true]

theorem hilbertSchmidt_single_diagonal
    {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (b : α) :
    qubitFourthComplexHilbertSchmidt A (Matrix.single b b 1) = star (A b b) := by
  classical
  simp [qubitFourthComplexHilbertSchmidt_eq_entrywise, Matrix.single, ite_and]

/-- Every computational-basis input has exactly the same fourth-twirl
image. No distributional invariance of the chosen Clifford section is
assumed. -/
theorem finiteCliffordFourthAverage_basis {K : ℕ} (hK : 3 ≤ K) (b : PauliBinaryWord K) :
    finiteCliffordFourthAverage K (Matrix.single (repeatedFourth b) (repeatedFourth b) 1) =
      (cliffordFourthWgSignedRowSum ((2 : ℝ) ^ K) : ℂ) • ∑ i : Fin 30, wordSector K i := by
  rw [wordFourthAverage_eq_sum hK]
  simp_rw [hilbertSchmidt_single_diagonal, wordSector_repeated_diagonal, star_one, mul_one]
  simp_rw [← Finset.sum_smul, complexWg_signed_row_sum]
  rw [Finset.smul_sum]

end
end TomographyOracleCore.Revision.CliffordFourthBasisInput
