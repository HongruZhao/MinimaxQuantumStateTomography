import TomographyOracleCore.Revision.FourthSynthesisAdjoint
import TomographyOracleCore.Revision.FourthBoundaryReindex

namespace TomographyOracleCore.Revision.FourthSynthesisTransport

open CliffordFourthProductProjection FourthTwirlTensorization
open scoped BigOperators
noncomputable section

variable {α β L : Type*} [Fintype α] [Fintype β] [Fintype L]
  [DecidableEq α] [DecidableEq β]

theorem familySynthesis_reindex (e : α ≃ β) (S : L → Matrix α α ℂ)
    (W : Matrix L L ℂ) (X : Matrix α α ℂ) :
    familySynthesis (fun i => Matrix.reindexAlgEquiv ℂ ℂ e (S i)) W
      (Matrix.reindexAlgEquiv ℂ ℂ e X) =
      Matrix.reindexAlgEquiv ℂ ℂ e (familySynthesis S W X) := by
  simp only [familySynthesis_apply, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show qubitFourthComplexHilbertSchmidt
      (Matrix.reindexAlgEquiv ℂ ℂ e (S j)) (Matrix.reindexAlgEquiv ℂ ℂ e X) =
      qubitFourthComplexHilbertSchmidt (S j) X from submatrix_hilbertSchmidt e.symm _ _]

theorem conjugation_hilbertSchmidt (U : Matrix.unitaryGroup α ℂ)
    (X Y : Matrix α α ℂ) :
    qubitFourthComplexHilbertSchmidt (unitaryMatrixConjugationLinearMap U X)
      (unitaryMatrixConjugationLinearMap U Y) = qubitFourthComplexHilbertSchmidt X Y := by
  rw [unitaryMatrixConjugationLinearMap_inverse_adjoint]
  have hc : unitaryMatrixConjugationLinearMap U⁻¹
      (unitaryMatrixConjugationLinearMap U X) = X := by
    change (unitaryMatrixConjugationLinearMap U⁻¹ * unitaryMatrixConjugationLinearMap U) X = X
    rw [← unitaryMatrixConjugationLinearMap_mul, inv_mul_cancel,
      unitaryMatrixConjugationLinearMap_one]
    rfl
  rw [hc]

theorem familySynthesis_conjugation (U : Matrix.unitaryGroup α ℂ)
    (S : L → Matrix α α ℂ) (W : Matrix L L ℂ) (X : Matrix α α ℂ) :
    familySynthesis (fun i => unitaryMatrixConjugationLinearMap U (S i)) W
      (unitaryMatrixConjugationLinearMap U X) =
      unitaryMatrixConjugationLinearMap U (familySynthesis S W X) := by
  simp only [familySynthesis_apply, conjugation_hilbertSchmidt, map_sum, map_smul]

end
end TomographyOracleCore.Revision.FourthSynthesisTransport
