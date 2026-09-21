import TomographyOracleCore.Revision.FourthTwirlTensorization
import TomographyOracleCore.Revision.FourthBoundaryReindex

namespace TomographyOracleCore.Revision.FourthTwirlTransport

open FourthTwirlTensorization PauliOmegaBlocks
open scoped BigOperators
noncomputable section

variable {α β E F : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
  [Fintype E] [Fintype F]

theorem fourthTensor_reindex (e : α ≃ β) (A B C D : Matrix α α ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e) (matrixTensorFour A B C D) =
      matrixTensorFour (Matrix.reindexAlgEquiv ℂ ℂ e A)
        (Matrix.reindexAlgEquiv ℂ ℂ e B) (Matrix.reindexAlgEquiv ℂ ℂ e C)
        (Matrix.reindexAlgEquiv ℂ ℂ e D) := by
  ext x y
  rfl

theorem fourthConjugation_reindex (e : α ≃ β) (U : Matrix.unitaryGroup α ℂ)
    (X : Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth (reindexUnitary e U))
      (Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e) X) =
      Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e)
        (unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) X) := by
  have ht : (unitaryTensorFourth (reindexUnitary e U)).val =
      Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e) (unitaryTensorFourth U).val :=
    (fourthTensor_reindex e U.val U.val U.val U.val).symm
  rw [unitaryMatrixConjugationLinearMap_apply, ht,
    ← reindexAlgEquiv_conjTranspose, ← map_mul, ← map_mul]
  rfl

theorem fourthAverage_reindex (e : α ≃ β) (U : E → Matrix.unitaryGroup α ℂ)
    (X : Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthAverage (fun t => reindexUnitary e (U t))
      (Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e) X) =
      Matrix.reindexAlgEquiv ℂ ℂ (fourthMapEquiv e) (fourthAverage U X) := by
  simp only [fourthAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    fourthConjugation_reindex, map_smul, map_sum]

theorem fourthConjugation_mul (U V : Matrix.unitaryGroup α ℂ)
    (X : Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth (U * V)) X =
      unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
        (unitaryMatrixConjugationLinearMap (unitaryTensorFourth V) X) := by
  rw [unitaryTensorFourth_mul, unitaryMatrixConjugationLinearMap_mul]
  rfl

theorem fourthAverage_product (U : E → Matrix.unitaryGroup α ℂ)
    (V : F → Matrix.unitaryGroup α ℂ) :
    fourthAverage (fun t : E × F => V t.2 * U t.1) =
      (fourthAverage V).comp (fourthAverage U) := by
  ext X : 1
  simp only [fourthAverage, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, Fintype.sum_prod_type, fourthConjugation_mul,
    map_smul, map_sum, ← Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  rw [mul_comm]

theorem fourthAverage_sandwich (U : E → Matrix.unitaryGroup α ℂ)
    (V W : Matrix.unitaryGroup α ℂ)
    (X : Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    fourthAverage (fun t => V * (U t * W)) X =
      unitaryMatrixConjugationLinearMap (unitaryTensorFourth V)
        (fourthAverage U (unitaryMatrixConjugationLinearMap (unitaryTensorFourth W) X)) := by
  simp only [fourthAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    fourthConjugation_mul, map_smul, map_sum]

end
end TomographyOracleCore.Revision.FourthTwirlTransport
