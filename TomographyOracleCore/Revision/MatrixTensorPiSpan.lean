import TomographyOracleCore.Revision.MatrixTensorPi

namespace TomographyOracleCore.Revision.MatrixTensorPiSpan

open MatrixTensorPi FourthSectorDecomposition
open scoped BigOperators
noncomputable section

variable {J α : Type*} [Fintype J] [DecidableEq J] [Fintype α] [DecidableEq α]

theorem tensorPi_single (a b : J → α) :
    tensorPi (fun j => Matrix.single (a j) (b j) (1 : ℂ)) = Matrix.single a b 1 := by
  classical
  ext x y
  simp only [tensorPi, Matrix.single, Matrix.of_apply, prod_indicator_eq_ite_forall,
    forall_and, ← funext_iff]

/-- Tensor products of literal matrix units span all operators, including
operators representing arbitrarily entangled inputs. -/
theorem linearMap_ext_on_tensorPi
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (L M : Matrix (J → α) (J → α) ℂ →ₗ[ℂ] E)
    (h : ∀ A : J → Matrix α α ℂ, L (tensorPi A) = M (tensorPi A)) : L = M := by
  classical
  apply LinearMap.ext
  intro X
  rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hs : Matrix.single a b (X a b) =
      X a b • tensorPi (fun j => Matrix.single (a j) (b j) (1 : ℂ)) := by
    rw [tensorPi_single, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hs, map_smul, map_smul, h]

theorem linearMap_ext_on_fourthTensorPi
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (L M : Matrix (FourthIndex (J → α)) (FourthIndex (J → α)) ℂ →ₗ[ℂ] E)
    (h : ∀ A : J → Matrix (FourthIndex α) (FourthIndex α) ℂ,
      L (fourthTensorPi A) = M (fourthTensorPi A)) : L = M := by
  classical
  let R := Matrix.reindexAlgEquiv ℂ ℂ (fourthPiEquiv J α).symm
  have hh : L.comp R.toLinearMap = M.comp R.toLinearMap := by
    apply linearMap_ext_on_tensorPi
    intro A
    exact h A
  apply LinearMap.ext
  intro X
  have hx := congrArg (fun F : Matrix (J → FourthIndex α) (J → FourthIndex α) ℂ →ₗ[ℂ] E =>
    F (R.symm X)) hh
  simpa only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, AlgEquiv.apply_symm_apply] using hx

end
end TomographyOracleCore.Revision.MatrixTensorPiSpan
