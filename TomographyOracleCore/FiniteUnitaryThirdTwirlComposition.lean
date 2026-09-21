import TomographyOracleCore.FiniteUnitaryProjectiveRelativeThirdMoment

namespace TomographyOracleCore

open scoped BigOperators

noncomputable section

/-!
# Composition of independent finite third twirls

The averaged third-moment channel of a product of two independently chosen
unitaries is exactly the composition of their averaged channels.  This is
the algebraic bridge from a literal multi-layer finite circuit ensemble to
the completely-positive-map iteration used by relative-design gluing.
-/

theorem unitaryTensorCubeGeneral_mul
    {D : ℕ}
    (U V : Matrix.unitaryGroup (Fin D) ℂ) :
    unitaryTensorCubeGeneral (U * V) =
      unitaryTensorCubeGeneral U * unitaryTensorCubeGeneral V := by
  unfold unitaryTensorCubeGeneral
  change matrixTensorThree (U.1 * V.1) (U.1 * V.1) (U.1 * V.1) =
    matrixTensorThree U.1 U.1 U.1 * matrixTensorThree V.1 V.1 V.1
  exact matrixTensorThree_mul U.1 U.1 U.1 V.1 V.1 V.1

theorem unitaryThirdConjugationGeneral_comp
    {D : ℕ}
    (U V : Matrix.unitaryGroup (Fin D) ℂ)
    (X : FiniteUnitaryThirdSpace D) :
    unitaryThirdConjugationGeneral U
        (unitaryThirdConjugationGeneral V X) =
      unitaryThirdConjugationGeneral (U * V) X := by
  unfold unitaryThirdConjugationGeneral
  rw [unitaryTensorCubeGeneral_mul, Matrix.conjTranspose_mul]
  noncomm_ring

theorem sum_product_unitaryThirdConjugationGeneral
    {D : ℕ}
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    (U₁ : E₁ → Matrix.unitaryGroup (Fin D) ℂ)
    (U₂ : E₂ → Matrix.unitaryGroup (Fin D) ℂ)
    (X : FiniteUnitaryThirdSpace D) :
    (∑ e : E₁ × E₂,
        unitaryThirdConjugationGeneral (U₂ e.2 * U₁ e.1) X) =
      ∑ e₂ : E₂, unitaryThirdConjugationGeneral (U₂ e₂)
        (∑ e₁ : E₁, unitaryThirdConjugationGeneral (U₁ e₁) X) := by
  rw [Fintype.sum_prod_type]
  simp_rw [← unitaryThirdConjugationGeneral_comp]
  have hsum (e₂ : E₂) :
      unitaryThirdConjugationGeneral (U₂ e₂)
          (∑ e₁ : E₁, unitaryThirdConjugationGeneral (U₁ e₁) X) =
        ∑ e₁ : E₁, unitaryThirdConjugationGeneral (U₂ e₂)
          (unitaryThirdConjugationGeneral (U₁ e₁) X) := by
    unfold unitaryThirdConjugationGeneral
    rw [Matrix.mul_sum, Matrix.sum_mul]
  simp_rw [hsum]
  rw [Finset.sum_comm]

/-- The normalized third twirl of the independent product ensemble
`U₂ * U₁` is the composition `Phi[U₂] ∘ Phi[U₁]`. -/
theorem finiteUnitaryThirdTwirlLinearMap_product
    {D : ℕ}
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    [Nonempty E₁] [Nonempty E₂]
    (U₁ : E₁ → Matrix.unitaryGroup (Fin D) ℂ)
    (U₂ : E₂ → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlLinearMap
        (fun e : E₁ × E₂ ↦ U₂ e.2 * U₁ e.1) =
      (finiteUnitaryThirdTwirlLinearMap U₂).comp
        (finiteUnitaryThirdTwirlLinearMap U₁) := by
  apply LinearMap.ext
  intro X
  change ((Fintype.card (E₁ × E₂) : ℂ)⁻¹) •
      (∑ e : E₁ × E₂,
        unitaryThirdConjugationGeneral (U₂ e.2 * U₁ e.1) X) =
    ((Fintype.card E₂ : ℂ)⁻¹) •
      ∑ e₂ : E₂, unitaryThirdConjugationGeneral (U₂ e₂)
        (((Fintype.card E₁ : ℂ)⁻¹ •
          ∑ e₁ : E₁, unitaryThirdConjugationGeneral (U₁ e₁) X))
  rw [sum_product_unitaryThirdConjugationGeneral U₁ U₂ X]
  simp_rw [unitaryThirdConjugationGeneral_smul]
  rw [← Finset.smul_sum, smul_smul]
  rw [Fintype.card_prod]
  push_cast
  rw [mul_inv_rev]

end
end TomographyOracleCore
