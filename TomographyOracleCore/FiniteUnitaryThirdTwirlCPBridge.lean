import TomographyOracleCore.FiniteUnitaryThirdTwirlComposition
import TomographyOracleCore.RelativeDesignFiniteUnitaryThirdTwirlCP

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance finiteUnitaryThirdTwirlCPBridgeSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance finiteUnitaryThirdTwirlCPBridgeStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Literal completely-positive finite third twirls

This file identifies the completely-positive Kraus average with the literal
`Fin D` third-twirl linear map used by the tomography moment bridge.  It also
shows that the completely-positive representatives respect independent
product ensembles and composition.
-/

/-- On `Fin D`, the generic matrix-space finite twirl is literally the third
twirl used by the tomography bridge. -/
theorem finiteUnitaryThirdTwirlMatrixLinearMap_eq_literal
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlMatrixLinearMap U =
      finiteUnitaryThirdTwirlLinearMap U := by
  rfl

/-- The explicit Kraus average is an unconditional completely-positive
representative of the literal finite third twirl. -/
theorem finiteUnitaryThirdTwirlCP_toLiteralLinearMap
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    (finiteUnitaryThirdTwirlCP U).toLinearMap =
      finiteUnitaryThirdTwirlLinearMap U := by
  rw [finiteUnitaryThirdTwirlCP_toLinearMap,
    finiteUnitaryThirdTwirlMatrixLinearMap_eq_literal]
  rfl

/-- At the level of literal linear maps, the CP representative of an
independent product ensemble is the composition of the two CP
representatives. -/
theorem finiteUnitaryThirdTwirlCP_product_toLinearMap
    {D : ℕ}
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    [Nonempty E₁] [Nonempty E₂]
    (U₁ : E₁ → Matrix.unitaryGroup (Fin D) ℂ)
    (U₂ : E₂ → Matrix.unitaryGroup (Fin D) ℂ) :
    (finiteUnitaryThirdTwirlCP
      (fun e : E₁ × E₂ ↦ U₂ e.2 * U₁ e.1)).toLinearMap =
      (CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP U₂)
        (finiteUnitaryThirdTwirlCP U₁)).toLinearMap := by
  rw [finiteUnitaryThirdTwirlCP_toLiteralLinearMap,
    CompletelyPositiveMap.comp_toLinearMap,
    finiteUnitaryThirdTwirlCP_toLiteralLinearMap,
    finiteUnitaryThirdTwirlCP_toLiteralLinearMap,
    finiteUnitaryThirdTwirlLinearMap_product]
  rfl

/-- The completely-positive maps themselves respect independent product
ensembles. -/
theorem finiteUnitaryThirdTwirlCP_product
    {D : ℕ}
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂]
    [Nonempty E₁] [Nonempty E₂]
    (U₁ : E₁ → Matrix.unitaryGroup (Fin D) ℂ)
    (U₂ : E₂ → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlCP
        (fun e : E₁ × E₂ ↦ U₂ e.2 * U₁ e.1) =
      CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP U₂)
        (finiteUnitaryThirdTwirlCP U₁) := by
  apply DFunLike.coe_injective
  funext X
  exact LinearMap.congr_fun
    (finiteUnitaryThirdTwirlCP_product_toLinearMap U₁ U₂) X

end

end TomographyOracleCore
