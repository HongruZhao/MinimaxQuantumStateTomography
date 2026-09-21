import TomographyOracleCore.RelativeDesignFiniteUnitaryThirdTwirlCP

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance pauliHaarAbsorptionSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance pauliHaarAbsorptionStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Exact absorption by the Haar third twirl

Normalized Haar averaging absorbs any finite average of unitary
three-replica conjugations on its input side.  This is the exact endpoint
needed for the closing edge of the periodic Cho--Kim traversal, after the
active support has already become the whole register.
-/

/-- Haar third twirling after an arbitrary finite unitary third twirl is
exactly Haar third twirling. -/
theorem pauliHaarThirdTwirlLinearMap_comp_finiteUnitaryThirdTwirlMatrixLinearMap
    (K : ℕ) {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    (pauliHaarThirdTwirlLinearMap K).comp
        (finiteUnitaryThirdTwirlMatrixLinearMap U) =
      pauliHaarThirdTwirlLinearMap K := by
  apply LinearMap.ext
  intro X
  rw [LinearMap.comp_apply]
  rw [finiteUnitaryThirdTwirlMatrixLinearMap_apply]
  rw [map_smul, map_sum]
  change ((Fintype.card E : ℂ)⁻¹) •
      ∑ e : E,
        pauliHaarThirdTwirl K (unitaryThirdConjugation K (U e) X) = _
  simp_rw [pauliHaarThirdTwirl_conjugation]
  have hcard : (Fintype.card E : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hsum :
      (∑ _e : E, pauliHaarThirdTwirl K X) =
        (Fintype.card E : ℂ) • pauliHaarThirdTwirl K X := by
    ext i j
    simp
  rw [hsum]
  exact inv_smul_smul₀ hcard _

/-- Completely-positive form of finite-twirl absorption. -/
theorem pauliHaarThirdTwirlCP_comp_finiteUnitaryThirdTwirlCP
    (K : ℕ) {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    CompletelyPositiveMap.comp (pauliHaarThirdTwirlCP K)
        (finiteUnitaryThirdTwirlCP U) =
      pauliHaarThirdTwirlCP K := by
  apply DFunLike.coe_injective
  funext X
  change (pauliHaarThirdTwirlCP K).toLinearMap
      ((finiteUnitaryThirdTwirlCP U).toLinearMap X) =
    (pauliHaarThirdTwirlCP K).toLinearMap X
  rw [pauliHaarThirdTwirlCP_toLinearMap,
    finiteUnitaryThirdTwirlCP_toLinearMap]
  change CStarMatrix.ofMatrix
      (pauliHaarThirdTwirlLinearMap K
        (finiteUnitaryThirdTwirlMatrixLinearMap U
          (CStarMatrix.ofMatrix.symm X))) =
    CStarMatrix.ofMatrix
      (pauliHaarThirdTwirlLinearMap K
        (CStarMatrix.ofMatrix.symm X))
  exact congrArg CStarMatrix.ofMatrix <|
    LinearMap.congr_fun
      (pauliHaarThirdTwirlLinearMap_comp_finiteUnitaryThirdTwirlMatrixLinearMap
        K U) (CStarMatrix.ofMatrix.symm X)

end

end TomographyOracleCore
