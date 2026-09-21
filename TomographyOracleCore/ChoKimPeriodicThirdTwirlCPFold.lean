import TomographyOracleCore.ChoKimPeriodicThirdTwirlFactorizationBridge
import TomographyOracleCore.FiniteUnitaryThirdTwirlCPBridge

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance choKimCPFoldSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimCPFoldStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # CP realization of the literal Cho--Kim local-twirl folds -/

/-- The identity linear map, packaged as a completely positive map. -/
def CompletelyPositiveMap.identity
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : A →CP A where
  toLinearMap := LinearMap.id
  map_cstarMatrix_nonneg' := by
    intro k M hM
    simpa using hM

@[simp] theorem CompletelyPositiveMap.identity_toLinearMap
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] :
    (CompletelyPositiveMap.identity : A →CP A).toLinearMap =
      LinearMap.id := rfl

/-- Recursive CP composition of independently sampled embedded block
third twirls, in the same reverse order as `reverseFinThirdTwirlFold`. -/
def reverseFinThirdTwirlCPFold
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E] :
    (m : ℕ) →
      (Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) →
      CStarMatrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ →CP
        CStarMatrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ
  | 0, _ => CompletelyPositiveMap.identity
  | m + 1, U =>
      CompletelyPositiveMap.comp
        (reverseFinThirdTwirlCPFold m (fun j ↦ U j.succ))
        (finiteUnitaryThirdTwirlCP (U 0))

/-- The CP fold has exactly the already-audited literal matrix-linear fold
as its underlying map. -/
theorem reverseFinThirdTwirlCPFold_toLinearMap
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (m : ℕ) (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) :
    (reverseFinThirdTwirlCPFold m U).toLinearMap =
      reverseFinThirdTwirlFold m U := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [reverseFinThirdTwirlCPFold,
        CompletelyPositiveMap.comp_toLinearMap,
        ih (fun j ↦ U j.succ),
        finiteUnitaryThirdTwirlCP_toLiteralLinearMap]
      rfl

/-- The literal periodic Cho--Kim finite third-twirl CP map is exactly the
composition of the unshifted and shifted embedded single-block CP folds. -/
theorem finiteUnitaryThirdTwirlCP_choKim_eq_localCPFolds
    {n K : ℕ} (hdiv : K ∣ n) :
    finiteUnitaryThirdTwirlCP
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) =
      CompletelyPositiveMap.comp
        (reverseFinThirdTwirlCPFold (n / K)
          (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv))
        (reverseFinThirdTwirlCPFold (n / K)
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv)) := by
  apply DFunLike.coe_injective
  funext X
  apply LinearMap.congr_fun _ X
  rw [finiteUnitaryThirdTwirlCP_toLiteralLinearMap,
    CompletelyPositiveMap.comp_toLinearMap,
    reverseFinThirdTwirlCPFold_toLinearMap,
    reverseFinThirdTwirlCPFold_toLinearMap]
  exact finiteUnitaryThirdTwirlLinearMap_choKim_eq_localFolds hdiv

end

end TomographyOracleCore
