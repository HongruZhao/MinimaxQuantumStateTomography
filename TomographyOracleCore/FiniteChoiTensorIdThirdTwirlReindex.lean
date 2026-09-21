import TomographyOracleCore.RelativeDesignLocalHaarReferenceCP
import TomographyOracleCore.RelativeDesignChoiTensorIdOrder

namespace TomographyOracleCore

universe u v w x y

open scoped CStarAlgebra

noncomputable section

local instance finiteChoiTensorTwirlSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance finiteChoiTensorTwirlStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Choi tensor-identity and literal tensor-identity third twirls

The inactive-register gluing theorem adjoins a common identity factor at the
level of finite Choi matrices.  The circuit geometry instead presents the
same map as a finite unitary third twirl tensored with an identity register.
This file proves that these are exactly the same completely positive map and
records the naturality needed to change the active and inactive coordinates.
-/

/-- The combined three-replica coordinate change induced by a one-replica
split and independent coordinate changes on its active and inactive parts. -/
def tripleIndexActiveInactiveEquiv
    {Q : Type u} {P : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    (split : Q ≃ P × R)
    (active : TripleIndex P ≃ S)
    (inactive : TripleIndex R ≃ T) :
    TripleIndex Q ≃ S × T :=
  (tripleIndexCongr split).trans <|
    (tripleIndexProdEquiv P R).trans (active.prodCongr inactive)

private theorem if_eq_mul_indicator (z : ℂ) (p : Prop) [Decidable p] :
    (if p then z else 0) = z * (if p then 1 else 0) := by
  by_cases hp : p <;> simp [hp]

/-- Adjoining an untouched register through its raw EPR Choi factor is
exactly the finite-unitary third twirl with an identity tensor factor. -/
theorem CompletelyPositiveMap.finiteChoiTensorId_finiteUnitaryThirdTwirlCP
    {P : Type u} {R : Type v} {E : Type w}
    [Fintype P] [Fintype R] [Fintype E]
    [Nonempty P] [Nonempty R] [Nonempty E]
    [DecidableEq P] [DecidableEq R]
    (U : E → Matrix.unitaryGroup P ℂ) :
    CompletelyPositiveMap.finiteChoiTensorId
        (tripleIndexProdEquiv P R) (finiteUnitaryThirdTwirlCP U) =
      finiteUnitaryThirdTwirlTensorIdCP (J := R) U := by
  have hlinear :
      (CompletelyPositiveMap.finiteChoiTensorId
        (tripleIndexProdEquiv P R)
        (finiteUnitaryThirdTwirlCP U)).toLinearMap =
      (finiteUnitaryThirdTwirlTensorIdCP (J := R) U).toLinearMap := by
    apply finiteChoiMatrix_injective
    rw [CompletelyPositiveMap.finiteChoiTensorId_choi,
      finiteChoiMatrix_finiteUnitaryThirdTwirlTensorIdCP]
  apply DFunLike.coe_injective
  funext X
  exact DFunLike.congr_fun hlinear X

/-- The Choi tensor-identity construction is natural under an explicit
one-replica split and independent active/inactive basis changes. -/
theorem CompletelyPositiveMap.finiteChoiTensorId_reindex_active_inactive
    {Q : Type u} {P : Type v} {R : Type w}
    {S : Type x} {T : Type y}
    [Fintype Q] [Fintype P] [Fintype R] [Fintype S] [Fintype T]
    [Nonempty P] [Nonempty R] [Nonempty S] [Nonempty T]
    [DecidableEq Q] [DecidableEq P] [DecidableEq R]
    [DecidableEq S] [DecidableEq T]
    (split : Q ≃ P × R)
    (active : TripleIndex P ≃ S)
    (inactive : TripleIndex R ≃ T)
    (Phi : CStarMatrix (TripleIndex P) (TripleIndex P) ℂ →CP
      CStarMatrix (TripleIndex P) (TripleIndex P) ℂ) :
    CompletelyPositiveMap.finiteChoiTensorId
        (tripleIndexActiveInactiveEquiv split active inactive)
        (CompletelyPositiveMap.reindexEquiv active Phi) =
      CompletelyPositiveMap.reindexEquiv (tripleIndexCongr split).symm
        (CompletelyPositiveMap.finiteChoiTensorId
          (tripleIndexProdEquiv P R) Phi) := by
  have hlinear :
      (CompletelyPositiveMap.finiteChoiTensorId
        (tripleIndexActiveInactiveEquiv split active inactive)
        (CompletelyPositiveMap.reindexEquiv active Phi)).toLinearMap =
      (CompletelyPositiveMap.reindexEquiv (tripleIndexCongr split).symm
        (CompletelyPositiveMap.finiteChoiTensorId
          (tripleIndexProdEquiv P R) Phi)).toLinearMap := by
    apply finiteChoiMatrix_injective
    apply CStarMatrix.ext
    intro ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    simp only [CompletelyPositiveMap.finiteChoiTensorId_choi,
      finiteChoiKroneckerReindex_apply,
      finiteChoiMatrix_reindexEquiv_apply,
      tripleIndexActiveInactiveEquiv, Equiv.trans_apply,
      Equiv.prodCongr_apply, Equiv.symm_symm,
      finiteEPRProjector]
    simp
    exact if_eq_mul_indicator _ _
  apply DFunLike.coe_injective
  funext X
  exact DFunLike.congr_fun hlinear X

/-- Transported form specialized to a concrete finite third twirl. -/
theorem CompletelyPositiveMap.finiteChoiTensorId_reindexedThirdTwirl
    {Q : Type u} {P : Type v} {R : Type w}
    {S : Type x} {T : Type y} {E : Type*}
    [Fintype Q] [Fintype P] [Fintype R] [Fintype S] [Fintype T]
    [Fintype E]
    [Nonempty P] [Nonempty R] [Nonempty S] [Nonempty T] [Nonempty E]
    [DecidableEq Q] [DecidableEq P] [DecidableEq R]
    [DecidableEq S] [DecidableEq T]
    (split : Q ≃ P × R)
    (active : TripleIndex P ≃ S)
    (inactive : TripleIndex R ≃ T)
    (U : E → Matrix.unitaryGroup P ℂ) :
    CompletelyPositiveMap.finiteChoiTensorId
        (tripleIndexActiveInactiveEquiv split active inactive)
        (CompletelyPositiveMap.reindexEquiv active
          (finiteUnitaryThirdTwirlCP U)) =
      CompletelyPositiveMap.reindexEquiv (tripleIndexCongr split).symm
        (finiteUnitaryThirdTwirlTensorIdCP (J := R) U) := by
  rw [CompletelyPositiveMap.finiteChoiTensorId_reindex_active_inactive]
  rw [CompletelyPositiveMap.finiteChoiTensorId_finiteUnitaryThirdTwirlCP]

end

end TomographyOracleCore
