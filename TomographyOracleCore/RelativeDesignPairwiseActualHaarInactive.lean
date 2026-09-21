import TomographyOracleCore.RelativeDesignThreeMomentInactiveReferenceGluing
import TomographyOracleCore.RelativeDesignPairwiseActualHaarGluing

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra

noncomputable section

local instance pairwiseInactiveSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance pairwiseInactiveStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Pairwise actual-Haar gluing with a common inactive register

All maps on the active `A,B,C` component are lifted by the same raw EPR
factor on `ThreeReplica R`.  The already proved B.27 reference gluing theorem
is lifted verbatim; no second Gram estimate is needed.
-/

/-- One actual-Haar gluing step after adjoining an arbitrary one-replica
inactive register.  The two local B.21 and final B.22 inputs are deliberately
stated in their already weakened manuscript errors `d` and `b`; B.27 is
derived here from the concrete finite references and weakened only using
`q ≤ card B`. -/
theorem relativeCPApproximation_pairwiseActualHaar_inactive_of_base
    (A B C R I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq R] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × ThreeReplica R)
    (q : ℝ) (hq : 18 ≤ q)
    (hqOverlap : q ≤ (Fintype.card B : ℝ))
    (HAB HBC HABC :
      CStarMatrix (ThreeReplicaABC A B C)
          (ThreeReplicaABC A B C) ℂ →CP
        CStarMatrix (ThreeReplicaABC A B C)
          (ThreeReplicaABC A B C) ℂ)
    (hAB : RelativeCPApproximation
      ((9 / (4 * q)) / (1 - 9 / (4 * q)))
      HAB.toLinearMap
      (finiteThreeMomentABReferenceCP A B C).toLinearMap)
    (hBC : RelativeCPApproximation
      ((9 / (4 * q)) / (1 - 9 / (4 * q)))
      HBC.toLinearMap
      (finiteThreeMomentBCReferenceCP A B C).toLinearMap)
    (hglobal : RelativeCPApproximation (9 / (2 * q))
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap
      HABC.toLinearMap) :
    RelativeCPApproximation (choKimFThree q)
      (CompletelyPositiveMap.comp
        (CompletelyPositiveMap.finiteChoiTensorId e HAB)
        (CompletelyPositiveMap.finiteChoiTensorId e HBC)).toLinearMap
      (CompletelyPositiveMap.finiteChoiTensorId e HABC).toLinearMap := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hcardB0 : 0 < (Fintype.card B : ℝ) := by positivity
  have hoverlap : 2 ≤ Fintype.card B := by
    have hqB : (18 : ℝ) ≤ Fintype.card B := hq.trans hqOverlap
    exact_mod_cast (show (2 : ℝ) ≤ Fintype.card B by linarith)
  have harg :
      9 / (2 * (Fintype.card B : ℝ)) ≤ 9 / (2 * q) := by
    rw [div_le_div_iff₀ (by positivity : 0 < 2 * (Fintype.card B : ℝ))
      (by positivity : 0 < 2 * q)]
    nlinarith
  have hreferenceError :
      Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1 ≤
        Real.exp (9 / (2 * q)) - 1 := by
    exact sub_le_sub_right (Real.exp_le_exp.mpr harg) 1
  have hreferenceBase :=
    (relativeCPApproximation_finiteThreeMomentReferenceComposition
      A B C hoverlap).mono_error hreferenceError
  have hABLift := relativeCPApproximation_finiteChoiTensorId e
    HAB (finiteThreeMomentABReferenceCP A B C)
    ((9 / (4 * q)) / (1 - 9 / (4 * q))) hAB
  have hBCLift := relativeCPApproximation_finiteChoiTensorId e
    HBC (finiteThreeMomentBCReferenceCP A B C)
    ((9 / (4 * q)) / (1 - 9 / (4 * q))) hBC
  have hglobalLift := relativeCPApproximation_finiteChoiTensorId e
    (finiteThreeMomentGlobalReferenceCP A B C) HABC
    (9 / (2 * q)) hglobal
  have hreferenceLift := relativeCPApproximation_finiteChoiTensorId e
    (CompletelyPositiveMap.comp
      (finiteThreeMomentABReferenceCP A B C)
      (finiteThreeMomentBCReferenceCP A B C))
    (finiteThreeMomentGlobalReferenceCP A B C)
    (Real.exp (9 / (2 * q)) - 1) hreferenceBase
  rw [← CompletelyPositiveMap.finiteChoiTensorId_comp_toLinearMap]
    at hreferenceLift
  exact relativeCPApproximation_pairwiseActualHaar_of_references q hq
    (CompletelyPositiveMap.finiteChoiTensorId e HAB)
    (CompletelyPositiveMap.finiteChoiTensorId e
      (finiteThreeMomentABReferenceCP A B C))
    (CompletelyPositiveMap.finiteChoiTensorId e HBC)
    (CompletelyPositiveMap.finiteChoiTensorId e
      (finiteThreeMomentBCReferenceCP A B C))
    (CompletelyPositiveMap.finiteChoiTensorId e
      (finiteThreeMomentGlobalReferenceCP A B C))
    (CompletelyPositiveMap.finiteChoiTensorId e HABC)
    hABLift hBCLift hreferenceLift hglobalLift

end

end TomographyOracleCore
