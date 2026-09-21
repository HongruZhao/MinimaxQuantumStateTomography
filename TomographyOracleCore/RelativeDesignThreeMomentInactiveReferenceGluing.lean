import TomographyOracleCore.RelativeDesignChoiTensorIdOrder
import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaarGluing

namespace TomographyOracleCore

universe u


open scoped CStarAlgebra

noncomputable section

local instance inactiveReferenceTransportSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance inactiveReferenceTransportStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# B.26/B.27 with a common inactive register

The inactive register is handled by the audited Choi/EPR order transport.
Thus this module consumes the already proved base B.27 theorem directly: no
duplicate Gram estimate or flat-support argument remains.
-/

def finiteThreeMomentABReferenceInactiveCP
    (A B C T I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype T] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty T]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq T] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × T) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  CompletelyPositiveMap.finiteChoiTensorId e
    (finiteThreeMomentABReferenceCP A B C)

def finiteThreeMomentBCReferenceInactiveCP
    (A B C T I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype T] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty T]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq T] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × T) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  CompletelyPositiveMap.finiteChoiTensorId e
    (finiteThreeMomentBCReferenceCP A B C)

def finiteThreeMomentGlobalReferenceInactiveCP
    (A B C T I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype T] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty T]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq T] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × T) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  CompletelyPositiveMap.finiteChoiTensorId e
    (finiteThreeMomentGlobalReferenceCP A B C)

/-- B.26/B.27 with an arbitrary common inactive identity factor. -/
theorem relativeCPApproximation_finiteThreeMomentReferenceComposition_inactive
    (A B C T I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype T] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty T]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq T] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × T)
    (hoverlap : 2 ≤ Fintype.card B) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1)
      (CompletelyPositiveMap.comp
        (finiteThreeMomentABReferenceInactiveCP A B C T I e)
        (finiteThreeMomentBCReferenceInactiveCP A B C T I e)).toLinearMap
      (finiteThreeMomentGlobalReferenceInactiveCP
        A B C T I e).toLinearMap := by
  have h := relativeCPApproximation_finiteChoiTensorId e
    (CompletelyPositiveMap.comp
      (finiteThreeMomentABReferenceCP A B C)
      (finiteThreeMomentBCReferenceCP A B C))
    (finiteThreeMomentGlobalReferenceCP A B C)
    (Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1)
    (relativeCPApproximation_finiteThreeMomentReferenceComposition
      A B C hoverlap)
  rw [← CompletelyPositiveMap.finiteChoiTensorId_comp_toLinearMap] at h
  simpa [finiteThreeMomentABReferenceInactiveCP,
    finiteThreeMomentBCReferenceInactiveCP,
    finiteThreeMomentGlobalReferenceInactiveCP] using h

/-- One-replica form used by the circuit geometry.  The inactive Choi index
is explicitly `ThreeReplica R`. -/
theorem relativeCPApproximation_finiteThreeMomentReferenceComposition_inactiveReplica
    (A B C R I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq R] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × ThreeReplica R)
    (hoverlap : 2 ≤ Fintype.card B) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1)
      (CompletelyPositiveMap.comp
        (finiteThreeMomentABReferenceInactiveCP
          A B C (ThreeReplica R) I e)
        (finiteThreeMomentBCReferenceInactiveCP
          A B C (ThreeReplica R) I e)).toLinearMap
      (finiteThreeMomentGlobalReferenceInactiveCP
        A B C (ThreeReplica R) I e).toLinearMap := by
  exact relativeCPApproximation_finiteThreeMomentReferenceComposition_inactive
    A B C (ThreeReplica R) I e hoverlap

end

end TomographyOracleCore
