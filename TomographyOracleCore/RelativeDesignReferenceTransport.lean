import TomographyOracleCore.FiniteUnitaryThirdTwirlFactorCP
import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaarGluing

namespace TomographyOracleCore

universe u v

open scoped CStarAlgebra

noncomputable section

local instance referenceTransportSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance referenceTransportStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Basis transport for relative completely-positive estimates

Every connected-support reference in the Cho--Kim path is first proved in
factorized subsystem coordinates and then moved to the one fixed physical
matrix algebra.  This file proves that this coordinate change preserves the
entire relative-CP sandwich, including the scalar lower side.
-/

/-- Conjugating both CP maps by a finite basis equivalence preserves their
relative completely-positive comparison. -/
theorem relativeCPApproximation_reindexEquiv
    {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J)
    (E H : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (epsilon : ℝ)
    (h : RelativeCPApproximation epsilon E.toLinearMap H.toLinearMap) :
    RelativeCPApproximation epsilon
      (CompletelyPositiveMap.reindexEquiv e E).toLinearMap
      (CompletelyPositiveMap.reindexEquiv e H).toLinearMap := by
  constructor
  · obtain ⟨Delta, hDelta⟩ := h.lower
    refine ⟨CompletelyPositiveMap.reindexEquiv e Delta, ?_⟩
    apply LinearMap.ext
    intro X
    simp only [CompletelyPositiveMap.reindexEquiv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply]
    rw [LinearMap.congr_fun hDelta
      (CStarMatrix.reindexₐ ℂ ℂ e.symm X)]
    simp
  · obtain ⟨Delta, hDelta⟩ := h.upper
    refine ⟨CompletelyPositiveMap.reindexEquiv e Delta, ?_⟩
    apply LinearMap.ext
    intro X
    simp only [CompletelyPositiveMap.reindexEquiv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply]
    rw [LinearMap.congr_fun hDelta
      (CStarMatrix.reindexₐ ℂ ℂ e.symm X)]
    simp

/-- The concrete B.26/B.27 reference-composition theorem transported from
subsystem-major coordinates to any equivalent finite physical basis. -/
theorem relativeCPApproximation_finiteThreeMomentReferenceComposition_reindex
    (A B C : Type u) (I : Type v)
    [Fintype A] [Fintype B] [Fintype C] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq I]
    (e : ThreeReplicaABC A B C ≃ I)
    (hoverlap : 2 ≤ Fintype.card B) :
    RelativeCPApproximation
      (Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1)
      (CompletelyPositiveMap.comp
        (CompletelyPositiveMap.reindexEquiv e
          (finiteThreeMomentABReferenceCP A B C))
        (CompletelyPositiveMap.reindexEquiv e
          (finiteThreeMomentBCReferenceCP A B C))).toLinearMap
      (CompletelyPositiveMap.reindexEquiv e
        (finiteThreeMomentGlobalReferenceCP A B C)).toLinearMap := by
  have h := relativeCPApproximation_reindexEquiv e
    (CompletelyPositiveMap.comp
      (finiteThreeMomentABReferenceCP A B C)
      (finiteThreeMomentBCReferenceCP A B C))
    (finiteThreeMomentGlobalReferenceCP A B C)
    (Real.exp (9 / (2 * (Fintype.card B : ℝ))) - 1)
    (relativeCPApproximation_finiteThreeMomentReferenceComposition
      A B C hoverlap)
  rw [CompletelyPositiveMap.reindexEquiv_comp] at h
  exact h

end

end TomographyOracleCore
