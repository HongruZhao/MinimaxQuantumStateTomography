import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceRelativeCP
import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaarGluing

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance globalHaarReferenceSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance globalHaarReferenceStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Concrete global approximate-Haar reference -/

/-- The raw Choi matrix used by the concrete global reference CP map is
definitionally the `Phi_a` Choi sum occurring in B.21--B.23. -/
theorem finiteThreeMomentGlobalReferenceRawChoi_eq_approximateHaarRawChoi
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] :
    finiteThreeMomentGlobalReferenceRawChoi A B C =
      finiteThreeMomentApproximateHaarRawChoi
        (Fintype.card A * Fintype.card B * Fintype.card C)
        (finiteThreeMomentB26ChoiQ A B C) := by
  rfl

/-- B.21 instantiated with the concrete global reference CP map.  The sole
remaining premise is the exact literal Haar Choi/Weingarten identity. -/
theorem relativeCPApproximation_globalHaar_of_weingartenChoi
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (hD : 18 ≤ Fintype.card A * Fintype.card B * Fintype.card C)
    (Haar : CStarMatrix (ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C) ℂ)
    (hHaarChoi : finiteChoiMatrix Haar.toLinearMap =
      finiteThreeMomentWeingartenRawChoi
        (Fintype.card A * Fintype.card B * Fintype.card C)
        (finiteThreeMomentB26ChoiQ A B C)) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card A * Fintype.card B *
        Fintype.card C : ℕ) : ℝ) - 9))
      Haar.toLinearMap
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap := by
  apply relativeCPApproximation_haar_of_weingartenChoi
    (Fintype.card A * Fintype.card B * Fintype.card C) hD
    (finiteThreeMomentB26ChoiQ A B C)
    (finiteThreeMomentB26ChoiQ_norm_le_one A B C)
    (finiteThreeMomentB26ChoiQ_mul A B C)
    (finiteThreeMomentB26ChoiQ_star A B C)
    Haar (finiteThreeMomentGlobalReferenceCP A B C) hHaarChoi
  rw [finiteThreeMomentGlobalReferenceCP_choi,
    finiteThreeMomentGlobalReferenceRawChoi_eq_approximateHaarRawChoi]

/-- B.22 instantiated with the concrete global reference CP map. -/
theorem relativeCPApproximation_globalReference_of_weingartenChoi
    (A B C : Type u) [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (hD : 18 ≤ Fintype.card A * Fintype.card B * Fintype.card C)
    (Haar : CStarMatrix (ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C)
        (ThreeReplicaABC A B C) ℂ)
    (hHaarChoi : finiteChoiMatrix Haar.toLinearMap =
      finiteThreeMomentWeingartenRawChoi
        (Fintype.card A * Fintype.card B * Fintype.card C)
        (finiteThreeMomentB26ChoiQ A B C)) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card A * Fintype.card B *
        Fintype.card C : ℕ) : ℝ) - 18))
      (finiteThreeMomentGlobalReferenceCP A B C).toLinearMap
      Haar.toLinearMap := by
  apply relativeCPApproximation_reference_of_weingartenChoi
    (Fintype.card A * Fintype.card B * Fintype.card C) hD
    (finiteThreeMomentB26ChoiQ A B C)
    (finiteThreeMomentB26ChoiQ_norm_le_one A B C)
    (finiteThreeMomentB26ChoiQ_mul A B C)
    (finiteThreeMomentB26ChoiQ_star A B C)
    Haar (finiteThreeMomentGlobalReferenceCP A B C) hHaarChoi
  rw [finiteThreeMomentGlobalReferenceCP_choi,
    finiteThreeMomentGlobalReferenceRawChoi_eq_approximateHaarRawChoi]

end

end TomographyOracleCore
