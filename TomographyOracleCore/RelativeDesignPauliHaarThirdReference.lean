import TomographyOracleCore.RelativeDesignHaarThirdTwirlChoiWeingarten
import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceRelativeCP

namespace TomographyOracleCore

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance pauliHaarReferenceSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance pauliHaarReferenceStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Unconditional k=3 Haar/reference comparison on a qubit block -/

def pauliApproximateHaarThirdReferenceRawChoi (K : ℕ) :
    CStarMatrix
      (TripleIndex (PauliBinaryWord K) × TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K) × TripleIndex (PauliBinaryWord K)) ℂ :=
  finiteThreeMomentApproximateHaarRawChoi (2 ^ K)
    (haarThirdTwirlPermutationQ (PauliBinaryWord K))

theorem pauliApproximateHaarThirdReferenceRawChoi_nonneg (K : ℕ) :
    0 ≤ pauliApproximateHaarThirdReferenceRawChoi K := by
  rw [pauliApproximateHaarThirdReferenceRawChoi,
    finiteThreeMomentApproximateHaarRawChoi_eq_flat]
  rw [Complex.coe_smul]
  apply cstarMatrix_real_smul_nonneg (by positivity)
  let P := finiteThreeMomentReferenceProjection
    (haarThirdTwirlPermutationQ (PauliBinaryWord K))
  have hself : IsSelfAdjoint P :=
    finiteThreeMomentReferenceProjection_isSelfAdjoint _
      (haarThirdTwirlPermutationQ_star (PauliBinaryWord K))
  have hid : P * P = P :=
    finiteThreeMomentReferenceProjection_isIdempotent _
      (haarThirdTwirlPermutationQ_mul (PauliBinaryWord K))
  calc
    0 ≤ star P * P := star_mul_self_nonneg P
    _ = P * P := by rw [hself.star_eq]
    _ = P := hid

/-- The concrete approximate-Haar reference CP map on a `K`-qubit block. -/
def pauliApproximateHaarThirdReferenceCP (K : ℕ) :=
  finiteCPMapOfNonnegativeChoi
    (pauliApproximateHaarThirdReferenceRawChoi K)
    (pauliApproximateHaarThirdReferenceRawChoi_nonneg K)

@[simp] theorem pauliApproximateHaarThirdReferenceCP_choi (K : ℕ) :
    finiteChoiMatrix (pauliApproximateHaarThirdReferenceCP K).toLinearMap =
      finiteThreeMomentApproximateHaarRawChoi (2 ^ K)
        (haarThirdTwirlPermutationQ (PauliBinaryWord K)) := by
  rw [pauliApproximateHaarThirdReferenceCP,
    finiteChoiMatrix_finiteCPMapOfNonnegativeChoi]
  rfl

/-- Literal B.21 for the exact qubit Haar third twirl, with no external
analytic premise. -/
theorem relativeCPApproximation_pauliHaarThirdTwirl_reference
    (K : ℕ) (hD : 18 ≤ 2 ^ K) :
    RelativeCPApproximation (9 / (2 * ((2 ^ K : ℕ) : ℝ) - 9))
      (pauliHaarThirdTwirlCP K).toLinearMap
      (pauliApproximateHaarThirdReferenceCP K).toLinearMap := by
  apply relativeCPApproximation_haar_of_weingartenChoi
    (2 ^ K) hD (haarThirdTwirlPermutationQ (PauliBinaryWord K))
    (haarThirdTwirlPermutationQ_norm_le_one (PauliBinaryWord K))
    (haarThirdTwirlPermutationQ_mul (PauliBinaryWord K))
    (haarThirdTwirlPermutationQ_star (PauliBinaryWord K))
    (pauliHaarThirdTwirlCP K) (pauliApproximateHaarThirdReferenceCP K)
  · exact finiteChoiMatrix_pauliHaarThirdTwirlCP_eq_weingarten K (by omega)
  · exact pauliApproximateHaarThirdReferenceCP_choi K

/-- Literal B.22 in the reference-to-Haar orientation. -/
theorem relativeCPApproximation_pauliReference_haarThirdTwirl
    (K : ℕ) (hD : 18 ≤ 2 ^ K) :
    RelativeCPApproximation (9 / (2 * ((2 ^ K : ℕ) : ℝ) - 18))
      (pauliApproximateHaarThirdReferenceCP K).toLinearMap
      (pauliHaarThirdTwirlCP K).toLinearMap := by
  apply relativeCPApproximation_reference_of_weingartenChoi
    (2 ^ K) hD (haarThirdTwirlPermutationQ (PauliBinaryWord K))
    (haarThirdTwirlPermutationQ_norm_le_one (PauliBinaryWord K))
    (haarThirdTwirlPermutationQ_mul (PauliBinaryWord K))
    (haarThirdTwirlPermutationQ_star (PauliBinaryWord K))
    (pauliHaarThirdTwirlCP K) (pauliApproximateHaarThirdReferenceCP K)
  · exact finiteChoiMatrix_pauliHaarThirdTwirlCP_eq_weingarten K (by omega)
  · exact pauliApproximateHaarThirdReferenceCP_choi K

end

end TomographyOracleCore
