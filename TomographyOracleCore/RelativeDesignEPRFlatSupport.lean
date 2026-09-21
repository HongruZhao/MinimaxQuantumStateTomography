import TomographyOracleCore.RelativeDesignThreeMomentEPRGluing
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace TomographyOracleCore

noncomputable section

/-!
# Flat-support order bounds for an EPR/Choi comparison

This module isolates the operator-order step used in
Schuster--Haferkamp--Huang, Lemma 7.  A self-adjoint error supported on a
projection is bounded, on that support, by its operator norm times the
projection.  No channel or complete-positivity assertion is assumed here.
-/

/-- A self-adjoint element supported on a self-adjoint idempotent is trapped
between plus and minus its norm times that idempotent.  This is the abstract
C-star-algebra form of the flat-support estimate used for EPR/Choi states. -/
theorem selfAdjoint_supported_between_norm_smul_projection
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (X P : A)
    (hX : IsSelfAdjoint X)
    (hP : IsSelfAdjoint P)
    (hPid : P * P = P)
    (hsupport : P * X * P = X) :
    -(‖X‖ : ℝ) • P ≤ X ∧ X ≤ (‖X‖ : ℝ) • P := by
  constructor
  · have hbound := hP.conjugate_le_conjugate hX.neg_algebraMap_norm_le_self
    simpa [hsupport, Algebra.algebraMap_eq_smul_one, hPid] using hbound
  · have hbound := hP.conjugate_le_conjugate hX.le_algebraMap_norm_self
    simpa [hsupport, Algebra.algebraMap_eq_smul_one, hPid] using hbound

end

end TomographyOracleCore
