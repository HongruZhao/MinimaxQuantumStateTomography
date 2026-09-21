import TomographyOracleCore.RelativeDesignTwoUnitaryGluing

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

/-!
# Elementary calculus for relative CP errors

These lemmas keep the final approximate-Haar-to-Haar comparison explicit.
In particular, a reference map is never silently identified with Haar.
-/

/-- Every completely positive map is a relative approximation to itself at
zero error. -/
theorem relativeCPApproximation_zero_refl
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (Phi : A →CP A) :
    RelativeCPApproximation 0 Phi.toLinearMap Phi.toLinearMap := by
  constructor <;>
    simpa using CompletelyPositiveLE.refl Phi.toLinearMap

/-- Enlarging the relative error preserves a relative-CP approximation. -/
theorem RelativeCPApproximation.mono_error
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {E H : A →CP A} {epsilon eta : ℝ}
    (h : RelativeCPApproximation epsilon E.toLinearMap H.toLinearMap)
    (hepsilonEta : epsilon ≤ eta) :
    RelativeCPApproximation eta E.toLinearMap H.toLinearMap := by
  constructor
  · exact (CompletelyPositiveLE.real_smul_mono
      H
      (by linarith)).trans h.lower
  · exact h.upper.trans (CompletelyPositiveLE.real_smul_mono
      H
      (by linarith))

/-- Transitivity of relative-CP approximation with the exact multiplicative
error.  The lower sandwich remains valid even when the first displayed error
is already at least one: in that branch its target lower coefficient is
nonpositive and follows directly from complete positivity of `E`. -/
theorem relativeCPApproximation_trans
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (E H G : A →CP A) (epsilon eta : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (heta0 : 0 ≤ eta)
    (hEH : RelativeCPApproximation epsilon E.toLinearMap H.toLinearMap)
    (hHG : RelativeCPApproximation eta H.toLinearMap G.toLinearMap) :
    RelativeCPApproximation
      ((1 + epsilon) * (1 + eta) - 1)
      E.toLinearMap G.toLinearMap := by
  constructor
  · by_cases hepsilon1 : epsilon ≤ 1
    · have hscaled := hHG.lower.real_smul
        (1 - epsilon) (sub_nonneg.mpr hepsilon1)
      have hproduct : CompletelyPositiveLE
          (((((1 - epsilon) * (1 - eta) : ℝ) : ℂ) • G.toLinearMap))
          E.toLinearMap := by
        have htrans := hscaled.trans hEH.lower
        simpa [smul_smul] using htrans
      apply (CompletelyPositiveLE.real_smul_mono G ?_).trans hproduct
      nlinarith [mul_nonneg hepsilon0 heta0]
    · have hfactor : 2 ≤ (1 + epsilon) * (1 + eta) := by
        have hmul : 0 ≤ (1 + epsilon) * eta :=
          mul_nonneg (by linarith) heta0
        nlinarith
      have hcoeff :
          1 - ((1 + epsilon) * (1 + eta) - 1) ≤ 0 := by
        linarith
      have hnegative := CompletelyPositiveLE.real_smul_mono G hcoeff
      have hzero : CompletelyPositiveLE
          ((((0 : ℝ) : ℂ) • G.toLinearMap)) E.toLinearMap := by
        refine ⟨E, ?_⟩
        simp
      exact hnegative.trans hzero
  · have hscaled := hHG.upper.real_smul
      (1 + epsilon) (by linarith)
    have htrans := hEH.upper.trans hscaled
    simpa [smul_smul] using htrans

end

end TomographyOracleCore
