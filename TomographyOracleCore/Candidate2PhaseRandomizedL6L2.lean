import TomographyOracleCore.Candidate2PhaseRandomizedLaw

/-!
# L6--L2 transfer for the Candidate 2 quarter-phase law

This module packages the exact second- and sixth-marginal identities from
`Candidate2PhaseRandomizedLaw` into the real
`PeriodicForwardCovariance.HasL6L2Marginals` interface.  It contains only a
moment comparison; it neither states nor assumes a sample-covariance
concentration theorem.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace

namespace TomographyOracleCore.Candidate2PhaseRandomizedL6L2

noncomputable section

open Candidate2PhaseRandomizedLaw

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance : CompleteSpace E := FiniteDimensional.complete ℂ E
local instance : InnerProductSpace ℝ E :=
  InnerProductSpace.complexToReal

/-- Complex sixth-to-second marginal control before realification.  The
constant is written in the same norm-ratio convention as
`PeriodicForwardCovariance.HasL6L2Marginals`. -/
def HasComplexL6L2Marginals (mu : Measure E) (kappa : ℝ) : Prop :=
  ∀ u : E,
    ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu ≤
      kappa ^ 6 * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ^ 3

/-- The exact sixth-power constant produced by quarter-phase realification.
The real sixth marginal contributes a factor `1 / 2`, while the real second
marginal is `1 / 2` of the complex second marginal.  Consequently the
sixth-to-second coefficient is multiplied by exactly
`(1 / 2) / (1 / 2)^3 = 4`. -/
theorem integral_abs_real_inner_sixth_phaseRandomizedLaw_le_four_mul_second_cubed
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu2 : MemLp id 2 mu) (hmu6 : MemLp id 6 mu)
    {kappa : ℝ} (hL6 : HasComplexL6L2Marginals mu kappa) (u : E) :
    (∫ y, |⟪y, u⟫_ℝ| ^ 6 ∂phaseRandomizedLaw mu) ≤
      4 * kappa ^ 6 *
        (∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) ^ 3 := by
  have hsecond :
      (∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) =
        ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu := by
    calc
      (∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) =
          ∫ y, ⟪y, u⟫_ℝ ^ 2 ∂phaseRandomizedLaw mu := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact sq_abs _
      _ = ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu :=
        integral_real_inner_sq_phaseRandomizedLaw hmu2 u
  calc
    (∫ y, |⟪y, u⟫_ℝ| ^ 6 ∂phaseRandomizedLaw mu) ≤
        ((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂mu :=
      integral_abs_real_inner_sixth_phaseRandomizedLaw_le hmu6 u
    _ ≤ ((2 : ℝ)⁻¹) *
        (kappa ^ 6 * (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ^ 3) := by
      exact mul_le_mul_of_nonneg_left (hL6 u) (by norm_num)
    _ = 4 * kappa ^ 6 *
        (((2 : ℝ)⁻¹) * ∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂mu) ^ 3 := by
      ring
    _ = 4 * kappa ^ 6 *
        (∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) ^ 3 := by
      rw [hsecond]

/-- Package the exact factor-four transfer into the real `HasL6L2Marginals`
interface.  The scalar side condition makes the conversion between the
complex and real norm-ratio constants explicit. -/
theorem hasL6L2Marginals_phaseRandomizedLaw
    {mu : Measure E} [IsProbabilityMeasure mu]
    (hmu2 : MemLp id 2 mu) (hmu6 : MemLp id 6 mu)
    {kappaComplex kappaReal : ℝ}
    (hL6 : HasComplexL6L2Marginals mu kappaComplex)
    (hscale : 4 * kappaComplex ^ 6 ≤ kappaReal ^ 6) :
    PeriodicForwardCovariance.HasL6L2Marginals
      (phaseRandomizedLaw mu) kappaReal := by
  intro u
  have hsecond_nonneg :
      0 ≤ ∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu :=
    integral_nonneg fun y ↦ by positivity
  calc
    (∫ y, |⟪y, u⟫_ℝ| ^ 6 ∂phaseRandomizedLaw mu) ≤
        4 * kappaComplex ^ 6 *
          (∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) ^ 3 :=
      integral_abs_real_inner_sixth_phaseRandomizedLaw_le_four_mul_second_cubed
        hmu2 hmu6 hL6 u
    _ ≤ kappaReal ^ 6 *
        (∫ y, |⟪y, u⟫_ℝ| ^ 2 ∂phaseRandomizedLaw mu) ^ 3 := by
      exact mul_le_mul_of_nonneg_right hscale (pow_nonneg hsecond_nonneg 3)

end

end TomographyOracleCore.Candidate2PhaseRandomizedL6L2
