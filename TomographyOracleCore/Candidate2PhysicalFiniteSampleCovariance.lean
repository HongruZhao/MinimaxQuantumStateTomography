import TomographyOracleCore.Candidate2FixedNormCovarianceFiniteSample
import TomographyOracleCore.Candidate2FiniteBornVectorLaw

/-!
# Physical Born-law specialization of the finite-sample covariance bound

This module substitutes the literal phase-randomized Born vector law into the
verified fixed-norm covariance theorem.  The only scientific premise left in
the generic and periodic endpoints is the displayed complex `L6--L2`
marginal estimate; no sample-covariance theorem is assumed.

The resulting bound is the explicit finite-net fallback, not yet the sharp
effective-rank minimax covariance rate.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Module
open scoped ENNReal RealInnerProductSpace

namespace TomographyOracleCore.Candidate2PhysicalFiniteSampleCovariance

noncomputable section

open Candidate2FiniteBornVectorLaw
open Candidate2PhaseRandomizedL6L2
open MatrixReduction
open PeriodicForwardCovariance
open PeriodicForwardCovariance.PeakySpread

local instance {D : ℕ} :
    InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

/-- Finite-dimensional real rank of a complex Euclidean coordinate space. -/
theorem finrank_real_complexEuclideanSpace (D : ℕ) :
    finrank ℝ (EuclideanSpace ℂ (Fin D)) = 2 * D := by
  rw [finrank_real_of_complex]
  simp

/-- Complete finite-sample covariance tail for a literal finite-unitary Born
experiment, conditional only on its displayed complex `L6--L2` marginal
bound. -/
theorem measure_pi_norm_covarianceError_finiteUnitaryBorn_ge_le
    {D : ℕ} (hD : 0 < D)
    {A : Type*} [Fintype A] [Nonempty A]
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    {T : ℕ} (hT : 0 < T)
    {eta kappaComplex kappaReal lambda epsilon : ℝ}
    (heta : 0 < eta)
    (hL6 : HasComplexL6L2Marginals
      (finiteUnitaryBornVectorLaw U rho) kappaComplex)
    (hscale : 4 * kappaComplex ^ 6 ≤ kappaReal ^ 6)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon) :
    let mu := finiteUnitaryPhaseRandomizedBornVectorLaw U rho
    (Measure.pi fun _ : Fin T => mu).real {omega |
      lambda ^ 2 * ((D : ℝ) + 1) ^ 3 + epsilon +
            lambda ^ 2 * kappaReal ^ 6 *
              ‖populationCovariance mu‖ ^ 3 +
          2 * (((D : ℝ) + 1) + ‖populationCovariance mu‖) * eta ≤
        ‖sampleCovariance omega - populationCovariance mu‖} ≤
      (1 + 2 / eta) ^ (2 * D) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let mu := finiteUnitaryPhaseRandomizedBornVectorLaw U rho
  letI : IsProbabilityMeasure mu :=
    finiteUnitaryPhaseRandomizedBornVectorLaw_isProbability hD U rho
  have hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = (D : ℝ) + 1 := by
    dsimp only [mu]
    exact ae_fixedNorm_finiteUnitaryPhaseRandomizedBornVectorLaw hD U rho
  have hrealL6 : HasL6L2Marginals mu kappaReal := by
    dsimp only [mu]
    exact hasL6L2Marginals_finiteUnitaryPhaseRandomizedBornVectorLaw
      hD U rho hL6 hscale
  have hmain := measure_pi_norm_covarianceError_ge_le
    mu hT heta hfixed hrealL6 hlambda hepsilon
  simpa only [finrank_real_complexEuclideanSpace] using hmain

/-- Literal periodic shallow Cho--Kim specialization of the same complete
finite-sample fallback.  The complex `L6--L2` premise is precisely the
remaining physical fourth-moment-to-sixth-marginal specialization. -/
theorem measure_pi_norm_covarianceError_choKimPeriodicBorn_ge_le
    {n K : ℕ} (hdiv : K ∣ n)
    (rho : DensityOperator (Fin (2 ^ n)))
    {T : ℕ} (hT : 0 < T)
    {eta kappaComplex kappaReal lambda epsilon : ℝ}
    (heta : 0 < eta)
    (hL6 : HasComplexL6L2Marginals
      (choKimPeriodicBornVectorLaw hdiv rho) kappaComplex)
    (hscale : 4 * kappaComplex ^ 6 ≤ kappaReal ^ 6)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon) :
    let mu := choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho
    (Measure.pi fun _ : Fin T => mu).real {omega |
      lambda ^ 2 * (((2 ^ n : ℕ) : ℝ) + 1) ^ 3 + epsilon +
            lambda ^ 2 * kappaReal ^ 6 *
              ‖populationCovariance mu‖ ^ 3 +
          2 * ((((2 ^ n : ℕ) : ℝ) + 1) +
            ‖populationCovariance mu‖) * eta ≤
        ‖sampleCovariance omega - populationCovariance mu‖} ≤
      (1 + 2 / eta) ^ (2 * (2 ^ n)) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  let mu := choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho
  letI : IsProbabilityMeasure mu :=
    choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability hdiv rho
  have hfixed : ∀ᵐ x ∂mu,
      ‖x‖ ^ 2 = ((2 ^ n : ℕ) : ℝ) + 1 := by
    dsimp only [mu]
    exact ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho
  have hrealL6 : HasL6L2Marginals mu kappaReal := by
    dsimp only [mu]
    exact hasL6L2Marginals_choKimPeriodicPhaseRandomizedBornVectorLaw
      hdiv rho hL6 hscale
  have hmain := measure_pi_norm_covarianceError_ge_le
    mu hT heta hfixed hrealL6 hlambda hepsilon
  simpa only [finrank_real_complexEuclideanSpace] using hmain

end

end TomographyOracleCore.Candidate2PhysicalFiniteSampleCovariance
