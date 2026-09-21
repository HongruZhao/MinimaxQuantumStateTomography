import TomographyOracleCore.Candidate2EuclideanSphereFiniteNet
import TomographyOracleCore.Candidate2FixedNormPeakyUniform

/-!
# A complete finite-sample fixed-norm covariance event bound

This module composes the verified clipped-spread concentration, the explicit
Euclidean sphere net, and the deterministic fixed-norm peaky bound.  It first
records the exact unit-direction event and then uses finite-dimensional
Rayleigh attainment to obtain the operator-norm event.

The final confidence specialization is deliberately labeled a fallback.  Its
fixed choices `eta = lambda = 1` are simple and fully explicit, but do not
claim the sharp effective-rank minimax rate.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace Metric Set Module
open scoped ENNReal NNReal RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A symmetric operator on a nontrivial finite-dimensional real Hilbert
space attains its operator norm as the absolute Rayleigh quotient of a unit
vector. -/
theorem exists_unit_norm_eq_abs_rayleighQuotient
    [FiniteDimensional ℝ E] [Nontrivial E]
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) :
    ∃ u : E, ‖u‖ = 1 ∧ ‖A‖ = |A.rayleighQuotient u| := by
  let sphere : Set E := Metric.sphere (0 : E) 1
  have hsphereNonempty : sphere.Nonempty := by
    obtain ⟨x, hx⟩ := exists_ne (0 : E)
    refine ⟨‖x‖⁻¹ • x, ?_⟩
    rw [show sphere = Metric.sphere (0 : E) 1 by rfl,
      mem_sphere_zero_iff_norm, norm_smul, norm_inv,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
  have hcontinuous : Continuous (fun x : E => |A.reApplyInnerSelf x|) :=
    A.reApplyInnerSelf_continuous.abs
  obtain ⟨u, huSphere, huMax⟩ :=
    (isCompact_sphere (0 : E) 1).exists_isMaxOn
      hsphereNonempty hcontinuous.continuousOn
  have hu : ‖u‖ = 1 := by
    simpa only [sphere, mem_sphere_zero_iff_norm] using huSphere
  have hall (x : E) :
      |A.rayleighQuotient x| ≤ |A.rayleighQuotient u| := by
    by_cases hx : x = 0
    · simp [hx]
    let y : E := ‖x‖⁻¹ • x
    have hy : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x),
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hySphere : y ∈ sphere := by
      simpa only [sphere, mem_sphere_zero_iff_norm] using hy
    have hmax := huMax hySphere
    have hscale : A.rayleighQuotient y = A.rayleighQuotient x := by
      dsimp only [y]
      exact A.rayleigh_smul x
        (inv_ne_zero (norm_ne_zero_iff.mpr hx))
    rw [← hscale]
    simpa [ContinuousLinearMap.rayleighQuotient, hy, hu] using hmax
  refine ⟨u, hu, le_antisymm ?_ (A.rayleighQuotient_le_norm u)⟩
  rw [A.norm_eq_iSup_rayleighQuotient hA]
  exact ciSup_le hall

/-- Canonical-product event bound for the existence of a bad unit Rayleigh
direction.  The threshold is the deterministic fixed-norm peaky term plus the
uniform clipped-spread threshold. -/
theorem measure_pi_exists_unit_abs_covarianceError_rayleighQuotient_ge_le
    [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E]
    (populationLaw : Measure E) [IsProbabilityMeasure populationLaw]
    {T : ℕ} (hT : 0 < T)
    {eta q kappa lambda epsilon : ℝ}
    (heta : 0 < eta)
    (hnorm : ∀ᵐ x ∂populationLaw, ‖x‖ ^ 2 = q)
    (hL6 : HasL6L2Marginals populationLaw kappa)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon) :
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
      ∃ u : E, ‖u‖ = 1 ∧
        lambda ^ 2 * q ^ 3 + epsilon +
              lambda ^ 2 * kappa ^ 6 *
                ‖populationCovariance populationLaw‖ ^ 3 +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          |(sampleCovariance omega - populationCovariance populationLaw).rayleighQuotient u|} ≤
      (1 + 2 / eta) ^ finrank ℝ E *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  let sampleLaw : Measure (Fin T → E) :=
    Measure.pi fun _ : Fin T => populationLaw
  let badRayleigh : Set (Fin T → E) := {omega |
    ∃ u : E, ‖u‖ = 1 ∧
      lambda ^ 2 * q ^ 3 + epsilon +
            lambda ^ 2 * kappa ^ 6 *
              ‖populationCovariance populationLaw‖ ^ 3 +
          2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
        |(sampleCovariance omega - populationCovariance populationLaw).rayleighQuotient u|}
  let restrictedBad : Set (Fin T → E) := {omega |
    (∀ i, ‖omega i‖ ^ 2 ≤ q) ∧ omega ∈ badRayleigh}
  let badSpread : Set (Fin T → E) := {omega |
    ∃ u : E, ‖u‖ = 1 ∧
      epsilon +
            lambda ^ 2 * kappa ^ 6 *
              ‖populationCovariance populationLaw‖ ^ 3 +
          2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
        |centeredDirectionalSpread populationLaw lambda omega u|}
  have hnormCoordinate : ∀ i, ∀ᵐ omega ∂sampleLaw,
      ‖omega i‖ ^ 2 ≤ q := by
    intro i
    have hi : ∀ᵐ omega ∂sampleLaw, ‖omega i‖ ^ 2 = q := by
      exact (measurePreserving_eval
        (fun _ : Fin T => populationLaw) i).quasiMeasurePreserving.ae hnorm
    exact hi.mono fun _omega homega => homega.le
  have hnormAll : ∀ᵐ omega ∂sampleLaw,
      ∀ i, ‖omega i‖ ^ 2 ≤ q :=
    Filter.eventually_all.mpr hnormCoordinate
  have hrestricted : badRayleigh =ᵐ[sampleLaw] restrictedBad := by
    filter_upwards [hnormAll] with omega homega
    change (omega ∈ badRayleigh) = ((∀ i, ‖omega i‖ ^ 2 ≤ q) ∧
      omega ∈ badRayleigh)
    apply propext
    exact ⟨fun h => ⟨homega, h⟩, fun h => h.2⟩
  have hsubset : restrictedBad ⊆ badSpread := by
    intro omega homega
    rcases homega with ⟨homegaNorm, u, hu, hlarge⟩
    have hpeaky :=
      abs_covarianceError_rayleighQuotient_le_fixedNormPeaky_add_spread
        (fixedNorm_memLp hnorm 2) hT omega hlambda homegaNorm u hu
    have hpeaky' :
        |(sampleCovariance omega - populationCovariance populationLaw).rayleighQuotient u| ≤
          lambda ^ 2 * q ^ 3 +
            |centeredDirectionalSpread populationLaw lambda omega u| := by
      simpa only [centeredDirectionalSpread] using hpeaky
    exact ⟨u, hu, by linarith⟩
  change sampleLaw.real badRayleigh ≤ _
  rw [measureReal_congr hrestricted]
  calc
    sampleLaw.real restrictedBad ≤ sampleLaw.real badSpread :=
      measureReal_mono hsubset
    _ ≤ (1 + 2 / eta) ^ finrank ℝ E *
        (2 * Real.exp
          (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
      dsimp only [sampleLaw, badSpread]
      exact measure_pi_unitSphere_centeredDirectionalSpread_ge_le_of_fixedNorm
        populationLaw hT heta hnorm hL6 hlambda hepsilon

/-- Complete operator-norm event bound.  Nontriviality is needed only to make
the unit sphere nonempty for exact Rayleigh attainment. -/
theorem measure_pi_norm_covarianceError_ge_le
    [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (populationLaw : Measure E) [IsProbabilityMeasure populationLaw]
    {T : ℕ} (hT : 0 < T)
    {eta q kappa lambda epsilon : ℝ}
    (heta : 0 < eta)
    (hnorm : ∀ᵐ x ∂populationLaw, ‖x‖ ^ 2 = q)
    (hL6 : HasL6L2Marginals populationLaw kappa)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon) :
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
      lambda ^ 2 * q ^ 3 + epsilon +
            lambda ^ 2 * kappa ^ 6 *
              ‖populationCovariance populationLaw‖ ^ 3 +
          2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
        ‖sampleCovariance omega - populationCovariance populationLaw‖} ≤
      (1 + 2 / eta) ^ finrank ℝ E *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  let badRayleigh : Set (Fin T → E) := {omega |
    ∃ u : E, ‖u‖ = 1 ∧
      lambda ^ 2 * q ^ 3 + epsilon +
            lambda ^ 2 * kappa ^ 6 *
              ‖populationCovariance populationLaw‖ ^ 3 +
          2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
        |(sampleCovariance omega - populationCovariance populationLaw).rayleighQuotient u|}
  have hsubset :
      {omega : Fin T → E |
        lambda ^ 2 * q ^ 3 + epsilon +
              lambda ^ 2 * kappa ^ 6 *
                ‖populationCovariance populationLaw‖ ^ 3 +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          ‖sampleCovariance omega - populationCovariance populationLaw‖} ⊆
        badRayleigh := by
    intro omega homega
    have hsymm :
        (sampleCovariance omega - populationCovariance populationLaw).toLinearMap.IsSymmetric :=
      (sampleCovariance_isSymmetric omega).sub
        (populationCovariance_isSymmetric populationLaw)
    obtain ⟨u, hu, hattain⟩ :=
      exists_unit_norm_eq_abs_rayleighQuotient
        (sampleCovariance omega - populationCovariance populationLaw) hsymm
    exact ⟨u, hu, by rwa [← hattain]⟩
  calc
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
        lambda ^ 2 * q ^ 3 + epsilon +
              lambda ^ 2 * kappa ^ 6 *
                ‖populationCovariance populationLaw‖ ^ 3 +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          ‖sampleCovariance omega - populationCovariance populationLaw‖} ≤
        (Measure.pi fun _ : Fin T => populationLaw).real badRayleigh :=
      measureReal_mono hsubset
    _ ≤ (1 + 2 / eta) ^ finrank ℝ E *
        (2 * Real.exp
          (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
      dsimp only [badRayleigh]
      exact measure_pi_exists_unit_abs_covarianceError_rayleighQuotient_ge_le
        populationLaw hT heta hnorm hL6 hlambda hepsilon

/-- Confidence calibration used by the elementary fallback specialization.
It is the exact value that cancels the factor `2 * 3^D` when
`eta = lambda = 1`. -/
def fallbackCovarianceEpsilon (T D : ℕ) (delta : ℝ) : ℝ :=
  Real.sqrt
    (Real.log ((2 * (3 : ℝ) ^ D) / delta) / (2 * (T : ℝ)))

/-- Exact scalar confidence calculation behind the fallback theorem. -/
theorem fallbackCovariance_tail_le
    {T D : ℕ} (hT : 0 < T) {delta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (3 : ℝ) ^ D *
        (2 * Real.exp
          (-2 * (T : ℝ) * fallbackCovarianceEpsilon T D delta ^ 2)) ≤
      delta := by
  let M : ℝ := 2 * (3 : ℝ) ^ D
  have hpow : 1 ≤ (3 : ℝ) ^ D := one_le_pow₀ (by norm_num)
  have hMpos : 0 < M := by dsimp only [M]; positivity
  have hMone : 1 ≤ M := by dsimp only [M]; nlinarith
  have hratioOne : 1 ≤ M / delta := by
    exact (le_div_iff₀ hdelta).2 (by
      simpa only [one_mul] using hdeltaOne.trans hMone)
  have hratioPos : 0 < M / delta := lt_of_lt_of_le zero_lt_one hratioOne
  have hlog : 0 ≤ Real.log (M / delta) := Real.log_nonneg hratioOne
  have hdenom : 0 < 2 * (T : ℝ) := by positivity
  have hepsilonSq : fallbackCovarianceEpsilon T D delta ^ 2 =
      Real.log (M / delta) / (2 * (T : ℝ)) := by
    rw [fallbackCovarianceEpsilon, Real.sq_sqrt]
    simpa only [M] using div_nonneg hlog hdenom.le
  have hexponent :
      -2 * (T : ℝ) * fallbackCovarianceEpsilon T D delta ^ 2 =
        -Real.log (M / delta) := by
    rw [hepsilonSq]
    field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne']
  calc
    (3 : ℝ) ^ D *
        (2 * Real.exp
          (-2 * (T : ℝ) * fallbackCovarianceEpsilon T D delta ^ 2)) =
        M * Real.exp (-Real.log (M / delta)) := by
      rw [hexponent]
      dsimp only [M]
      ring
    _ = M * (M / delta)⁻¹ := by
      rw [Real.exp_neg, Real.exp_log hratioPos]
    _ = delta := by
      field_simp [hMpos.ne', hdelta.ne']
    _ ≤ delta := le_rfl

/-- **Elementary fallback specialization.**  Taking `eta = lambda = 1`
and calibrating `epsilon` explicitly gives confidence `delta`.

This theorem is useful as a completely explicit sanity-check endpoint.  Its
nonvanishing deterministic terms (`q^3`, the `L6` bias, and the unit-radius
Lipschitz penalty) mean that it is not the sharp effective-rank minimax rate.
-/
theorem measure_pi_norm_covarianceError_ge_le_fallback
    [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (populationLaw : Measure E) [IsProbabilityMeasure populationLaw]
    {T : ℕ} (hT : 0 < T) {q kappa delta : ℝ}
    (hnorm : ∀ᵐ x ∂populationLaw, ‖x‖ ^ 2 = q)
    (hL6 : HasL6L2Marginals populationLaw kappa)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1) :
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
      q ^ 3 + fallbackCovarianceEpsilon T (finrank ℝ E) delta +
            kappa ^ 6 * ‖populationCovariance populationLaw‖ ^ 3 +
          2 * (q + ‖populationCovariance populationLaw‖) ≤
        ‖sampleCovariance omega - populationCovariance populationLaw‖} ≤
      delta := by
  let epsilon := fallbackCovarianceEpsilon T (finrank ℝ E) delta
  have hmain := measure_pi_norm_covarianceError_ge_le
    populationLaw hT (eta := (1 : ℝ)) (lambda := (1 : ℝ))
      (epsilon := epsilon) (by norm_num) hnorm hL6 (by norm_num)
      (by dsimp only [epsilon, fallbackCovarianceEpsilon]; positivity)
  norm_num at hmain
  calc
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
        q ^ 3 + fallbackCovarianceEpsilon T (finrank ℝ E) delta +
              kappa ^ 6 * ‖populationCovariance populationLaw‖ ^ 3 +
            2 * (q + ‖populationCovariance populationLaw‖) ≤
          ‖sampleCovariance omega - populationCovariance populationLaw‖} ≤
        (3 : ℝ) ^ finrank ℝ E *
          (2 * Real.exp
            (-2 * (T : ℝ) *
              fallbackCovarianceEpsilon T (finrank ℝ E) delta ^ 2)) := by
      simpa only [epsilon, neg_mul] using hmain
    _ ≤ delta := fallbackCovariance_tail_le hT hdelta hdeltaOne

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
