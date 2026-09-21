import TomographyOracleCore.PeriodicForwardCovarianceBaiYinReduction
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps

/-!
# Fixed-norm covariance plumbing for Candidate 2

This file closes the elementary measure-theoretic and finite-dimensional
linear-algebra steps that precede a dimension-free Bai--Yin covariance bound.
It intentionally does not state or assume that missing probability theorem.

The missing theorem is the genuinely probabilistic step: under fixed norm,
mean-zero and uniform sixth-to-second marginal moment control, bound the
expected operator norm of `sampleCovariance X - populationCovariance mu` at
the effective-rank scale.  Nothing below derives an expectation or tail bound
for that random operator.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace ENNReal

namespace TomographyOracleCore.PeriodicForwardCovariance

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

omit [InnerProductSpace ℝ E] in
/-- A finite measure supported on a sphere has moments of every exponent. -/
theorem fixedNorm_memLp
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {mu : Measure E} [IsFiniteMeasure mu]
    {q : ℝ} (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (p : ℝ≥0∞) :
    MemLp id p mu := by
  apply MemLp.of_bound aestronglyMeasurable_id (q + 1)
  filter_upwards [hnorm] with x hx
  change ‖x‖ ≤ q + 1
  have hq : 0 ≤ q := hx ▸ sq_nonneg ‖x‖
  nlinarith [sq_nonneg (‖x‖ - 1)]

section ProductSample

variable {T : ℕ} [MeasurableSpace E] [BorelSpace E]
variable (mu : Measure E) [IsProbabilityMeasure mu]

/-- The `i`th coordinate of the canonical finite product sample. -/
def productCoordinate (i : Fin T) : (Fin T → E) → E := fun omega ↦ omega i

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] in
theorem measurable_productCoordinate (i : Fin T) :
    Measurable (productCoordinate (E := E) i) := by
  exact measurable_pi_apply i

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] in
/-- The canonical coordinate sample under `mu^T` is independent. -/
theorem iIndepFun_productCoordinate :
    iIndepFun (fun i ↦ productCoordinate (E := E) i)
      (Measure.pi fun _ : Fin T ↦ mu) := by
  change iIndepFun (fun i omega ↦ omega i) (Measure.pi fun _ : Fin T ↦ mu)
  exact iIndepFun_pi (μ := fun _ : Fin T ↦ mu) (X := fun _ ↦ id)
    (fun _ ↦ aemeasurable_id)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] in
/-- Every canonical product coordinate has exactly the prescribed marginal. -/
theorem map_productCoordinate_eq (i : Fin T) :
    (Measure.pi fun _ : Fin T ↦ mu).map (productCoordinate (E := E) i) = mu := by
  change (Measure.pi fun _ : Fin T ↦ mu).map (Function.eval i) = mu
  exact (measurePreserving_eval (fun _ : Fin T ↦ mu) i).map_eq

end ProductSample

/-- The rank-one covariance lift depends continuously on its vector. -/
theorem continuous_rankOneCovariance :
    Continuous (rankOneCovariance (E := E)) := by
  have hdual : Continuous fun x : E ↦ InnerProductSpace.toDualMap ℝ E x :=
    (InnerProductSpace.toDualMap ℝ E).continuous
  have hpair : Continuous fun x : E ↦
      ContinuousLinearMap.smulRight (InnerProductSpace.toDualMap ℝ E x) x :=
    (isBoundedBilinearMap_smulRight.continuous).comp
      (hdual.prodMk continuous_id)
  convert hpair using 1
  funext x
  rw [rankOneCovariance, InnerProductSpace.rankOne_def]
  rfl

theorem measurable_rankOneCovariance [MeasurableSpace E] [BorelSpace E] :
    Measurable (rankOneCovariance (E := E)) :=
  continuous_rankOneCovariance.measurable

/-- The empirical covariance is a measurable function of a finite sample. -/
theorem measurable_sampleCovariance
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {T : ℕ} :
    Measurable (sampleCovariance (E := E) (T := T)) := by
  apply Continuous.measurable
  change Continuous fun X : Fin T → E ↦
    ((T : ℝ)⁻¹) • ∑ i, rankOneCovariance (X i)
  exact (continuous_finsetSum _ fun i _ ↦
    continuous_rankOneCovariance.comp (continuous_apply i)).const_smul ((T : ℝ)⁻¹)

section Scalarization

variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- The population quadratic form is exactly the second moment of the real
marginal.  This fixes the inner-product orientation used by the empirical
covariance process. -/
theorem inner_populationCovariance_apply_self_eq_integral_sq
    {mu : Measure E} (hmu : MemLp id 2 mu) (u : E) :
    ⟪populationCovariance mu u, u⟫_ℝ =
      ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu := by
  rw [populationCovariance_inner hmu]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_comm u x, pow_two]

/-- Exact scalar empirical-process representation of the sample-covariance
error in a fixed direction. -/
theorem inner_sampleCovariance_sub_population_apply_self
    {mu : Measure E} (hmu : MemLp id 2 mu)
    {T : ℕ} (X : Fin T → E) (u : E) :
    ⟪(sampleCovariance X - populationCovariance mu) u, u⟫_ℝ =
      ((T : ℝ)⁻¹) * ∑ i, ⟪X i, u⟫_ℝ ^ 2 -
        ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu := by
  rw [sub_apply, inner_sub_left, inner_sampleCovariance_apply_self,
    inner_populationCovariance_apply_self_eq_integral_sq hmu]

/-- A directional second moment is controlled by the population covariance
operator norm.  This is the duality normalization used in the L6--L2 route. -/
theorem integral_sq_inner_le_populationCovariance_norm_mul_sq
    {mu : Measure E} (hmu : MemLp id 2 mu) (u : E) :
    (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ≤
      ‖populationCovariance mu‖ * ‖u‖ ^ 2 := by
  calc
    (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) =
        ⟪populationCovariance mu u, u⟫_ℝ :=
      (inner_populationCovariance_apply_self_eq_integral_sq hmu u).symm
    _ ≤ |⟪populationCovariance mu u, u⟫_ℝ| := le_abs_self _
    _ ≤ ‖populationCovariance mu u‖ * ‖u‖ :=
      abs_real_inner_le_norm _ _
    _ ≤ (‖populationCovariance mu‖ * ‖u‖) * ‖u‖ := by
      exact mul_le_mul_of_nonneg_right
        ((populationCovariance mu).le_opNorm u) (norm_nonneg u)
    _ = ‖populationCovariance mu‖ * ‖u‖ ^ 2 := by ring

/-- Unit-direction specialization of the population covariance duality
bound. -/
theorem integral_sq_inner_le_populationCovariance_norm_of_norm_eq_one
    {mu : Measure E} (hmu : MemLp id 2 mu) (u : E) (hu : ‖u‖ = 1) :
    (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu) ≤ ‖populationCovariance mu‖ := by
  simpa [hu] using
    integral_sq_inner_le_populationCovariance_norm_mul_sq hmu u

/-- The L6--L2 marginal hypothesis yields a sixth-moment bound normalized by
the population covariance operator norm.  This is an elementary moment input,
not a sample-covariance concentration theorem. -/
theorem sixthMoment_le_populationCovariance_norm_mul_sq
    {mu : Measure E} (hmu : MemLp id 2 mu) {kappa : ℝ}
    (hL6 : HasL6L2Marginals mu kappa) (u : E) :
    (∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu) ≤
      kappa ^ 6 * (‖populationCovariance mu‖ * ‖u‖ ^ 2) ^ 3 := by
  have hsecond_nonneg :
      0 ≤ ∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂mu :=
    integral_nonneg fun x ↦ sq_nonneg |⟪x, u⟫_ℝ|
  have hsecond_le :
      (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂mu) ≤
        ‖populationCovariance mu‖ * ‖u‖ ^ 2 := by
    calc
      (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂mu) =
          ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact sq_abs _
      _ ≤ ‖populationCovariance mu‖ * ‖u‖ ^ 2 :=
        integral_sq_inner_le_populationCovariance_norm_mul_sq hmu u
  calc
    (∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu) ≤
        kappa ^ 6 * (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂mu) ^ 3 := hL6 u
    _ ≤ kappa ^ 6 * (‖populationCovariance mu‖ * ‖u‖ ^ 2) ^ 3 := by
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hsecond_nonneg hsecond_le 3) (by positivity)

/-- Unit-direction specialization of the operator-normalized sixth-moment
bound. -/
theorem sixthMoment_le_populationCovariance_norm_of_norm_eq_one
    {mu : Measure E} (hmu : MemLp id 2 mu) {kappa : ℝ}
    (hL6 : HasL6L2Marginals mu kappa) (u : E) (hu : ‖u‖ = 1) :
    (∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu) ≤
      kappa ^ 6 * ‖populationCovariance mu‖ ^ 3 := by
  simpa [hu] using
    sixthMoment_le_populationCovariance_norm_mul_sq hmu hL6 u

end Scalarization

section Trace

variable [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- In finite dimension, the trace of the population second-moment operator is
the population squared norm. -/
theorem trace_populationCovariance_eq_integral_norm_sq
    {mu : Measure E} (hmu : MemLp id 2 mu) :
    (populationCovariance mu).toLinearMap.trace ℝ E =
      ∫ x, ‖x‖ ^ 2 ∂mu := by
  let b := stdOrthonormalBasis ℝ E
  rw [LinearMap.trace_eq_sum_inner _ b]
  change (∑ i, ⟪b i, populationCovariance mu (b i)⟫_ℝ) = _
  have hinner (i : Fin (Module.finrank ℝ E)) :
      ⟪b i, populationCovariance mu (b i)⟫_ℝ =
        ∫ x, ⟪b i, x⟫_ℝ * ⟪b i, x⟫_ℝ ∂mu := by
    rw [real_inner_comm]
    exact populationCovariance_inner hmu (b i) (b i)
  calc
    (∑ i, ⟪b i, populationCovariance mu (b i)⟫_ℝ) =
        ∑ i, ∫ x, ⟪b i, x⟫_ℝ * ⟪b i, x⟫_ℝ ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      exact hinner i
    _ = ∫ x, ∑ i, ⟪b i, x⟫_ℝ * ⟪b i, x⟫_ℝ ∂mu := by
      rw [integral_finsetSum Finset.univ]
      intro i _
      simpa only [id_eq, pow_two] using (hmu.const_inner (b i)).integrable_sq
    _ = ∫ x, ‖x‖ ^ 2 ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      simpa only [pow_two] using b.sum_sq_inner_right x

/-- For a probability distribution supported on the sphere of squared radius
`q`, the population covariance has trace exactly `q`. -/
theorem trace_populationCovariance_eq_fixedNorm
    {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}
    (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) :
    (populationCovariance mu).toLinearMap.trace ℝ E = q := by
  rw [trace_populationCovariance_eq_integral_norm_sq (fixedNorm_memLp hnorm 2)]
  calc
    (∫ x, ‖x‖ ^ 2 ∂mu) = ∫ _x, q ∂mu := integral_congr_ae hnorm
    _ = q := by simp

end Trace

/-- Scalar effective rank, used after separately identifying the covariance
trace and operator norm.  This definition does not itself identify
`opSigma` with the norm of `populationCovariance mu`. -/
def effectiveRank (traceSigma opSigma : ℝ) : ℝ := traceSigma / opSigma

theorem effectiveRank_le_iff
    {traceSigma opSigma r : ℝ} (hop : 0 < opSigma) :
    effectiveRank traceSigma opSigma ≤ r ↔
      traceSigma ≤ r * opSigma := by
  exact (div_le_iff₀ hop)

/-- Fixed norm makes Bai--Yin truncation inactive almost everywhere. -/
theorem ae_fixedNorm_baiYinTruncate_eq_self
    [MeasurableSpace E] {mu : Measure E}
    {T : ℕ} {q opSigma : ℝ} (hq : 0 ≤ q)
    (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (hsize : q ≤ (T : ℝ) * opSigma) :
    ∀ᵐ x ∂mu, baiYinTruncate T q opSigma x = x := by
  filter_upwards [hnorm] with x hx
  exact fixedNorm_baiYinTruncate_eq_self hq hx hsize

/-- Effective-rank sample-size control is exactly the condition making the
fixed-norm Bai--Yin truncation inactive. -/
theorem ae_baiYinTruncate_eq_self_of_effectiveRank_le
    [MeasurableSpace E] {mu : Measure E}
    {T : ℕ} {q opSigma : ℝ} (hq : 0 ≤ q) (hop : 0 < opSigma)
    (hnorm : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q)
    (heff : effectiveRank q opSigma ≤ (T : ℝ)) :
    ∀ᵐ x ∂mu, baiYinTruncate T q opSigma x = x := by
  apply ae_fixedNorm_baiYinTruncate_eq_self hq hnorm
  exact (effectiveRank_le_iff hop).mp heff

end

end TomographyOracleCore.PeriodicForwardCovariance
