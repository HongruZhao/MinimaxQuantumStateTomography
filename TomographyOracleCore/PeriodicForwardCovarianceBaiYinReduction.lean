import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# Deterministic front end for the periodic-forward covariance route

This file formalizes only the algebraic and measure-theoretic reductions which
precede a dimension-free Bai--Yin theorem.  It deliberately does **not** state
the Bai--Yin conclusion as a theorem: that probabilistic inequality is not in
Mathlib and is the remaining external mathematical formalization project.

The intended application has fixed-norm real vectors (obtained by realifying
the phase-randomized complex rank-one lift), sixth-to-second marginal moment
control, and effective rank of order `D`.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The rank-one second-moment operator `x ⊗ x`. -/
def rankOneCovariance (x : E) : E →L[ℝ] E :=
  InnerProductSpace.rankOne ℝ x x

@[simp]
theorem rankOneCovariance_apply (x u : E) :
    rankOneCovariance x u = ⟪x, u⟫_ℝ • x := by
  simp [rankOneCovariance]

@[simp]
theorem norm_rankOneCovariance (x : E) :
    ‖rankOneCovariance x‖ = ‖x‖ ^ 2 := by
  simp [rankOneCovariance, pow_two]

theorem rankOneCovariance_isSymmetric (x : E) :
    (rankOneCovariance x).toLinearMap.IsSymmetric := by
  simpa [rankOneCovariance] using
    (InnerProductSpace.isSymmetric_rankOne_self (𝕜 := ℝ) x)

/-- Uncentered sample covariance, normalized by the sample size.  For `T = 0`
this is definitionally zero because Lean's inverse of zero is zero. -/
def sampleCovariance {T : ℕ} (X : Fin T → E) : E →L[ℝ] E :=
  ((T : ℝ)⁻¹) • ∑ i, rankOneCovariance (X i)

@[simp]
theorem sampleCovariance_apply {T : ℕ} (X : Fin T → E) (u : E) :
    sampleCovariance X u =
      ((T : ℝ)⁻¹) • ∑ i, ⟪X i, u⟫_ℝ • X i := by
  classical
  simp [sampleCovariance]

theorem inner_sampleCovariance_apply_self {T : ℕ} (X : Fin T → E) (u : E) :
    ⟪sampleCovariance X u, u⟫_ℝ =
      ((T : ℝ)⁻¹) * ∑ i, ⟪X i, u⟫_ℝ ^ 2 := by
  classical
  rw [sampleCovariance_apply, real_inner_smul_left, sum_inner]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [real_inner_smul_left, pow_two]

theorem sampleCovariance_isSymmetric {T : ℕ} (X : Fin T → E) :
    (sampleCovariance X).toLinearMap.IsSymmetric := by
  classical
  unfold sampleCovariance
  rw [ContinuousLinearMap.toLinearMap_smul]
  refine LinearMap.IsSymmetric.smul (by simp) ?_
  rw [ContinuousLinearMap.toLinearMap_sum]
  exact LinearMap.isSymmetric_sum Finset.univ fun i _ ↦
    rankOneCovariance_isSymmetric (X i)

/-- The exact Rayleigh-quotient reduction used before any empirical-process
estimate. -/
theorem norm_sampleCovariance_sub_eq_iSup_rayleighQuotient
    {T : ℕ} (X : Fin T → E) (Sigma : E →L[ℝ] E)
    (hSigma : Sigma.toLinearMap.IsSymmetric) :
    ‖sampleCovariance X - Sigma‖ =
      ⨆ u : E, |(sampleCovariance X - Sigma).rayleighQuotient u| := by
  apply ContinuousLinearMap.norm_eq_iSup_rayleighQuotient
  exact (sampleCovariance_isSymmetric X).sub hSigma

/-- Lean-friendly sixth-to-second marginal moment assumption.  This is the
sixth-power form of `‖⟨X,u⟩‖_{L6} ≤ kappa ‖⟨X,u⟩‖_{L2}`. -/
def HasL6L2Marginals [MeasurableSpace E] (mu : Measure E) (kappa : ℝ) : Prop :=
  ∀ u : E,
    ∫ x, |⟪x, u⟫_ℝ| ^ 6 ∂mu ≤
      kappa ^ 6 * (∫ x, |⟪x, u⟫_ℝ| ^ 2 ∂mu) ^ 3

/-- Truncation written in fourth-power form.  For nonnegative radii this is
equivalent to the cutoff in Abdalla--Zhivotovskiy's Theorem 2. -/
def baiYinTruncate (T : ℕ) (traceSigma opSigma : ℝ) (x : E) : E :=
  if ‖x‖ ^ 4 ≤ (T : ℝ) * traceSigma * opSigma then x else 0

theorem baiYinTruncate_eq_self
    {T : ℕ} {traceSigma opSigma : ℝ} {x : E}
    (h : ‖x‖ ^ 4 ≤ (T : ℝ) * traceSigma * opSigma) :
    baiYinTruncate T traceSigma opSigma x = x := by
  simp [baiYinTruncate, h]

/-- Fixed norm makes the Bai--Yin truncation inactive once the sample size is
at least the corresponding effective-rank scale. -/
theorem fixedNorm_baiYinTruncate_eq_self
    {T : ℕ} {q opSigma : ℝ} {x : E}
    (hq : 0 ≤ q) (hnorm : ‖x‖ ^ 2 = q)
    (hsize : q ≤ (T : ℝ) * opSigma) :
    baiYinTruncate T q opSigma x = x := by
  apply baiYinTruncate_eq_self
  rw [show ‖x‖ ^ 4 = q ^ 2 by nlinarith [sq_nonneg (‖x‖ ^ 2)]]
  nlinarith

/-- The exact population second-moment operator already available in Mathlib. -/
abbrev populationCovariance [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (mu : Measure E) : E →L[ℝ] E :=
  covarianceOperator mu

theorem populationCovariance_inner
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu) (u v : E) :
    ⟪populationCovariance mu u, v⟫_ℝ =
      ∫ x, ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ ∂mu := by
  simpa [populationCovariance] using covarianceOperator_inner hmu u v

theorem populationCovariance_isSymmetric
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (mu : Measure E) :
    (populationCovariance mu).toLinearMap.IsSymmetric :=
  by simpa [populationCovariance] using
    (isPositive_covarianceOperator (E := E) (μ := mu)).isSymmetric

end

end TomographyOracleCore.PeriodicForwardCovariance
