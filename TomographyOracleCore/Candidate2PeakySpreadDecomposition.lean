import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing

/-!
# Peaky--spread decomposition for the Candidate 2 covariance process

This file formalizes the elementary decomposition at the start of Section 2
of Abdalla--Zhivotovskiy.  For a nonnegative observation `y` and `lambda > 0`,
the observation is bounded by its peaky part

`y * 1_{1 < lambda * y}`

plus the clipped spread part `lambda⁻¹ * psi (lambda * y)`.  Summing this
pointwise inequality gives the finite-sample covariance decomposition in every
direction.  The file does not include the later probabilistic estimates for
either the peaky or spread supremum.
-/

open MeasureTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

/-- The clipping function used by Abdalla--Zhivotovskiy:
`psi(x) = x` on `[-1, 1]`, and `psi(x) = sign(x)` outside that interval. -/
def clippedPsi (x : ℝ) : ℝ :=
  if x < -1 then -1 else if 1 < x then 1 else x

/-- The part of a nonnegative scalar observation above the cutoff
`lambda * y > 1`. -/
def peakyTerm (lambda y : ℝ) : ℝ :=
  if 1 < lambda * y then y else 0

/-- The clipped, rescaled contribution of one scalar observation. -/
def clippedSpread (lambda y : ℝ) : ℝ :=
  lambda⁻¹ * clippedPsi (lambda * y)

/-- The normalized average of a finite real sample.  At `T = 0` this is zero,
in accordance with Lean's total inverse. -/
def empiricalMean {T : ℕ} (y : Fin T → ℝ) : ℝ :=
  ((T : ℝ)⁻¹) * ∑ i, y i

/-- The normalized sum of observations above the peaky cutoff. -/
def peakyMean {T : ℕ} (lambda : ℝ) (y : Fin T → ℝ) : ℝ :=
  empiricalMean fun i ↦ peakyTerm lambda (y i)

/-- The normalized clipped empirical process. -/
def spreadMean {T : ℕ} (lambda : ℝ) (y : Fin T → ℝ) : ℝ :=
  empiricalMean fun i ↦ clippedSpread lambda (y i)

theorem clippedPsi_eq_one_of_one_lt {x : ℝ} (hx : 1 < x) :
    clippedPsi x = 1 := by
  have hleft : ¬x < -1 := by linarith
  rw [clippedPsi, if_neg hleft, if_pos hx]

theorem clippedPsi_eq_self_of_nonneg_of_le_one {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    clippedPsi x = x := by
  have hleft : ¬x < -1 := by linarith
  have hright : ¬1 < x := not_lt.mpr hx1
  rw [clippedPsi, if_neg hleft, if_neg hright]

/-- A clipped spread contribution remains nonnegative on nonnegative data. -/
theorem clippedSpread_nonneg {lambda y : ℝ} (hlambda : 0 < lambda)
    (hy : 0 ≤ y) :
    0 ≤ clippedSpread lambda y := by
  have hprod : 0 ≤ lambda * y := mul_nonneg hlambda.le hy
  have hleft : ¬lambda * y < -1 := by linarith
  by_cases htail : 1 < lambda * y
  · rw [clippedSpread, clippedPsi, if_neg hleft, if_pos htail, mul_one]
    exact inv_nonneg.mpr hlambda.le
  · rw [clippedSpread, clippedPsi, if_neg hleft, if_neg htail,
      ← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]
    exact hy

/-- Clipping never increases a nonnegative observation after rescaling. -/
theorem clippedSpread_le_self {lambda y : ℝ} (hlambda : 0 < lambda)
    (hy : 0 ≤ y) :
    clippedSpread lambda y ≤ y := by
  have hprod : 0 ≤ lambda * y := mul_nonneg hlambda.le hy
  have hleft : ¬lambda * y < -1 := by linarith
  by_cases htail : 1 < lambda * y
  · rw [clippedSpread, clippedPsi, if_neg hleft, if_pos htail, mul_one]
    have hinv : 1 * lambda⁻¹ ≤ y :=
      (mul_inv_le_iff₀ hlambda).2 (by simpa [mul_comm] using htail.le)
    simpa only [one_mul] using hinv
  · rw [clippedSpread, clippedPsi, if_neg hleft, if_neg htail,
      ← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]

theorem peakyTerm_nonneg {lambda y : ℝ} (hy : 0 ≤ y) :
    0 ≤ peakyTerm lambda y := by
  by_cases htail : 1 < lambda * y
  · simpa [peakyTerm, htail] using hy
  · simp [peakyTerm, htail]

theorem peakyTerm_le_self {lambda y : ℝ} (hy : 0 ≤ y) :
    peakyTerm lambda y ≤ y := by
  by_cases htail : 1 < lambda * y
  · simp [peakyTerm, htail]
  · simp [peakyTerm, htail, hy]

/-- The scalar peaky--spread inequality.  This is the pointwise algebra behind
the covariance-process decomposition. -/
theorem self_le_peakyTerm_add_clippedSpread
    {lambda y : ℝ} (hlambda : 0 < lambda) (hy : 0 ≤ y) :
    y ≤ peakyTerm lambda y + clippedSpread lambda y := by
  have hprod : 0 ≤ lambda * y := mul_nonneg hlambda.le hy
  have hleft : ¬lambda * y < -1 := by linarith
  by_cases htail : 1 < lambda * y
  · rw [peakyTerm, if_pos htail, clippedSpread, clippedPsi,
      if_neg hleft, if_pos htail, mul_one]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hlambda.le)
  · rw [peakyTerm, if_neg htail, clippedSpread, clippedPsi,
      if_neg hleft, if_neg htail, ← mul_assoc,
      inv_mul_cancel₀ hlambda.ne', one_mul, zero_add]

/-- `spreadMean` is exactly the `1 / (T * lambda)` normalization displayed in
the paper. -/
theorem spreadMean_eq_paper_normalization {T : ℕ} (lambda : ℝ)
    (y : Fin T → ℝ) :
    spreadMean lambda y =
      (lambda * (T : ℝ))⁻¹ * ∑ i, clippedPsi (lambda * y i) := by
  simp only [spreadMean, empiricalMean, clippedSpread, mul_inv_rev,
    mul_assoc, Finset.mul_sum]

theorem peakyMean_nonneg {T : ℕ} {lambda : ℝ} {y : Fin T → ℝ}
    (hy : ∀ i, 0 ≤ y i) :
    0 ≤ peakyMean lambda y := by
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  simp only [peakyMean, empiricalMean]
  exact mul_nonneg hweight
    (Finset.sum_nonneg fun i _ ↦ peakyTerm_nonneg (hy i))

theorem spreadMean_le_empiricalMean
    {T : ℕ} {lambda : ℝ} {y : Fin T → ℝ}
    (hlambda : 0 < lambda) (hy : ∀ i, 0 ≤ y i) :
    spreadMean lambda y ≤ empiricalMean y := by
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  simp only [spreadMean, empiricalMean]
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun i _ ↦ clippedSpread_le_self hlambda (hy i))
    hweight

theorem empiricalMean_le_peakyMean_add_spreadMean
    {T : ℕ} {lambda : ℝ} {y : Fin T → ℝ}
    (hlambda : 0 < lambda) (hy : ∀ i, 0 ≤ y i) :
    empiricalMean y ≤ peakyMean lambda y + spreadMean lambda y := by
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  simp only [empiricalMean, peakyMean, spreadMean]
  calc
    (T : ℝ)⁻¹ * ∑ i, y i ≤
        (T : ℝ)⁻¹ * ∑ i,
          (peakyTerm lambda (y i) + clippedSpread lambda (y i)) := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ ↦
          self_le_peakyTerm_add_clippedSpread hlambda (hy i)) hweight
    _ = (T : ℝ)⁻¹ * ∑ i, peakyTerm lambda (y i) +
        (T : ℝ)⁻¹ * ∑ i, clippedSpread lambda (y i) := by
      rw [Finset.sum_add_distrib, mul_add]

/-- A one-dimensional deterministic inequality that turns the two order
relations of the decomposition into an absolute-deviation bound. -/
theorem abs_sub_le_peaky_add_abs_spread_sub
    {a p s m : ℝ} (hp : 0 ≤ p) (hsa : s ≤ a) (haps : a ≤ p + s) :
    |a - m| ≤ p + |s - m| := by
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (s - m)]
  · linarith [le_abs_self (s - m)]

/-- Exact finite-sample peaky--spread decomposition for arbitrary nonnegative
scalar observations and an arbitrary population target `m`. -/
theorem empiricalAbsDeviation_le_peaky_add_spread
    {T : ℕ} {lambda : ℝ} {y : Fin T → ℝ}
    (hlambda : 0 < lambda) (hy : ∀ i, 0 ≤ y i) (m : ℝ) :
    |empiricalMean y - m| ≤
      peakyMean lambda y + |spreadMean lambda y - m| := by
  exact abs_sub_le_peaky_add_abs_spread_sub
    (peakyMean_nonneg hy)
    (spreadMean_le_empiricalMean hlambda hy)
    (empiricalMean_le_peakyMean_add_spreadMean hlambda hy)

section Covariance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Squared marginal observations in a fixed direction. -/
def directionalSquares {T : ℕ} (X : Fin T → E) (u : E) : Fin T → ℝ :=
  fun i ↦ ⟪X i, u⟫_ℝ ^ 2

/-- The peaky empirical term in a fixed direction. -/
def directionalPeakyMean {T : ℕ} (lambda : ℝ)
    (X : Fin T → E) (u : E) : ℝ :=
  peakyMean lambda (directionalSquares X u)

/-- The clipped spread empirical term in a fixed direction. -/
def directionalSpreadMean {T : ℕ} (lambda : ℝ)
    (X : Fin T → E) (u : E) : ℝ :=
  spreadMean lambda (directionalSquares X u)

theorem directionalSquares_nonneg {T : ℕ} (X : Fin T → E) (u : E)
    (i : Fin T) :
    0 ≤ directionalSquares X u i := by
  exact sq_nonneg _

/-- The exact directional covariance deviation is bounded by the peaky sum
plus the centered clipped-spread deviation.  Its only scalar hypothesis is
`lambda > 0`; nonnegativity is automatic for squared marginals. -/
theorem directional_covariance_deviation_le_peaky_add_spread
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu)
    {T : ℕ} (X : Fin T → E) (u : E)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    |⟪(sampleCovariance X - populationCovariance mu) u, u⟫_ℝ| ≤
      directionalPeakyMean lambda X u +
        |directionalSpreadMean lambda X u -
          ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu| := by
  rw [inner_sampleCovariance_sub_population_apply_self hmu]
  simpa only [directionalPeakyMean, directionalSpreadMean,
    directionalSquares, empiricalMean] using
    (empiricalAbsDeviation_le_peaky_add_spread
      (T := T) (lambda := lambda) (y := directionalSquares X u)
      hlambda (fun i ↦ sq_nonneg _) (∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu))

/-- Rayleigh-quotient form of the same deterministic decomposition.  This
version works for every direction, including zero, by Lean's total division. -/
theorem abs_covarianceError_rayleighQuotient_le_peaky_add_spread
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu)
    {T : ℕ} (X : Fin T → E) (u : E)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    |(sampleCovariance X - populationCovariance mu).rayleighQuotient u| ≤
      (directionalPeakyMean lambda X u +
        |directionalSpreadMean lambda X u -
          ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu|) / ‖u‖ ^ 2 := by
  have hdirection :=
    directional_covariance_deviation_le_peaky_add_spread hmu X u hlambda
  calc
    |(sampleCovariance X - populationCovariance mu).rayleighQuotient u| =
        |⟪(sampleCovariance X - populationCovariance mu) u, u⟫_ℝ| /
          ‖u‖ ^ 2 := by
      simp only [ContinuousLinearMap.rayleighQuotient,
        ContinuousLinearMap.reApplyInnerSelf_apply, RCLike.re_to_real,
        abs_div, abs_sq]
    _ ≤ (directionalPeakyMean lambda X u +
        |directionalSpreadMean lambda X u -
          ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu|) / ‖u‖ ^ 2 :=
      div_le_div_of_nonneg_right hdirection (sq_nonneg ‖u‖)

/-- Unit-direction form, matching the unit-sphere supremum in the paper. -/
theorem abs_covarianceError_rayleighQuotient_le_peaky_add_spread_of_norm_eq_one
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} (hmu : MemLp id 2 mu)
    {T : ℕ} (X : Fin T → E) (u : E) (hu : ‖u‖ = 1)
    {lambda : ℝ} (hlambda : 0 < lambda) :
    |(sampleCovariance X - populationCovariance mu).rayleighQuotient u| ≤
      directionalPeakyMean lambda X u +
        |directionalSpreadMean lambda X u -
          ∫ x, ⟪x, u⟫_ℝ ^ 2 ∂mu| := by
  simpa [hu] using
    (abs_covarianceError_rayleighQuotient_le_peaky_add_spread
      hmu X u hlambda)

/-- Exact operator-norm-to-Rayleigh-supremum representation specialized to the
sample-minus-population covariance operator.  Together with the preceding
pointwise theorem, this is the deterministic supremum reduction; the uniform
probability estimates are the separate remaining step. -/
theorem norm_covarianceError_eq_iSup_abs_rayleighQuotient
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {mu : Measure E} {T : ℕ} (X : Fin T → E) :
    ‖sampleCovariance X - populationCovariance mu‖ =
      ⨆ u : E,
        |(sampleCovariance X - populationCovariance mu).rayleighQuotient u| := by
  exact norm_sampleCovariance_sub_eq_iSup_rayleighQuotient
    X (populationCovariance mu) (populationCovariance_isSymmetric mu)

end Covariance

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
