import TomographyOracleCore.Candidate2PeakySpreadDecomposition

/-!
# Threshold-count reduction for the peaky covariance process

This file formalizes the deterministic reduction displayed as equation (11)
in Section 2.3 of Abdalla--Zhivotovskiy, *Covariance Estimation: Optimal
Dimension-free Guarantees for Adversarial Corruption and Heavy Tails*
(arXiv:2205.08494v3).

For a direction `u`, let `I_u` be the sample indices for which
`1 < lambda * <X_i,u>^2`.  The peaky empirical term is exactly the energy on
`I_u`.  Consequently its lower bound is the exceedance count divided by
`T * lambda`, while any uniform sparse directional-energy bound gives its
upper bound.

The predicate `SparseDirectionalEnergyBound` below is a Lean-facing name for
the directional side of equation (5) in the source.  This module proves only
the deterministic implication from that predicate.  It does **not** assert
the source's random sparse-supremum theorem (Theorem 3), its colouring
argument, or its effective-rank probability estimate.
-/

open InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Indices whose squared marginal in direction `u` exceeds the clipping
threshold.  This is the set `I_v` from Abdalla--Zhivotovskiy Section 2.3. -/
def directionalExceedanceSet {T : ℕ} (lambda : ℝ)
    (X : Fin T → E) (u : E) : Finset (Fin T) :=
  Finset.univ.filter fun i ↦ 1 < lambda * directionalSquares X u i

/-- A deterministic upper bound on the energy of every set of at most `k`
sample indices, uniformly over unit directions.

The paper identifies the least admissible `B` with the sparse coefficient
supremum `f(k, [T])` through its equation (5).  We use the directional form
directly, avoiding any unproved identification with a supremum. -/
def SparseDirectionalEnergyBound {T : ℕ} (k : ℕ)
    (X : Fin T → E) (B : ℝ) : Prop :=
  ∀ I : Finset (Fin T), I.card ≤ k →
    ∀ u : E, ‖u‖ = 1 →
      ∑ i ∈ I, directionalSquares X u i ≤ B

/-- A uniform bound on the number of threshold exceedances over all unit
directions. -/
def UniformDirectionalExceedanceCountBound {T : ℕ} (lambda : ℝ)
    (X : Fin T → E) (k : ℕ) : Prop :=
  ∀ u : E, ‖u‖ = 1 → (directionalExceedanceSet lambda X u).card ≤ k

/-- The peaky sum is exactly the squared-marginal energy on the exceedance
set. -/
theorem sum_peakyTerm_eq_sum_directionalExceedanceSet
    {T : ℕ} (lambda : ℝ) (X : Fin T → E) (u : E) :
    ∑ i, peakyTerm lambda (directionalSquares X u i) =
      ∑ i ∈ directionalExceedanceSet lambda X u,
        directionalSquares X u i := by
  classical
  rw [directionalExceedanceSet]
  symm
  simpa [peakyTerm] using
    (Finset.sum_filter
      (s := (Finset.univ : Finset (Fin T)))
      (fun i ↦ 1 < lambda * directionalSquares X u i)
      (fun i ↦ directionalSquares X u i))

/-- Exact restricted-sum formula for the directional peaky mean. -/
theorem directionalPeakyMean_eq_inv_mul_sum_exceedanceSet
    {T : ℕ} (lambda : ℝ) (X : Fin T → E) (u : E) :
    directionalPeakyMean lambda X u =
      (T : ℝ)⁻¹ * ∑ i ∈ directionalExceedanceSet lambda X u,
        directionalSquares X u i := by
  rw [directionalPeakyMean, peakyMean, empiricalMean,
    sum_peakyTerm_eq_sum_directionalExceedanceSet]

/-- Left-hand side of Abdalla--Zhivotovskiy equation (11): every threshold
exceedance contributes at least `lambda⁻¹` to the peaky sum. -/
theorem exceedance_card_div_le_directionalPeakyMean
    {T : ℕ} (hT : 0 < T) {lambda : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (u : E) :
    ((directionalExceedanceSet lambda X u).card : ℝ) /
        ((T : ℝ) * lambda) ≤
      directionalPeakyMean lambda X u := by
  classical
  let I := directionalExceedanceSet lambda X u
  have hpoint : ∀ i ∈ I, lambda⁻¹ ≤ directionalSquares X u i := by
    intro i hi
    have hiTail : 1 < lambda * directionalSquares X u i := by
      simpa [I, directionalExceedanceSet] using hi
    have hdiv : 1 / lambda < directionalSquares X u i :=
      (div_lt_iff₀ hlambda).2 (by simpa [mul_comm] using hiTail)
    simpa [one_div] using hdiv.le
  have hsum :
      ∑ _i ∈ I, lambda⁻¹ ≤
        ∑ i ∈ I, directionalSquares X u i :=
    Finset.sum_le_sum hpoint
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  calc
    (I.card : ℝ) / ((T : ℝ) * lambda) =
        (T : ℝ)⁻¹ * ∑ _i ∈ I, lambda⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp [hTne, hlambda.ne']
    _ ≤ (T : ℝ)⁻¹ *
        ∑ i ∈ I, directionalSquares X u i :=
      mul_le_mul_of_nonneg_left hsum hweight
    _ = directionalPeakyMean lambda X u := by
      rw [directionalPeakyMean_eq_inv_mul_sum_exceedanceSet]

/-- Right-hand side of equation (11), expressed without a supremum: once the
exceedance set has size at most `k`, a sparse directional-energy bound `B`
controls the peaky mean by `B / T`. -/
theorem directionalPeakyMean_le_sparseDirectionalEnergy
    {T k : ℕ} (_hT : 0 < T) {lambda B : ℝ}
    (X : Fin T → E)
    (hSparse : SparseDirectionalEnergyBound k X B)
    (u : E) (hu : ‖u‖ = 1)
    (hcard : (directionalExceedanceSet lambda X u).card ≤ k) :
    directionalPeakyMean lambda X u ≤ B / (T : ℝ) := by
  have hweight : 0 ≤ ((T : ℝ)⁻¹) :=
    inv_nonneg.mpr (Nat.cast_nonneg T)
  calc
    directionalPeakyMean lambda X u =
        (T : ℝ)⁻¹ *
          ∑ i ∈ directionalExceedanceSet lambda X u,
            directionalSquares X u i :=
      directionalPeakyMean_eq_inv_mul_sum_exceedanceSet lambda X u
    _ ≤ (T : ℝ)⁻¹ * B :=
      mul_le_mul_of_nonneg_left
        (hSparse (directionalExceedanceSet lambda X u) hcard u hu)
        hweight
    _ = B / (T : ℝ) := by ring

/-- The complete deterministic sandwich from equation (11). -/
theorem directionalPeakyMean_sparse_sandwich
    {T k : ℕ} (hT : 0 < T) {lambda B : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E)
    (hSparse : SparseDirectionalEnergyBound k X B)
    (u : E) (hu : ‖u‖ = 1)
    (hcard : (directionalExceedanceSet lambda X u).card ≤ k) :
    ((directionalExceedanceSet lambda X u).card : ℝ) /
          ((T : ℝ) * lambda) ≤
        directionalPeakyMean lambda X u ∧
      directionalPeakyMean lambda X u ≤ B / (T : ℝ) := by
  exact ⟨exceedance_card_div_le_directionalPeakyMean hT hlambda X u,
    directionalPeakyMean_le_sparseDirectionalEnergy hT X hSparse u hu hcard⟩

/-- Solving the two sides of equation (11) gives the deterministic
self-consistency inequality `|I_u| ≤ lambda * B`. -/
theorem exceedance_card_le_lambda_mul_sparseEnergy
    {T k : ℕ} (hT : 0 < T) {lambda B : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E)
    (hSparse : SparseDirectionalEnergyBound k X B)
    (u : E) (hu : ‖u‖ = 1)
    (hcard : (directionalExceedanceSet lambda X u).card ≤ k) :
    ((directionalExceedanceSet lambda X u).card : ℝ) ≤ lambda * B := by
  have hsandwich :=
    directionalPeakyMean_sparse_sandwich hT hlambda X hSparse u hu hcard
  have hquot :
      ((directionalExceedanceSet lambda X u).card : ℝ) /
          ((T : ℝ) * lambda) ≤ B / (T : ℝ) :=
    hsandwich.1.trans hsandwich.2
  have hden : 0 < (T : ℝ) * lambda :=
    mul_pos (Nat.cast_pos.mpr hT) hlambda
  have hmul := (div_le_iff₀ hden).1 hquot
  have hTne : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
  calc
    ((directionalExceedanceSet lambda X u).card : ℝ) ≤
        (B / (T : ℝ)) * ((T : ℝ) * lambda) := hmul
    _ = lambda * B := by field_simp [hTne]

/-- Uniform version of the sparse reduction.  This is the exact interface
needed after proving a simultaneous exceedance-count and sparse-energy event. -/
theorem directionalPeakyMean_le_of_uniform_sparse_event
    {T k : ℕ} (hT : 0 < T) {lambda B : ℝ}
    (X : Fin T → E)
    (hCount : UniformDirectionalExceedanceCountBound lambda X k)
    (hSparse : SparseDirectionalEnergyBound k X B) :
    ∀ u : E, ‖u‖ = 1 →
      directionalPeakyMean lambda X u ≤ B / (T : ℝ) := by
  intro u hu
  exact directionalPeakyMean_le_sparseDirectionalEnergy
    hT X hSparse u hu (hCount u hu)

/-- Elementary threshold counting by the empirical sixth moment.  The
restricted sum is an order-statistic statement: each selected index costs at
least one unit after multiplication by `lambda^3`. -/
theorem exceedance_card_le_lambda_cube_mul_restricted_sixth
    {T : ℕ} {lambda : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (u : E) :
    ((directionalExceedanceSet lambda X u).card : ℝ) ≤
      lambda ^ 3 *
        ∑ i ∈ directionalExceedanceSet lambda X u,
          |⟪X i, u⟫_ℝ| ^ 6 := by
  classical
  let I := directionalExceedanceSet lambda X u
  have hpoint : ∀ i ∈ I, (1 : ℝ) ≤ lambda ^ 3 * |⟪X i, u⟫_ℝ| ^ 6 := by
    intro i hi
    have hiTail : 1 < lambda * directionalSquares X u i := by
      simpa [I, directionalExceedanceSet] using hi
    have hprod : 0 ≤ lambda * directionalSquares X u i :=
      mul_nonneg hlambda.le (directionalSquares_nonneg X u i)
    have hpow : (1 : ℝ) ^ 3 ≤
        (lambda * directionalSquares X u i) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) hiTail.le 3
    have habs : |⟪X i, u⟫_ℝ| ^ 6 = ⟪X i, u⟫_ℝ ^ 6 := by
      rw [← abs_pow]
      exact abs_of_nonneg (by positivity)
    calc
      (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ (lambda * directionalSquares X u i) ^ 3 := hpow
      _ = lambda ^ 3 * |⟪X i, u⟫_ℝ| ^ 6 := by
        rw [habs]
        simp only [directionalSquares]
        ring
  calc
    (I.card : ℝ) = ∑ _i ∈ I, (1 : ℝ) := by simp
    _ ≤ ∑ i ∈ I, lambda ^ 3 * |⟪X i, u⟫_ℝ| ^ 6 :=
      Finset.sum_le_sum hpoint
    _ = lambda ^ 3 * ∑ i ∈ I, |⟪X i, u⟫_ℝ| ^ 6 := by
      rw [Finset.mul_sum]

/-- Unrestricted empirical-sixth-moment corollary of the threshold-count
bound. -/
theorem exceedance_card_le_lambda_cube_mul_sum_sixth
    {T : ℕ} {lambda : ℝ} (hlambda : 0 < lambda)
    (X : Fin T → E) (u : E) :
    ((directionalExceedanceSet lambda X u).card : ℝ) ≤
      lambda ^ 3 * ∑ i, |⟪X i, u⟫_ℝ| ^ 6 := by
  have hrestricted :=
    exceedance_card_le_lambda_cube_mul_restricted_sixth hlambda X u
  have hsum :
      ∑ i ∈ directionalExceedanceSet lambda X u, |⟪X i, u⟫_ℝ| ^ 6 ≤
        ∑ i, |⟪X i, u⟫_ℝ| ^ 6 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun _i _hi _hnot ↦ by positivity)
  exact hrestricted.trans
    (mul_le_mul_of_nonneg_left hsum (by positivity))

/-- Elementary solver for the square-root self-consistency inequality used
after equation (11) in the source (lines leading to `m \lesssim r(Sigma)`).
This is a derived algebraic lemma, not a quoted probabilistic result. -/
theorem self_consistent_sqrt_count_le
    {m r A : ℝ} (hm : 0 ≤ m) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hself : m ≤ A * (r + Real.sqrt (r * m))) :
    m ≤ 2 * (A + A ^ 2) * r := by
  have hsqrtm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
  have hsqrtr : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr
  have hyoung :=
    two_mul_le_add_sq (Real.sqrt m) (2 * A * Real.sqrt r)
  have hmixed :
      A * Real.sqrt (r * m) ≤ m / 4 + A ^ 2 * r := by
    rw [Real.sqrt_mul hr]
    nlinarith
  have hcoef : 0 ≤ (A + A ^ 2) * r :=
    mul_nonneg (add_nonneg hA (sq_nonneg A)) hr
  nlinarith

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
