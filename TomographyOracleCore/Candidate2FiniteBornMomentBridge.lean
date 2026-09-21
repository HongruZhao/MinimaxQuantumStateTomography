import TomographyOracleCore.Candidate2FiniteBornVectorLaw

/-!
# Candidate 2: exact finite Born-moment bridge

The Candidate-2 vector is `sqrt(D+1)` times a unit measurement vector.  This
file removes that scaling exactly.  Consequently, its complex `L6--L2`
condition is reduced to a single finite Born-weighted inequality between an
unscaled sixth marginal and the cube of an unscaled second marginal.

The unscaled sixth marginal contains one Born weight and three test-vector
overlaps, so it is precisely a fourth-projective-moment quantity.  No
Clifford moment estimate is assumed or asserted here.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators ENNReal RealInnerProductSpace

namespace TomographyOracleCore.Candidate2FiniteBornMomentBridge

noncomputable section

open MatrixReduction
open Candidate2FiniteBornVectorLaw
open Candidate2PhaseRandomizedL6L2

variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]

/-- The unscaled Born-weighted second marginal of a finite projective
measurement ensemble. -/
def finiteUnitaryBornUnscaledSecondMarginal
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ((Fintype.card A : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : A, ∑ b : Fin D,
      finiteUnitaryBornWeight rho (U e) b *
        ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 2

/-- The unscaled Born-weighted sixth marginal.  There are four projective
copies: one in the Born weight and three in the sixth power. -/
def finiteUnitaryBornUnscaledSixthMarginal
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ((Fintype.card A : ℕ) : ℝ≥0∞)⁻¹.toReal •
    ∑ e : A, ∑ b : Fin D,
      finiteUnitaryBornWeight rho (U e) b *
        ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 6

/-- Exact second-power scaling of the Candidate-2 measurement vector. -/
theorem norm_inner_candidate2ScaledMeasurementVector_sq
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D)
    (u : EuclideanSpace ℂ (Fin D)) :
    ‖⟪candidate2ScaledMeasurementVector U b, u⟫_ℂ‖ ^ 2 =
      ((D : ℝ) + 1) *
        ‖⟪finiteUnitaryMeasurementVector U b, u⟫_ℂ‖ ^ 2 := by
  rw [candidate2ScaledMeasurementVector, inner_smul_left_eq_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt (by positivity)]

/-- Exact sixth-power scaling of the Candidate-2 measurement vector. -/
theorem norm_inner_candidate2ScaledMeasurementVector_sixth
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D)
    (u : EuclideanSpace ℂ (Fin D)) :
    ‖⟪candidate2ScaledMeasurementVector U b, u⟫_ℂ‖ ^ 6 =
      ((D : ℝ) + 1) ^ 3 *
        ‖⟪finiteUnitaryMeasurementVector U b, u⟫_ℂ‖ ^ 6 := by
  rw [candidate2ScaledMeasurementVector, inner_smul_left_eq_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]
  rw [show Real.sqrt ((D : ℝ) + 1) ^ 6 = ((D : ℝ) + 1) ^ 3 by
    calc
      Real.sqrt ((D : ℝ) + 1) ^ 6 =
          (Real.sqrt ((D : ℝ) + 1) ^ 2) ^ 3 := by ring
      _ = ((D : ℝ) + 1) ^ 3 := by
        rw [Real.sq_sqrt (by positivity : 0 ≤ (D : ℝ) + 1)]]

/-- Pull a common scalar out of the two finite sums used in the Born law. -/
private theorem sum_sum_mul_factor
    (c : ℝ) (f : A → Fin D → ℝ) :
    (∑ e : A, ∑ b : Fin D, c * f e b) =
      c * ∑ e : A, ∑ b : Fin D, f e b := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _he
  rw [Finset.mul_sum]

/-- Exact integral formula for the scaled second marginal. -/
theorem integral_finiteUnitaryBornVectorLaw_inner_sq
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 2 ∂finiteUnitaryBornVectorLaw U rho) =
      ((D : ℝ) + 1) *
        finiteUnitaryBornUnscaledSecondMarginal U rho u := by
  rw [integral_finiteUnitaryBornVectorLaw_real_eq_sum hD]
  simp_rw [norm_inner_candidate2ScaledMeasurementVector_sq]
  have hsum :
      (∑ e : A, ∑ b : Fin D,
        finiteUnitaryBornWeight rho (U e) b *
          (((D : ℝ) + 1) *
            ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 2)) =
        ((D : ℝ) + 1) *
          ∑ e : A, ∑ b : Fin D,
            finiteUnitaryBornWeight rho (U e) b *
              ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 2 := by
    calc
      _ = ∑ e : A, ∑ b : Fin D,
          ((D : ℝ) + 1) *
            (finiteUnitaryBornWeight rho (U e) b *
              ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro e _he
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = _ := sum_sum_mul_factor _ _
  rw [hsum]
  simp only [finiteUnitaryBornUnscaledSecondMarginal, smul_eq_mul]
  ring

/-- Exact integral formula for the scaled sixth marginal. -/
theorem integral_finiteUnitaryBornVectorLaw_inner_sixth
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂finiteUnitaryBornVectorLaw U rho) =
      ((D : ℝ) + 1) ^ 3 *
        finiteUnitaryBornUnscaledSixthMarginal U rho u := by
  rw [integral_finiteUnitaryBornVectorLaw_real_eq_sum hD]
  simp_rw [norm_inner_candidate2ScaledMeasurementVector_sixth]
  have hsum :
      (∑ e : A, ∑ b : Fin D,
        finiteUnitaryBornWeight rho (U e) b *
          (((D : ℝ) + 1) ^ 3 *
            ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 6)) =
        ((D : ℝ) + 1) ^ 3 *
          ∑ e : A, ∑ b : Fin D,
            finiteUnitaryBornWeight rho (U e) b *
              ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 6 := by
    calc
      _ = ∑ e : A, ∑ b : Fin D,
          ((D : ℝ) + 1) ^ 3 *
            (finiteUnitaryBornWeight rho (U e) b *
              ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 6) := by
        apply Finset.sum_congr rfl
        intro e _he
        apply Finset.sum_congr rfl
        intro b _hb
        ring
      _ = _ := sum_sum_mul_factor _ _
  rw [hsum]
  simp only [finiteUnitaryBornUnscaledSixthMarginal, smul_eq_mul]
  ring

/-- The exact fourth-projective-moment reduction.  An unscaled finite-sum
comparison yields the complex `L6--L2` property of the literal scaled Born
vector law with no loss in the constant. -/
theorem hasComplexL6L2Marginals_finiteUnitaryBornVectorLaw_of_unscaled
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) (kappa : ℝ)
    (hmoment : ∀ u : EuclideanSpace ℂ (Fin D),
      finiteUnitaryBornUnscaledSixthMarginal U rho u ≤
        kappa ^ 6 *
          (finiteUnitaryBornUnscaledSecondMarginal U rho u) ^ 3) :
    HasComplexL6L2Marginals (finiteUnitaryBornVectorLaw U rho) kappa := by
  intro u
  rw [integral_finiteUnitaryBornVectorLaw_inner_sixth hD,
    integral_finiteUnitaryBornVectorLaw_inner_sq hD]
  have hscale : 0 ≤ ((D : ℝ) + 1) ^ 3 := by positivity
  calc
    ((D : ℝ) + 1) ^ 3 *
        finiteUnitaryBornUnscaledSixthMarginal U rho u ≤
      ((D : ℝ) + 1) ^ 3 *
        (kappa ^ 6 *
          finiteUnitaryBornUnscaledSecondMarginal U rho u ^ 3) :=
        mul_le_mul_of_nonneg_left (hmoment u) hscale
    _ = kappa ^ 6 *
        (((D : ℝ) + 1) *
          finiteUnitaryBornUnscaledSecondMarginal U rho u) ^ 3 := by ring

/-- Literal periodic Cho--Kim specialization of the same exact reduction. -/
theorem hasComplexL6L2Marginals_choKimPeriodicBornVectorLaw_of_unscaled
    {n K : ℕ} (hdiv : K ∣ n)
    (rho : DensityOperator (Fin (2 ^ n))) (kappa : ℝ)
    (hmoment : ∀ u : EuclideanSpace ℂ (Fin (2 ^ n)),
      finiteUnitaryBornUnscaledSixthMarginal
          (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho u ≤
        kappa ^ 6 *
          (finiteUnitaryBornUnscaledSecondMarginal
            (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho u) ^ 3) :
    HasComplexL6L2Marginals
      (choKimPeriodicBornVectorLaw hdiv rho) kappa := by
  unfold choKimPeriodicBornVectorLaw
  exact
    hasComplexL6L2Marginals_finiteUnitaryBornVectorLaw_of_unscaled
      (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        rho kappa hmoment

end

end TomographyOracleCore.Candidate2FiniteBornMomentBridge
