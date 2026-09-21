import TomographyOracleCore.RelativeDesignThreeMomentWeingarten

namespace TomographyOracleCore

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance haarReferenceB23SpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance haarReferenceB23StarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Literal order-three Haar/reference Choi comparison (B.23)

The actual Haar identification is kept as a literal equality with the
explicit Weingarten Choi matrix.  Everything after that identity—the exact
error, support, norm estimate, and relative-CP conclusion—is finite algebra.
-/

/-- Raw unnormalized-Choi form of the order-three Weingarten expression.
Since `normalizedWeingartenThree = D^3 Wg`, the outer factor `D^-3`
recovers the usual unitary Weingarten coefficient. -/
def finiteThreeMomentWeingartenRawChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  ((((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
    ∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree D sigma tau : ℂ) • Q sigma tau

/-- Raw Choi form of the approximate-Haar frame map `Phi_a`. -/
def finiteThreeMomentApproximateHaarRawChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  ((((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
    ∑ sigma : Equiv.Perm (Fin 3), Q sigma sigma

/-- Matrix-valued normalized Weingarten defect. -/
def normalizedWeingartenWeightedErrorThree
    {E : Type*} [AddCommMonoid E] [Module ℂ E]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → E) : E :=
  ∑ sigma : Equiv.Perm (Fin 3),
    ∑ tau : Equiv.Perm (Fin 3),
      (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau

/-- Subtracting the approximate-Haar frame Choi matrix from the literal
Weingarten Choi matrix gives the scaled normalized defect. -/
theorem finiteThreeMomentWeingartenRawChoi_sub_approximateHaar
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    finiteThreeMomentWeingartenRawChoi D Q -
        finiteThreeMomentApproximateHaarRawChoi D Q =
      ((((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
        normalizedWeingartenWeightedErrorThree D Q := by
  unfold finiteThreeMomentWeingartenRawChoi
    finiteThreeMomentApproximateHaarRawChoi
    normalizedWeingartenWeightedErrorThree
  rw [← smul_sub]
  congr 1
  unfold normalizedWeingartenDeltaThree
  simp [sub_smul, Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro sigma hsigma
  rw [← Fintype.sum_ite_eq' sigma (fun tau ↦ Q sigma tau)]
  apply Finset.sum_congr rfl
  intro tau htau
  by_cases h : tau = sigma
  · subst tau
    rw [if_pos (show sigma = sigma from rfl),
      if_pos (show sigma = sigma from rfl)]
    exact (one_smul ℂ (Q sigma sigma)).symm
  · have h' : sigma ≠ tau := fun hst ↦ h hst.symm
    rw [if_neg h, if_neg h']
    exact (zero_smul ℂ (Q sigma tau)).symm

/-- Operator-norm triangle estimate with the exact order-three ℓ¹
Weingarten defect. -/
theorem norm_normalizedWeingartenWeightedErrorThree_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (D : ℕ) (hD : 3 ≤ D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → E)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1) :
    ‖normalizedWeingartenWeightedErrorThree D Q‖ ≤
      6 * (3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
        weingartenThreeDenominator D := by
  calc
    ‖normalizedWeingartenWeightedErrorThree D Q‖ ≤
        ∑ sigma : Equiv.Perm (Fin 3),
          ∑ tau : Equiv.Perm (Fin 3),
            ‖(normalizedWeingartenDeltaThree D sigma tau : ℂ) •
              Q sigma tau‖ := by
      unfold normalizedWeingartenWeightedErrorThree
      exact (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun sigma _ ↦ norm_sum_le _ _)
    _ ≤ ∑ sigma : Equiv.Perm (Fin 3),
          ∑ tau : Equiv.Perm (Fin 3),
            normalizedWeingartenAbsoluteDeltaThree D sigma tau := by
      apply Finset.sum_le_sum
      intro sigma hsigma
      apply Finset.sum_le_sum
      intro tau htau
      rw [norm_smul]
      have hcoeff :
          ‖(normalizedWeingartenDeltaThree D sigma tau : ℂ)‖ =
            normalizedWeingartenAbsoluteDeltaThree D sigma tau := by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using
          abs_normalizedWeingartenDeltaThree D hD sigma tau
      rw [hcoeff]
      exact mul_le_of_le_one_right
        (by rw [← abs_normalizedWeingartenDeltaThree D hD]; positivity)
        (hQ sigma tau)
    _ = 6 * (3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
          weingartenThreeDenominator D :=
      sum_normalizedWeingartenAbsoluteDeltaThree D hD

/-- B.23 in raw-Choi normalization: the literal Haar/reference Choi error
is at most `epsilon` times the flat reference eigenvalue, where
`epsilon = 9/(2D-9)`. -/
theorem norm_scaled_normalizedWeingartenWeightedErrorThree_le
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (D : ℕ) (hD : 18 ≤ D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) → E)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1) :
    ‖(((((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
        normalizedWeingartenWeightedErrorThree D Q)‖ ≤
      (9 / (2 * (D : ℝ) - 9)) *
        (6 * ((D : ℝ) ^ 3)⁻¹) := by
  have hD3 : 3 ≤ D := by omega
  have hscale : 0 ≤ ((D : ℝ) ^ 3)⁻¹ := by positivity
  rw [norm_smul]
  have hnormScale : ‖(((((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ))‖ =
      ((D : ℝ) ^ 3)⁻¹ := by
    simpa using abs_of_nonneg hscale
  rw [hnormScale]
  calc
    ((D : ℝ) ^ 3)⁻¹ *
        ‖normalizedWeingartenWeightedErrorThree D Q‖ ≤
      ((D : ℝ) ^ 3)⁻¹ *
        (6 * (3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
          weingartenThreeDenominator D) :=
      mul_le_mul_of_nonneg_left
        (norm_normalizedWeingartenWeightedErrorThree_le D hD3 Q hQ)
        hscale
    _ ≤ ((D : ℝ) ^ 3)⁻¹ *
        (6 * (9 / (2 * (D : ℝ) - 9))) := by
      apply mul_le_mul_of_nonneg_left _ hscale
      rw [show 6 * (3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
          weingartenThreeDenominator D =
        6 * ((3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
          weingartenThreeDenominator D) by ring]
      apply mul_le_mul_of_nonneg_left
        (normalizedWeingartenAbsoluteDeltaThree_le D hD) (by norm_num)
    _ = (9 / (2 * (D : ℝ) - 9)) *
        (6 * ((D : ℝ) ^ 3)⁻¹) := by ring

end

end TomographyOracleCore
