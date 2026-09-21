import TomographyOracleCore.RelativeDesignThreeMomentPermutationSupport

namespace TomographyOracleCore

open scoped BigOperators

noncomputable section

/-!
# Explicit order-three Weingarten matrix

At moment order three the inverse of the normalized permutation Gram
matrix has only three values, according to the conjugacy class of
`sigma * tau⁻¹`.  The coefficient below is `D^3 Wg(sigma*tau⁻¹,D)`.
-/

/-- Common denominator of the order-three unitary Weingarten function. -/
def weingartenThreeDenominator (D : ℕ) : ℝ :=
  (((D : ℝ) ^ 2 - 1) * ((D : ℝ) ^ 2 - 4))

/-- The normalized order-three Weingarten coefficient `D^3 Wg`. -/
def normalizedWeingartenThree (D : ℕ)
    (sigma tau : Equiv.Perm (Fin 3)) : ℝ :=
  if finThreeFullCycleCount (sigma * tau⁻¹) = 3 then
    (D : ℝ) ^ 2 * ((D : ℝ) ^ 2 - 2) /
      weingartenThreeDenominator D
  else if finThreeFullCycleCount (sigma * tau⁻¹) = 2 then
    -((D : ℝ) ^ 3) / weingartenThreeDenominator D
  else
    2 * (D : ℝ) ^ 2 / weingartenThreeDenominator D

/-- Difference between normalized Weingarten and the identity matrix. -/
def normalizedWeingartenDeltaThree (D : ℕ)
    (sigma tau : Equiv.Perm (Fin 3)) : ℝ :=
  normalizedWeingartenThree D sigma tau -
    if sigma = tau then 1 else 0

/-- Explicit absolute value of the normalized Weingarten defect. -/
def normalizedWeingartenAbsoluteDeltaThree (D : ℕ)
    (sigma tau : Equiv.Perm (Fin 3)) : ℝ :=
  if sigma = tau then
    (3 * (D : ℝ) ^ 2 - 4) / weingartenThreeDenominator D
  else if finThreeFullCycleCount (sigma * tau⁻¹) = 2 then
    (D : ℝ) ^ 3 / weingartenThreeDenominator D
  else
    2 * (D : ℝ) ^ 2 / weingartenThreeDenominator D

theorem weingartenThreeDenominator_pos
    (D : ℕ) (hD : 3 ≤ D) : 0 < weingartenThreeDenominator D := by
  have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
  unfold weingartenThreeDenominator
  have h1 : 0 < (D : ℝ) ^ 2 - 1 := by nlinarith
  have h4 : 0 < (D : ℝ) ^ 2 - 4 := by nlinarith
  exact mul_pos h1 h4

set_option maxHeartbeats 1200000 in
/-- The displayed order-three coefficients are the inverse of the
normalized permutation Gram matrix. -/
theorem normalizedPermutationGramThree_mul_normalizedWeingartenThree
    (D : ℕ) (hD : 3 ≤ D)
    (sigma rho : Equiv.Perm (Fin 3)) :
    (∑ tau : Equiv.Perm (Fin 3),
      normalizedPermutationGramThree D sigma tau *
        normalizedWeingartenThree D tau rho) =
      if sigma = rho then 1 else 0 := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hD1 : (D : ℝ) ^ 2 - 1 ≠ 0 := by
    have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  have hD4 : (D : ℝ) ^ 2 - 4 ≠ 0 := by
    have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  rcases finThreePerm_eq_six sigma with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases finThreePerm_eq_six rho with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [finThreePerm_univ_explicit,
      normalizedPermutationGramThree, normalizedWeingartenThree,
      weingartenThreeDenominator, finThreeFullCycleCount,
      finThreeCycleForward, finThreeCycleBackward, Equiv.swap_apply_def] <;>
    field_simp <;> ring

/-- A permutation of three slots has three cycles exactly when it is the
identity. -/
theorem finThreeFullCycleCount_eq_three_iff
    (pi : Equiv.Perm (Fin 3)) :
    finThreeFullCycleCount pi = 3 ↔ pi = 1 := by
  unfold finThreeFullCycleCount
  by_cases hpi : pi = 1
  · simp [hpi]
  · simp only [hpi, if_false]
    split_ifs <;> simp

set_option maxHeartbeats 1200000 in
/-- At `D ≥ 3`, the explicit piecewise expression is exactly the absolute
value of the normalized Weingarten defect. -/
theorem abs_normalizedWeingartenDeltaThree
    (D : ℕ) (hD : 3 ≤ D)
    (sigma tau : Equiv.Perm (Fin 3)) :
    |normalizedWeingartenDeltaThree D sigma tau| =
      normalizedWeingartenAbsoluteDeltaThree D sigma tau := by
  have hden := weingartenThreeDenominator_pos D hD
  have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
  by_cases hst : sigma = tau
  · subst tau
    have hnum : 0 ≤ 3 * (D : ℝ) ^ 2 - 4 := by
      nlinarith [sq_nonneg ((D : ℝ) - 3)]
    have hcalc : normalizedWeingartenDeltaThree D sigma sigma =
        (3 * (D : ℝ) ^ 2 - 4) / weingartenThreeDenominator D := by
      simp [normalizedWeingartenDeltaThree, normalizedWeingartenThree]
      field_simp [hden.ne']
      unfold weingartenThreeDenominator
      ring
    rw [hcalc, abs_of_nonneg (div_nonneg hnum hden.le)]
    simp [normalizedWeingartenAbsoluteDeltaThree]
  · have hcount3 :
        finThreeFullCycleCount (sigma * tau⁻¹) ≠ 3 := by
      intro hthree
      apply hst
      have hone := (finThreeFullCycleCount_eq_three_iff _).mp hthree
      simpa [mul_inv_eq_one] using hone
    by_cases hcount2 :
        finThreeFullCycleCount (sigma * tau⁻¹) = 2
    · have hfrac : 0 ≤ (D : ℝ) ^ 3 /
          weingartenThreeDenominator D :=
        div_nonneg (by positivity) hden.le
      have hdelta : normalizedWeingartenDeltaThree D sigma tau =
          -((D : ℝ) ^ 3 / weingartenThreeDenominator D) := by
        simp [normalizedWeingartenDeltaThree, normalizedWeingartenThree,
          hst, hcount3, hcount2]
        rw [neg_div]
      rw [hdelta, abs_neg, abs_of_nonneg hfrac]
      simp [normalizedWeingartenAbsoluteDeltaThree, hst, hcount2]
    · have hfrac : 0 ≤ 2 * (D : ℝ) ^ 2 /
          weingartenThreeDenominator D :=
        div_nonneg (by positivity) hden.le
      simp [normalizedWeingartenDeltaThree,
        normalizedWeingartenAbsoluteDeltaThree, normalizedWeingartenThree,
        hst, hcount3, hcount2, abs_of_nonneg hfrac]

set_option maxHeartbeats 1200000 in
/-- Exact ℓ¹ defect of the six-by-six normalized Weingarten matrix. -/
theorem sum_normalizedWeingartenAbsoluteDeltaThree
    (D : ℕ) (hD : 3 ≤ D) :
    (∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        normalizedWeingartenAbsoluteDeltaThree D sigma tau) =
      6 * (3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
        weingartenThreeDenominator D := by
  have hden := weingartenThreeDenominator_pos D hD
  simp +decide [finThreePerm_univ_explicit,
    normalizedWeingartenAbsoluteDeltaThree,
    weingartenThreeDenominator, finThreeFullCycleCount,
    finThreeCycleForward, finThreeCycleBackward, Equiv.swap_apply_def]
  field_simp
  ring

/-- The exact order-three ℓ¹ defect is bounded by the B.21 parameter. -/
theorem normalizedWeingartenAbsoluteDeltaThree_le
    (D : ℕ) (hD : 18 ≤ D) :
    (3 * (D : ℝ) ^ 3 + 7 * (D : ℝ) ^ 2 - 4) /
        weingartenThreeDenominator D ≤
      9 / (2 * (D : ℝ) - 9) := by
  have hDr : (18 : ℝ) ≤ D := by exact_mod_cast hD
  have hden := weingartenThreeDenominator_pos D (by omega)
  have hright : 0 < 2 * (D : ℝ) - 9 := by linarith
  rw [div_le_div_iff₀ hden hright]
  unfold weingartenThreeDenominator
  have hpoly : 0 ≤ (D : ℝ) *
      (3 * (D : ℝ) ^ 3 + 13 * (D : ℝ) ^ 2 + 18 * (D : ℝ) + 8) := by
    positivity
  nlinarith

end

end TomographyOracleCore
