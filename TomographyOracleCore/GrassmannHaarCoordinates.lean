import TomographyOracleCore.GrassmannUnitaryHaar

namespace TomographyOracleCore

open MatrixReduction MeasureTheory Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-!
# Coordinate form of the canonical Grassmann overlap

The analytic input in the Hayden--Leung--Winter argument is a statement
about the squared mass of the lower-left block of a Haar unitary.  This file
identifies that concrete block mass with the invariant projector overlap.
-/

/-- Squared Frobenius mass of the rows outside the first `m` coordinates and
the columns inside them. -/
def canonicalUnitaryComplementCoordinateMass (k m : ℕ)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) : ℝ :=
  ∑ i : Fin k, if m ≤ (i : ℕ) then
    ∑ j : Fin k, if (j : ℕ) < m then Complex.normSq (U.1 i j) else 0
  else 0

/-- Contribution of one of the first `m` unitary columns to the complementary
coordinate block.  These are the eigenbasis observables `a_i` in the
Hayden--Leung--Winter Jensen comparison. -/
def canonicalUnitaryComplementColumnMass (k m : ℕ) (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) (j : Fin m) : ℝ :=
  ∑ i : Fin k, if m ≤ (i : ℕ) then
    Complex.normSq (U.1 i (Fin.castLE hmk j)) else 0

/-- The lower-left block mass is the sum of its first-`m` column masses. -/
theorem canonicalUnitaryComplementCoordinateMass_eq_sum_columnMass
    (k m : ℕ) (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    canonicalUnitaryComplementCoordinateMass k m U =
      ∑ j : Fin m, canonicalUnitaryComplementColumnMass k m hmk U j := by
  classical
  unfold canonicalUnitaryComplementCoordinateMass
  unfold canonicalUnitaryComplementColumnMass
  calc
    (∑ i : Fin k, if m ≤ (i : ℕ) then
        ∑ j : Fin k, if (j : ℕ) < m then Complex.normSq (U.1 i j) else 0
      else 0) =
        ∑ i : Fin k, ∑ j : Fin k,
          if m ≤ (i : ℕ) ∧ (j : ℕ) < m then
            Complex.normSq (U.1 i j) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases him : m ≤ (i : ℕ)
      · simp [him]
      · simp [him]
    _ = ∑ j : Fin k, ∑ i : Fin k,
          if m ≤ (i : ℕ) ∧ (j : ℕ) < m then
            Complex.normSq (U.1 i j) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin k, if (j : ℕ) < m then
          ∑ i : Fin k, if m ≤ (i : ℕ) then
            Complex.normSq (U.1 i j) else 0 else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hjm : (j : ℕ) < m
      · simp [hjm]
      · simp [hjm]
    _ = ∑ j : {j : Fin k // (j : ℕ) < m},
          ∑ i : Fin k, if m ≤ (i : ℕ) then
            Complex.normSq (U.1 i j.1) else 0 := by
      rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp
    _ = ∑ j : Fin m, ∑ i : Fin k, if m ≤ (i : ℕ) then
          Complex.normSq (U.1 i (Fin.castLE hmk j)) else 0 := by
      symm
      simpa only [Fin.castLEquiv_apply] using
        (Equiv.sum_comp (Fin.castLEquiv hmk)
          (fun j : {j : Fin k // (j : ℕ) < m} =>
            ∑ i : Fin k, if m ≤ (i : ℕ) then
              Complex.normSq (U.1 i j.1) else 0))

/-- The complement of the canonical projector is the complementary
coordinate diagonal. -/
theorem one_sub_canonicalRankMProjectorMatrix (k m : ℕ) :
    1 - canonicalRankMProjectorMatrix k m =
      Matrix.diagonal (fun i : Fin k => if m ≤ (i : ℕ) then (1 : ℂ) else 0) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : (i : ℕ) < m
    · simp [canonicalRankMProjectorMatrix, canonicalRankMProjectorDiagonal,
        hi, Nat.not_le.mpr hi]
    · have hmi : m ≤ (i : ℕ) := Nat.le_of_not_gt hi
      simp [canonicalRankMProjectorMatrix, canonicalRankMProjectorDiagonal,
        hi, hmi]
  · simp [canonicalRankMProjectorMatrix, hij]

/-- A diagonal entry of the conjugated canonical projector is the squared
mass of the corresponding row in the first `m` columns. -/
theorem unitaryConjugateCanonical_diagonal_eq_coordinateMass
    (k m : ℕ) (U : unitary (Matrix (Fin k) (Fin k) ℂ)) (i : Fin k) :
    unitaryConjugateMatrix U (canonicalRankMProjectorMatrix k m) i i =
      ∑ j : Fin k,
        if (j : ℕ) < m then (Complex.normSq (U.1 i j) : ℂ) else 0 := by
  rw [unitaryConjugateMatrix_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [canonicalRankMProjectorMatrix, Matrix.mul_diagonal]
  by_cases hjm : (j : ℕ) < m
  · simp only [canonicalRankMProjectorDiagonal, hjm, if_pos, mul_one,
      Matrix.star_apply]
    exact Complex.mul_conj (U.1 i j)
  · simp [canonicalRankMProjectorDiagonal, hjm]

theorem canonicalUnitaryComplementOverlap_eq_coordinateMass
    (k m : ℕ) (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    canonicalUnitaryComplementOverlap k m hmk U =
      canonicalUnitaryComplementCoordinateMass k m U := by
  change (((1 - canonicalRankMProjectorMatrix k m) *
    unitaryConjugateMatrix U (canonicalRankMProjectorMatrix k m)).trace.re) = _
  rw [one_sub_canonicalRankMProjectorMatrix]
  rw [Matrix.trace]
  unfold canonicalUnitaryComplementCoordinateMass
  simp only [Matrix.diag_apply, Matrix.diagonal_mul]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [unitaryConjugateCanonical_diagonal_eq_coordinateMass]
  by_cases him : m ≤ (i : ℕ)
  · simp only [him, if_pos, one_mul]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjm : (j : ℕ) < m
    · simp [hjm]
    · simp [hjm]
  · simp [him]

/-- The invariant projector overlap in the exact column-sum form used by
the spectral Jensen argument. -/
theorem canonicalUnitaryComplementOverlap_eq_sum_columnMass
    (k m : ℕ) (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    canonicalUnitaryComplementOverlap k m hmk U =
      ∑ j : Fin m, canonicalUnitaryComplementColumnMass k m hmk U j := by
  rw [canonicalUnitaryComplementOverlap_eq_coordinateMass k m hmk U]
  exact canonicalUnitaryComplementCoordinateMass_eq_sum_columnMass k m hmk U

end

end TomographyOracleCore
