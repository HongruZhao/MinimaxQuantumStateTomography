import TomographyOracleCore.Revision.AlgorithmResourcesPowerMinimum

/-! Executable signed approximate extreme directions, without a spectral gap assumption. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixReduction MatrixSolver FinitePrecision
open scoped BigOperators ComplexOrder

variable {d : ℕ}

/-- Compare the two computed rational quotients using exact rational order. -/
def qSignedSpectralDirection (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    (Fin d → QComplex) × ℚ :=
  let vp := qMinimumDirection hD (-A) delta
  let vm := qMinimumDirection hD A delta
  if -qRayleigh A vm ≤ qRayleigh A vp then (vp, 1) else (vm, -1)

def qSignedScore (A : Matrix (Fin d) (Fin d) QComplex)
    (direction : (Fin d → QComplex) × ℚ) : ℚ :=
  direction.2 * qRayleigh A direction.1

theorem qSignedScore_ge_plus (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    qRayleigh A (qMinimumDirection hD (-A) delta) ≤
      qSignedScore A (qSignedSpectralDirection hD A delta) := by
  unfold qSignedScore qSignedSpectralDirection
  dsimp only
  split_ifs with h <;> simp only [one_mul, neg_one_mul]
  · exact le_rfl
  · linarith

theorem qSignedScore_ge_minus (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    -qRayleigh A (qMinimumDirection hD A delta) ≤
      qSignedScore A (qSignedSpectralDirection hD A delta) := by
  unfold qSignedScore qSignedSpectralDirection
  dsimp only
  split_ifs with h <;> simp only [one_mul, neg_one_mul]
  · exact h
  · exact le_rfl

theorem qSignedSpectralDirection_sign (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (delta : ℚ) :
    |(qSignedSpectralDirection hD A delta).2| = 1 := by
  unfold qSignedSpectralDirection
  dsimp only
  split_ifs <;> norm_num

noncomputable section

theorem complexRayleigh_neg (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    complexRayleigh (-A) v = -complexRayleigh A v := by
  simp [complexRayleigh, complexQuadratic, Matrix.neg_mulVec, mul_neg,
    Finset.sum_neg_distrib, neg_div]

theorem qRayleigh_neg (A : Matrix (Fin d) (Fin d) QComplex) (v : Fin d → QComplex) :
    qRayleigh (-A) v = -qRayleigh A v := by
  apply Rat.cast_injective (α := ℝ)
  rw [← castQVector_rayleigh, castQMatrix_neg, complexRayleigh_neg,
    castQVector_rayleigh, Rat.cast_neg]

theorem qSignedSpectralDirection_nonzero
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) :
    (qSignedSpectralDirection hD A delta).1 ≠ 0 := by
  have hn : (castQMatrix (-A)).IsHermitian := by simpa using hA.neg
  unfold qSignedSpectralDirection
  dsimp only
  split_ifs
  · exact qMinimumDirection_nonzero hD (-A) hn delta
  · exact qMinimumDirection_nonzero hD A hA delta

/-- The returned vector and sign approximate the absolute spectral extreme
of the literal input Hermitian matrix, using only rational computations. -/
theorem qSignedSpectralDirection_accuracy
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta) :
    matrixOperatorNorm (castQMatrix A) - (delta : ℝ) ≤
      (qSignedScore A (qSignedSpectralDirection hD A delta) : ℝ) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hD
  obtain ⟨j, hj⟩ := exists_extreme_eigenvalue (castQMatrix A) hA
  let w : Fin d → ℂ := fun i => hA.eigenvectorBasis j i
  have hw : w ≠ 0 := by
    intro hz
    have hz' : hA.eigenvectorBasis j = 0 := by ext i; exact congrFun hz i
    have hnorm := hA.eigenvectorBasis.norm_eq_one j
    rw [hz', norm_zero] at hnorm
    norm_num at hnorm
  have hr : complexRayleigh (castQMatrix A) w = hA.eigenvalues j := by
    rw [complexRayleigh_eq_rayleighQuotient]
    have h := signedRayleigh_eigenvector (castQMatrix A) hA j 1
    simpa [signedRayleigh, w] using h
  have hn : (castQMatrix (-A)).IsHermitian := by simpa using hA.neg
  have hm := qMinimumDirection_compare_vector hD A hA delta hdelta w hw
  rw [hr] at hm
  have hp := qMinimumDirection_compare_vector hD (-A) hn delta hdelta w hw
  rw [qRayleigh_neg, Rat.cast_neg, castQMatrix_neg, complexRayleigh_neg, hr] at hp
  have hsp : (qRayleigh A (qMinimumDirection hD (-A) delta) : ℝ) ≤
      (qSignedScore A (qSignedSpectralDirection hD A delta) : ℝ) :=
    Rat.cast_le.mpr (qSignedScore_ge_plus hD A delta)
  have hsm : -(qRayleigh A (qMinimumDirection hD A delta) : ℝ) ≤
      (qSignedScore A (qSignedSpectralDirection hD A delta) : ℝ) := by
    exact_mod_cast qSignedScore_ge_minus hD A delta
  rw [hj]
  by_cases hs : 0 ≤ hA.eigenvalues j
  · rw [abs_of_nonneg hs]
    linarith
  · rw [abs_of_neg (lt_of_not_ge hs)]
    linarith

/-- Direct interface for the already proved epsilon-subgradient theorem. -/
theorem qSignedSpectralDirection_signedRayleigh
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta) :
    matrixOperatorNorm (castQMatrix A) - (delta : ℝ) ≤
      signedRayleigh (castQMatrix A)
        (WithLp.toLp 2 (castQVector (qSignedSpectralDirection hD A delta).1))
        ((qSignedSpectralDirection hD A delta).2 : ℝ) := by
  rw [signedRayleigh, ← complexRayleigh_eq_rayleighQuotient, castQVector_rayleigh]
  simpa only [qSignedScore, Rat.cast_mul] using
    qSignedSpectralDirection_accuracy hD A hA delta hdelta

#print axioms qSignedSpectralDirection_signedRayleigh

end
end TomographyOracleCore.Revision.AlgorithmResources
