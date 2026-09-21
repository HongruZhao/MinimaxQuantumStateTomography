import TomographyOracleCore.Revision.AlgorithmResourcesPowerArithmetic
import TomographyOracleCore.Revision.AlgorithmResourcesPowerBound

/-! The executable rational column search satisfies the matrix spectral bound. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix
open scoped BigOperators ComplexOrder

noncomputable section

variable {d : ℕ}

def castQVector (v : Fin d → QComplex) : Fin d → ℂ := qComplexToComplex ∘ v

@[simp] theorem castQVector_apply (v : Fin d → QComplex) (i : Fin d) :
    castQVector v i = qComplexToComplex (v i) := rfl

theorem castQVector_eq_zero (v : Fin d → QComplex) : castQVector v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    apply qComplexToComplex_injective
    simpa using congrFun h i
  · rintro rfl
    ext i
    simp

@[simp] theorem castQMatrix_mulVec (A : Matrix (Fin d) (Fin d) QComplex)
    (v : Fin d → QComplex) : castQMatrix A *ᵥ castQVector v = castQVector (A *ᵥ v) := by
  ext i
  simp only [Matrix.mulVec, dotProduct, castQVector_apply, castQMatrix_apply,
    map_sum, map_mul]

@[simp] theorem castQVector_normSq (v : Fin d → QComplex) :
    complexVectorNormSq (castQVector v) = (qVectorNormSq v : ℝ) := by
  simp only [complexVectorNormSq, castQVector_apply, qComplexToComplex_normSq,
    qVectorNormSq, Rat.cast_sum]

@[simp] theorem castQVector_quadratic (A : Matrix (Fin d) (Fin d) QComplex)
    (v : Fin d → QComplex) : complexQuadratic (castQMatrix A) (castQVector v) =
      ((∑ i, star (v i) * (A *ᵥ v) i).re : ℝ) := by
  unfold complexQuadratic
  rw [castQMatrix_mulVec]
  have he : (∑ i, star (castQVector v i) * castQVector (A *ᵥ v) i) =
      qComplexToComplex (∑ i, star (v i) * (A *ᵥ v) i) := by
    simp only [castQVector_apply, map_sum, map_mul, qComplexToComplex_star]
  rw [he, qComplexToComplex_re]

@[simp] theorem castQVector_rayleigh (A : Matrix (Fin d) (Fin d) QComplex)
    (v : Fin d → QComplex) : complexRayleigh (castQMatrix A) (castQVector v) =
      (qRayleigh A v : ℝ) := by
  simp [complexRayleigh, qRayleigh]

@[simp] theorem castQVector_powerColumn (A : Matrix (Fin d) (Fin d) QComplex)
    (k : ℕ) (j : Fin d) :
    castQVector (qPowerColumn A k j) = powerColumn (castQMatrix A) k j := by
  ext i
  change castQMatrix (A ^ k) i j = (castQMatrix A ^ k) i j
  rw [castQMatrix_pow]

/-- The actual executable maximizer attains a gap-free additive approximation
to the top eigenvalue. The only hypotheses are properties of the input matrix. -/
theorem qBestPowerColumn_spectral_bound
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).PosSemidef) (k : ℕ) (j : Fin d)
    (hmax : ∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues j)
    (hpos : 0 < hA.isHermitian.eigenvalues j) :
    hA.isHermitian.eigenvalues j -
      (d : ℝ) * hA.isHermitian.eigenvalues j / ((2 * k : ℕ) + 1 : ℝ) ≤
      (qRayleigh A (qPowerColumn A k (qBestPowerColumn hD A k)) : ℝ) := by
  have hc : ∀ i, complexRayleigh (castQMatrix A) (powerColumn (castQMatrix A) k i) ≤
      (qRayleigh A (qPowerColumn A k (qBestPowerColumn hD A k)) : ℝ) := by
    intro i
    rw [← castQVector_powerColumn, castQVector_rayleigh]
    exact_mod_cast qBestPowerColumn_max hD A k i
  simpa only [Fintype.card_fin] using
    largest_eigenvalue_le_column_bound (castQMatrix A) hA k j hmax hpos _ hc

#print axioms qBestPowerColumn_spectral_bound

end
end TomographyOracleCore.Revision.AlgorithmResources
