import TomographyOracleCore.Revision.AlgorithmResourcesPowerShift
import TomographyOracleCore.Revision.FinitePrecisionProjector

/-! A proved executable rational linear-optimization direction for density matrices. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixReduction MatrixSolver FinitePrecision
open scoped BigOperators ComplexOrder

noncomputable section

variable {d : ℕ}

theorem trace_normalizedProjector_mul_eq_complexRayleigh
    (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ) :
    (normalizedProjector (WithLp.toLp 2 v) * A).trace.re = complexRayleigh A v := by
  rw [Matrix.trace_mul_comm, trace_mul_normalizedProjector_re_eq_rayleigh,
    complexRayleigh_eq_rayleighQuotient]

theorem qBestPowerColumn_nonzero
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).PosDef) (k : ℕ) (hk : d ≤ k) :
    qPowerColumn A k (qBestPowerColumn hD A k) ≠ 0 := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hD
  have hp : 0 < matrixOperatorNorm (castQMatrix A) := by
    obtain ⟨i, hi⟩ := exists_extreme_eigenvalue (castQMatrix A) hA.isHermitian
    rw [hi, abs_of_pos (hA.eigenvalues_pos i)]
    exact hA.eigenvalues_pos i
  have happrox := qBestPowerColumn_operatorNorm_bound hD A hA k
  intro hz
  have hzq : qRayleigh A (qPowerColumn A k (qBestPowerColumn hD A k)) = 0 := by
    simp [qRayleigh, hz, qVectorNormSq]
  rw [hzq, Rat.cast_zero] at happrox
  have hd : (d : ℝ) < ((2 * k : ℕ) + 1 : ℝ) := by
    exact_mod_cast (show d < 2 * k + 1 by omega)
  have hdpos : 0 < ((2 * k : ℕ) + 1 : ℝ) := by positivity
  have hsmall : (d : ℝ) * matrixOperatorNorm (castQMatrix A) /
      ((2 * k : ℕ) + 1 : ℝ) < matrixOperatorNorm (castQMatrix A) := by
    apply (div_lt_iff₀ hdpos).mpr
    nlinarith
  linarith

theorem qMinimumDirection_nonzero
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) :
    qMinimumDirection hD A delta ≠ 0 :=
  qBestPowerColumn_nonzero hD _ (qShiftMinus_posDef A hA) _
    (qPowerIterationCount_ge_dimension d (qShiftBound A) delta)

theorem qMinimumDirection_shift_accuracy
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta) :
    matrixOperatorNorm ((qShiftBound A : ℝ) • 1 - castQMatrix A) - (delta : ℝ) ≤
      ((qShiftBound A : ℝ) • 1 - castQMatrix A).toEuclideanLin.toContinuousLinearMap.rayleighQuotient
        (WithLp.toLp 2 (castQVector (qMinimumDirection hD A delta))) := by
  let k := qPowerIterationCount d (qShiftBound A) delta
  have hden : 0 < ((2 * k : ℕ) + 1 : ℝ) := by positivity
  have hbudget := qPowerIterationCount_budget d (qShiftBound A) delta hdelta
  have hn := qShiftMinus_norm_le hD A
  have herr : (d : ℝ) * matrixOperatorNorm (castQMatrix (qShiftMinus A)) /
      ((2 * k : ℕ) + 1 : ℝ) ≤ (delta : ℝ) := by
    apply (div_le_iff₀ hden).mpr
    calc
      _ ≤ (d : ℝ) * (2 * (qShiftBound A : ℝ)) :=
        mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _)
      _ ≤ _ := by simpa [k, mul_comm] using hbudget
  have happrox := qBestPowerColumn_operatorNorm_bound hD (qShiftMinus A)
    (qShiftMinus_posDef A hA) k
  have hfinal : matrixOperatorNorm (castQMatrix (qShiftMinus A)) - (delta : ℝ) ≤
      (qRayleigh (qShiftMinus A) (qMinimumDirection hD A delta) : ℝ) := by
    dsimp [qMinimumDirection]
    dsimp [k] at happrox herr
    linarith
  rw [← castQVector_rayleigh, complexRayleigh_eq_rayleighQuotient,
    castQMatrix_shiftMinus] at hfinal
  exact hfinal

/-- The actual computed Gaussian-rational vector supplies a feasible
rank-one atom whose linear objective is within `delta` of every density.
There is no assumed eigenvector or optimization oracle in this theorem. -/
theorem qMinimumDirection_linear_minimizer
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta)
    (rho : DensityOperator (Fin d)) :
    (normalizedProjector
        (WithLp.toLp 2 (castQVector (qMinimumDirection hD A delta))) * castQMatrix A).trace.re ≤
      (rho.matrix * castQMatrix A).trace.re + (delta : ℝ) := by
  have hv : WithLp.toLp 2 (castQVector (qMinimumDirection hD A delta)) ≠ 0 := by
    intro hz
    apply qMinimumDirection_nonzero hD A hA delta
    apply (castQVector_eq_zero _).mp
    exact congrArg WithLp.ofLp hz
  exact normalizedProjector_linear_minimizer_of_shift _ _ hv (qShiftBound A) delta
    (qMinimumDirection_shift_accuracy hD A hA delta hdelta) rho

theorem qMinimumDirection_compare_vector
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).IsHermitian) (delta : ℚ) (hdelta : 0 < delta)
    (w : Fin d → ℂ) (hw : w ≠ 0) :
    (qRayleigh A (qMinimumDirection hD A delta) : ℝ) ≤
      complexRayleigh (castQMatrix A) w + (delta : ℝ) := by
  have hw' : (WithLp.toLp 2 w : EuclideanSpace ℂ (Fin d)) ≠ 0 := by
    intro hz
    apply hw
    exact congrArg WithLp.ofLp hz
  have h := qMinimumDirection_linear_minimizer hD A hA delta hdelta
    (normalizedProjectorDensity (WithLp.toLp 2 w) hw')
  change (normalizedProjector (WithLp.toLp 2 (castQVector (qMinimumDirection hD A delta))) *
      castQMatrix A).trace.re ≤
      (normalizedProjector (WithLp.toLp 2 w) * castQMatrix A).trace.re + _ at h
  simpa only [trace_normalizedProjector_mul_eq_complexRayleigh, castQVector_rayleigh] using h

#print axioms qMinimumDirection_linear_minimizer

end
end TomographyOracleCore.Revision.AlgorithmResources
