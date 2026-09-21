import TomographyOracleCore.Revision.MatrixSolverInexactImplementations
import TomographyOracleCore.Revision.PhysicalMinimaxHermitian

/-! Mathematical extension of the executable rational solver to the complex
sample space used by the physical experiment. On encoded Hermitian input it
is exactly the computed rational solver. A compact minimizer is used only
outside that input class; the extension is not an arbitrary-complex input
decoding algorithm.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

theorem castQMatrix_injective :
    Function.Injective (castQMatrix : Matrix (Fin D) (Fin D) QComplex →
      Matrix (Fin D) (Fin D) ℂ) := by
  intro A B h
  funext i j
  apply qComplexToComplex_injective
  exact congrArg (fun X : Matrix (Fin D) (Fin D) ℂ => X i j) h

noncomputable def guardedRationalSolve (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (gamma : ℚ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) := by
  classical
  exact if hQ : Q.IsHermitian then
    if hR : ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = Q then
      rationalDensity (rationalMatrixSolve hD M hR.choose gamma)
        (rationalMatrixSolve_feasible hD M hR.choose gamma hgamma)
    else PhysicalMinimax.forwardMinimizer hD U Q
  else PhysicalMinimax.forwardMinimizer hD U Q

/-- On an encoded Hermitian matrix the extension agrees exactly with the
executable rational implementation, including its actual output matrix. -/
theorem guardedRationalSolve_eq_encoded (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (gamma : ℚ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian) :
    guardedRationalSolve hD U M gamma hgamma (castQMatrix Q) =
      rationalDensity (rationalMatrixSolve hD M Q gamma)
        (rationalMatrixSolve_feasible hD M Q gamma hgamma) := by
  classical
  have hR : ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = castQMatrix Q := ⟨Q, rfl⟩
  have hchoose : hR.choose = Q := castQMatrix_injective hR.choose_spec
  simp only [guardedRationalSolve, dif_pos hQ, dif_pos hR, hchoose]

theorem guardedRationalSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (guardedRationalSolve hD U M gamma hgamma Q).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) +
          (gamma : ℝ) := by
  classical
  by_cases hQ : Q.IsHermitian
  · by_cases hR : ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = Q
    · have hencoded : (castQMatrix hR.choose).IsHermitian := by rw [hR.choose_spec]; exact hQ
      have ht := rationalMatrixSolve_fit hD U M hM hR.choose hencoded gamma hgamma hgamma_le sigma
      simpa only [guardedRationalSolve, dif_pos hQ, dif_pos hR, rationalDensity,
        hR.choose_spec] using ht
    · simp only [guardedRationalSolve, dif_pos hQ, dif_neg hR]
      exact (PhysicalMinimax.forwardMinimizer_le hD U Q sigma).trans
        (le_add_of_nonneg_right (Rat.cast_pos.mpr hgamma).le)
  · simp only [guardedRationalSolve, dif_neg hQ]
    exact (PhysicalMinimax.forwardMinimizer_le hD U Q sigma).trans
      (le_add_of_nonneg_right (Rat.cast_pos.mpr hgamma).le)

noncomputable def guardedRationalCalibratedSolve (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (L : RationalMatrixOperator D)
    (gamma : ℚ) (hgamma : 0 < gamma) :
    Matrix (Fin D) (Fin D) ℂ → DensityOperator (Fin D) :=
  guardedRationalSolve hD U (rationalProjectiveFromCalibrated L) gamma hgamma

theorem guardedRationalCalibratedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (L : RationalMatrixOperator D)
    (hL : ∀ A, castQMatrix (L A) = finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A))
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (guardedRationalCalibratedSolve hD U L gamma hgamma Q).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) +
          (gamma : ℝ) :=
  guardedRationalSolve_fit hD U _ (cast_rationalProjectiveFromCalibrated U L hL)
    gamma hgamma hgamma_le Q sigma

theorem guardedRationalCalibratedSolve_statistical_fit (hD : 0 < D) {T : ℕ} (hT : 0 < T)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (L : RationalMatrixOperator D)
    (hL : ∀ A, castQMatrix (L A) = finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A))
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (guardedRationalCalibratedSolve hD U L (rationalSampleTolerance T)
        (rationalSampleTolerance_pos hT) Q).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) +
          Real.sqrt ((D : ℝ) / (T : ℝ)) :=
  (guardedRationalCalibratedSolve_fit hD U L hL _ (rationalSampleTolerance_pos hT)
    (rationalSampleTolerance_le_one hT) Q sigma).trans
      (add_le_add le_rfl (rationalSampleTolerance_le_statistical hD hT))

theorem cast_rationalEmpiricalForward_eq {T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalEmpiricalForward sample) =
      PhysicalMinimax.empiricalForwardMatrix (fun t => castQMatrix (sample t)) :=
  cast_rationalEmpiricalForward sample

theorem rationalEmpiricalForward_isHermitian {T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) QComplex)
    (hsample : ∀ t, (castQMatrix (sample t)).IsHermitian) :
    (castQMatrix (rationalEmpiricalForward sample)).IsHermitian := by
  rw [cast_rationalEmpiricalForward_eq]
  exact PhysicalMinimax.empiricalForwardMatrix_isHermitian _ hsample

def rationalTranscriptForward {T : ℕ}
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (labels : Fin T → E × Fin D) : Matrix (Fin D) (Fin D) QComplex :=
  rationalEmpiricalForward (fun t => P (labels t).1 (labels t).2)

theorem cast_rationalTranscriptForward {T : ℕ}
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (hP : ∀ e b, castQMatrix (P e b) = finiteUnitaryMeasurementProjector (U e) b)
    (labels : Fin T → E × Fin D) :
    castQMatrix (rationalTranscriptForward P labels) =
      PhysicalMinimax.empiricalForwardMatrix
        (fun t => finiteUnitaryMeasurementProjector (U (labels t).1) (labels t).2) := by
  simp only [rationalTranscriptForward, cast_rationalEmpiricalForward_eq, hP]

/-- A physical transcript consisting of rationally encoded projectors has
an exactly rational empirical input. The conclusion states existence of
an encoding; conversion of arbitrary complex input is outside its scope. -/
theorem empiricalForwardMatrix_has_rational_encoding {T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ)
    (hsample : ∀ t, ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = sample t) :
    ∃ Q : Matrix (Fin D) (Fin D) QComplex,
      castQMatrix Q = PhysicalMinimax.empiricalForwardMatrix sample := by
  classical
  choose A hA using hsample
  refine ⟨rationalEmpiricalForward A, ?_⟩
  simp only [cast_rationalEmpiricalForward_eq, hA]

#print axioms guardedRationalSolve_fit
#print axioms guardedRationalSolve_eq_encoded
#print axioms guardedRationalCalibratedSolve_statistical_fit

end TomographyOracleCore.Revision.MatrixSolver
