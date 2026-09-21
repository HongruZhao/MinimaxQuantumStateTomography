import TomographyOracleCore.Revision.ConstantRationalSolver
import TomographyOracleCore.Revision.MatrixSolverInexactRisk

namespace TomographyOracleCore.Revision.MatrixSolver
open MeasureTheory MatrixReduction AlgorithmResources FinitePrecision PhysicalMinimax
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

noncomputable def guardedRationalMixedSolve (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (gamma : ℚ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) := by
  classical
  exact if hQ : Q.IsHermitian then
    if hR : ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = Q then
      rationalDensity (rationalMixedMatrixSolve hD M hR.choose gamma)
        (rationalMixedMatrixSolve_feasible hD M hR.choose gamma hgamma)
    else PhysicalMinimax.forwardMinimizer hD U Q
  else PhysicalMinimax.forwardMinimizer hD U Q

/-- On an encoded Hermitian matrix the extension agrees exactly with the
executable rational implementation, including its actual output matrix. -/
theorem guardedRationalMixedSolve_eq_encoded (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (gamma : ℚ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) QComplex) (hQ : (castQMatrix Q).IsHermitian) :
    guardedRationalMixedSolve hD U M gamma hgamma (castQMatrix Q) =
      rationalDensity (rationalMixedMatrixSolve hD M Q gamma)
        (rationalMixedMatrixSolve_feasible hD M Q gamma hgamma) := by
  classical
  have hR : ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = castQMatrix Q := ⟨Q, rfl⟩
  have hchoose : hR.choose = Q := castQMatrix_injective hR.choose_spec
  simp only [guardedRationalMixedSolve, dif_pos hQ, dif_pos hR, hchoose]

theorem guardedRationalMixedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (M : RationalMatrixOperator D)
    (hM : ∀ A, castQMatrix (M A) = finiteUnitaryProjectiveLinearChannel U (castQMatrix A))
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (guardedRationalMixedSolve hD U M gamma hgamma Q).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) +
          (gamma : ℝ) := by
  classical
  by_cases hQ : Q.IsHermitian
  · by_cases hR : ∃ A : Matrix (Fin D) (Fin D) QComplex, castQMatrix A = Q
    · have hencoded : (castQMatrix hR.choose).IsHermitian := by rw [hR.choose_spec]; exact hQ
      have ht := rationalMixedMatrixSolve_fit hD U M hM hR.choose hencoded gamma hgamma hgamma_le sigma
      simpa only [guardedRationalMixedSolve, dif_pos hQ, dif_pos hR, rationalDensity,
        hR.choose_spec] using ht
    · simp only [guardedRationalMixedSolve, dif_pos hQ, dif_neg hR]
      exact (PhysicalMinimax.forwardMinimizer_le hD U Q sigma).trans
        (le_add_of_nonneg_right (Rat.cast_pos.mpr hgamma).le)
  · simp only [guardedRationalMixedSolve, dif_neg hQ]
    exact (PhysicalMinimax.forwardMinimizer_le hD U Q sigma).trans
      (le_add_of_nonneg_right (Rat.cast_pos.mpr hgamma).le)


/-- Computable periodic solver using the reduced outer schedule. -/
def rationalMixedPeriodicSolve (n K : ℕ) (hdiv : K ∣ n)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (gamma : ℚ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex :=
  rationalMixedMatrixSolve (by positivity)
    (rationalProjectiveFromCalibrated (qPeriodicCalibratedChannel n K hdiv)) Q gamma

theorem rationalMixedPeriodicSolve_fit (n K : ℕ) (hdiv : K ∣ n) (hK : 0 < K)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (hQ : (castQMatrix Q).IsHermitian)
    (gamma : ℚ) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (sigma : DensityOperator (Fin (2 ^ n))) :
    matrixOperatorNorm (castQMatrix Q -
      finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (castQMatrix (rationalMixedPeriodicSolve n K hdiv Q gamma))) ≤
      matrixOperatorNorm (castQMatrix Q -
        finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
          sigma.matrix) + (gamma : ℝ) :=
  rationalMixedMatrixSolve_fit (by positivity) _ _
    (cast_rationalProjectiveFromCalibrated _ _ (qPeriodicCalibratedChannel_correct n K hdiv hK))
    Q hQ gamma hgamma hgamma_le sigma

noncomputable def guardedRationalMixedPeriodicSolve (n K T : ℕ) (hdiv : K ∣ n) (hT : 0 < T) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)) :=
  guardedRationalMixedSolve (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
    (rationalProjectiveFromCalibrated (qPeriodicCalibratedChannel n K hdiv))
    (rationalSampleTolerance T) (rationalSampleTolerance_pos hT)

theorem guardedRationalMixedPeriodicSolve_fit (n K T : ℕ)
    (hdiv : K ∣ n) (hK : 0 < K) (hT : 0 < T)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) (sigma : DensityOperator (Fin (2 ^ n))) :
    matrixOperatorNorm (Q -
      finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (guardedRationalMixedPeriodicSolve n K T hdiv hT Q).matrix) ≤
      matrixOperatorNorm (Q -
        finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
          sigma.matrix) + Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) :=
  (guardedRationalMixedSolve_fit (by positivity) _ _
    (cast_rationalProjectiveFromCalibrated _ _ (qPeriodicCalibratedChannel_correct n K hdiv hK))
    _ (rationalSampleTolerance_pos hT) (rationalSampleTolerance_le_one hT) Q sigma).trans
      (add_le_add le_rfl (rationalSampleTolerance_le_statistical (by positivity) hT))

theorem guardedRationalMixedPeriodicSolve_eq_encoded (n K T : ℕ)
    (hdiv : K ∣ n) (hT : 0 < T)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) (hQ : (castQMatrix Q).IsHermitian) :
    (guardedRationalMixedPeriodicSolve n K T hdiv hT (castQMatrix Q)).matrix =
      castQMatrix (rationalMixedPeriodicSolve n K hdiv Q (rationalSampleTolerance T)) := by
  exact congrArg DensityOperator.matrix (guardedRationalMixedSolve_eq_encoded (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
    (rationalProjectiveFromCalibrated (qPeriodicCalibratedChannel n K hdiv))
    (rationalSampleTolerance T) (rationalSampleTolerance_pos hT) Q hQ)

noncomputable section
theorem guardedRationalMixedPeriodicSolve_eq_on_possibleSamples (n K T : ℕ)
    (hdiv : K ∣ n) (hT : 0 < T)
    (sample : Fin T → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hsample : sample ∈ possibleSamples (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) T) :
    ∃ Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
      castQMatrix Q = empiricalForwardMatrix sample ∧
      (guardedRationalMixedPeriodicSolve n K T hdiv hT (empiricalForwardMatrix sample)).matrix =
        castQMatrix (rationalMixedPeriodicSolve n K hdiv Q (rationalSampleTolerance T)) := by
  have hencoding : ∀ t, ∃ A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
      castQMatrix A = sample t := by
    rcases hsample with ⟨labels, rfl⟩
    intro t
    exact choKim_projector_has_rational_encoding hdiv (labels t).1 (labels t).2
  obtain ⟨Q, hQ⟩ := empiricalForwardMatrix_has_rational_encoding sample hencoding
  have hHerm := empiricalForwardMatrix_isHermitian_of_mem_possibleSamples
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) sample hsample
  refine ⟨Q, hQ, ?_⟩
  rw [← hQ]
  exact guardedRationalMixedPeriodicSolve_eq_encoded n K T hdiv hT Q (by rw [hQ]; exact hHerm)

theorem ae_guardedRationalMixedPeriodicSolve_computed {n K T : ℕ}
    (h : ChoKimBlockCondition n K) (hT : 0 < T) (rho : DensityOperator (Fin (2 ^ n))) :
    ∀ᵐ sample ∂periodicSampleLaw h T rho,
      ∃ Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
        castQMatrix Q = empiricalForwardMatrix sample ∧
        (guardedRationalMixedPeriodicSolve n K T h.block_dvd hT (empiricalForwardMatrix sample)).matrix =
          castQMatrix (rationalMixedPeriodicSolve n K h.block_dvd Q (rationalSampleTolerance T)) := by
  have hs := ae_mem_possibleSamples (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho
  exact hs.mono fun sample hsample =>
    guardedRationalMixedPeriodicSolve_eq_on_possibleSamples n K T h.block_dvd hT sample hsample


end
end TomographyOracleCore.Revision.MatrixSolver
