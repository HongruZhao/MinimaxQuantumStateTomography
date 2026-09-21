import TomographyOracleCore.Revision.PhysicalMinimaxRates

namespace TomographyOracleCore.Revision.PhysicalMinimax

open MeasureTheory MatrixReduction
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

noncomputable section

/-- Real averaging and identity calibration preserve Hermiticity. -/
theorem empiricalForwardMatrix_isHermitian {D T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ)
    (hsample : ∀ t, (sample t).IsHermitian) :
    (empiricalForwardMatrix sample).IsHermitian := by
  unfold empiricalForwardMatrix Matrix.IsHermitian
  simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    star_trivial, Matrix.conjTranspose_sum, Matrix.conjTranspose_one]
  congr 2
  exact Finset.sum_congr rfl (fun t _ => hsample t)

/-- Every possible physical sample yields a Hermitian algorithm input. -/
theorem empiricalForwardMatrix_isHermitian_of_mem_possibleSamples
    {D T : ℕ} {E : Type*} [Fintype E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (sample : Fin T → Matrix (Fin D) (Fin D) ℂ)
    (hsample : sample ∈ possibleSamples U T) :
    (empiricalForwardMatrix sample).IsHermitian := by
  rcases hsample with ⟨labels, rfl⟩
  apply empiricalForwardMatrix_isHermitian
  intro t
  exact (finiteUnitaryMeasurementProjector_posSemidef (U (labels t).1) (labels t).2).isHermitian

/-- A solver guarded on Hermitian inputs always takes its intended branch
under the actual periodic Born experiment. -/
theorem ae_empiricalForwardMatrix_isHermitian
    {n K T : ℕ} (h : ChoKimBlockCondition n K)
    (rho : DensityOperator (Fin (2 ^ n))) :
    ∀ᵐ sample ∂periodicSampleLaw h T rho,
      (empiricalForwardMatrix sample).IsHermitian := by
  have hs := ae_mem_possibleSamples (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho
  exact hs.mono fun sample hsample =>
    empiricalForwardMatrix_isHermitian_of_mem_possibleSamples _ sample hsample

end
end TomographyOracleCore.Revision.PhysicalMinimax
