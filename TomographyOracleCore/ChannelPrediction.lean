import TomographyOracleCore.ForwardGeometry
import TomographyOracleCore.HaarChannel
import TomographyOracleCore.DensityGrid

namespace TomographyOracleCore
open MatrixReduction

/-- In positive complex dimension, any quarter-net satisfying the covering
property is nonempty. -/
theorem complex_quarterNet_nonempty_of_pos
    (D : ℕ) (hD : 0 < D)
    (net : Finset (EuclideanSpace ℂ (Fin D)))
    (hcover : ∀ x : EuclideanSpace ℂ (Fin D), ‖x‖ = 1 →
      ∃ u ∈ net, ‖x - u‖ ≤ (1 : ℝ) / 4) :
    net.Nonempty := by
  let i₀ : Fin D := ⟨0, hD⟩
  let x : EuclideanSpace ℂ (Fin D) :=
    EuclideanSpace.single i₀ (1 : ℂ)
  have hx : ‖x‖ = 1 := by simp [x]
  obtain ⟨u, hu, _hxu⟩ := hcover x hx
  exact ⟨u, hu⟩

/-- The energy for the identity forward map is exactly the squared Hermitian
Frobenius norm. -/
theorem hermitianForwardEnergy_sub_eq_frobenius_sq
    { ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma rho : DensityOperator ι) :
    hermitianForwardEnergy sigma rho (sigma.matrix - rho.matrix) =
      hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
        (sigma.sub_isHermitian rho) ^ 2 := by
  have htrace := trace_sq_eq_hermitianFrobeniusSq
    (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho)
  have hre := congrArg Complex.re htrace
  simpa [hermitianForwardEnergy, hermitianFrobeniusNorm_sq] using hre

/-- Quadratic prediction after a Hermiticity-preserving forward channel. -/
noncomputable def channelQuadraticPrediction
    (channel : DensityOperator (Fin D) → Matrix (Fin D) (Fin D) ℂ)
    (state : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  hermitianQuadraticValue (channel state) u


namespace PhysicalRisk
@[simp]
theorem channelQuadraticPrediction_haarCalibratedDensityChannel
    {D : ℕ} (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    channelQuadraticPrediction haarCalibratedDensityChannel rho u =
      DensityGrid.quadraticPrediction rho u := by
  simp [channelQuadraticPrediction, DensityGrid.quadraticPrediction,
    hermitianQuadraticValue]


end PhysicalRisk
end TomographyOracleCore
