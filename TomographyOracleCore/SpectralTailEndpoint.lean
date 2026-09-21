import TomographyOracleCore.OrderedSpectral

namespace TomographyOracleCore
open MatrixReduction

/-- The ordered tail vanishes after all `D` eigenvalues in dimension `D`. -/
theorem orderedSpectralTail_fin_dimension_eq_zero
    (D : ℕ) (rho : DensityOperator (Fin D)) :
    orderedSpectralTail rho D = 0 := by
  unfold orderedSpectralTail
  apply Finset.sum_eq_zero
  intro j hj
  have hjlt : j.val < D := by simpa using j.isLt
  simp [Nat.not_le_of_lt hjlt]


end TomographyOracleCore
