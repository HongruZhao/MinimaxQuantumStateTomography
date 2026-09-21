import TomographyOracleCore.Revision.PeriodicUniformFourthMoment
import TomographyOracleCore.Revision.BornCovarianceConditions

namespace TomographyOracleCore.Revision.PeriodicBornMoments

open MeasureTheory Candidate2FiniteBornVectorLaw BornFourthMoment BornCovarianceConditions
open PeriodicUniformFourthMoment
open scoped InnerProductSpace
noncomputable section

local instance {D : ℕ} : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

/-- Unconditional sixth marginal bound for the actual periodic Born law. -/
theorem periodic_born_sixth {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : MatrixReduction.DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂choKimPeriodicBornVectorLaw H.block_dvd rho) ≤ 34 :=
  integral_sixth_le_thirtyFour_of_uniform_eighth (by positivity) _ rho
    (periodic_uniform_eighth H hn) u hu

/-- The concrete Born covariance input has L6/L2 constant four. There is no
moment, representation, circuit-contraction, or concentration premise. -/
theorem periodic_born_hasL6L2 {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : MatrixReduction.DensityOperator (Fin (2 ^ n))) :
    PeriodicForwardCovariance.HasL6L2Marginals
      (choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho) 4 :=
  hasL6L2Marginals_periodic_of_uniform_eighth H hn rho (periodic_uniform_eighth H hn)

end
end TomographyOracleCore.Revision.PeriodicBornMoments
