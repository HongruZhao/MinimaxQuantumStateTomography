import TomographyOracleCore.Candidate2DeterministicOracle
import TomographyOracleCore.Revision.ConstantCurvature
import TomographyOracleCore.Revision.ConstantGeometry
namespace TomographyOracleCore.Candidate2DeterministicOracle
open MatrixReduction
noncomputable section
theorem periodicApproximateForwardFit_orderedSpectralOracle_sharp
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (sigma rho : DensityOperator (Fin (2 ^ n)))
    (radius delta : ℝ)
    (hradius : 0 ≤ radius) (hdelta : 0 ≤ delta)
    (hfit :
      matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
              sigma.matrix) ≤
        matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
              rho.matrix) + delta)
    (hdata :
      matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
              rho.matrix) ≤ radius) :
    OracleBound
      (hermitianTraceNorm (sigma.matrix - rho.matrix)
        (sigma.sub_isHermitian rho))
      (orderedSpectralTail rho)
      ((8 / sharpPeriodicCurvature) * radius + (4 / sharpPeriodicCurvature) * delta) (2 ^ n) := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let L := finiteUnitaryFullCalibratedLinearChannel U
  let forward := L sigma.matrix - L rho.matrix
  have hforwardFit : matrixOperatorNorm forward ≤
      2 * matrixOperatorNorm (Q - L rho.matrix) + delta := by
    exact Candidate2ForwardFit.densityApproximateForwardFit_error_le
      L Q sigma rho delta (by simpa [L, U] using hfit)
  have hforwardBound : matrixOperatorNorm forward ≤ 2 * radius + delta := by
    linarith [hforwardFit, show matrixOperatorNorm (Q - L rho.matrix) ≤ radius by
      simpa [L, U] using hdata]
  have hforwardDensity : forward =
      finiteUnitaryCalibratedDensityChannel U sigma -
        finiteUnitaryCalibratedDensityChannel U rho := by
    calc
      forward = L (sigma.matrix - rho.matrix) := by
        dsimp only [forward]
        rw [map_sub]
      _ = finiteUnitaryFullCalibratedLinearChannel U
          (sigma.matrix - rho.matrix) := rfl
      _ = finiteUnitaryCalibratedDensityChannel U sigma -
          finiteUnitaryCalibratedDensityChannel U rho :=
        finiteUnitaryFullCalibratedLinearChannel_density_sub U sigma rho
  have hcurvature :
      sharpPeriodicCurvature *
          hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
            (sigma.sub_isHermitian rho) ^ 2 ≤
        hermitianForwardEnergy sigma rho forward := by
    rw [hforwardDensity]
    exact h.finiteUnitaryCalibratedDensityChannel_curvature_sharp sigma rho
  intro s hs1 hsD
  have hred := density_orderedSpectralTail_trace_bound_sharp sigma rho s
    sharpPeriodicCurvature (matrixOperatorNorm forward)
    (hermitianForwardEnergy sigma rho forward) sharpPeriodicCurvature_pos
    (matrixOperatorNorm_nonneg _) hcurvature
    (hermitianForwardEnergy_le_traceNorm_mul_operatorNorm sigma rho forward)
  have hcoef : 0 ≤ 4 * (s : ℝ) / sharpPeriodicCurvature :=
    div_nonneg (by positivity) sharpPeriodicCurvature_pos.le
  calc
    _ ≤ 4 * orderedSpectralTail rho s +
        4 * ((s : ℝ) * matrixOperatorNorm forward / sharpPeriodicCurvature) := hred
    _ = 4 * orderedSpectralTail rho s +
        (4 * (s : ℝ) / sharpPeriodicCurvature) * matrixOperatorNorm forward := by ring
    _ ≤ 4 * orderedSpectralTail rho s +
        (4 * (s : ℝ) / sharpPeriodicCurvature) * (2 * radius + delta) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hforwardBound hcoef)
    _ = _ := by ring

end
end TomographyOracleCore.Candidate2DeterministicOracle
