import TomographyOracleCore.Candidate2ForwardFit
import TomographyOracleCore.Candidate2FullCalibratedChannel
import TomographyOracleCore.BinaryCliffordPeriodicPOVMCurvature
import TomographyOracleCore.HermitianSemanticUpper
import TomographyOracleCore.OrderedSpectral

namespace TomographyOracleCore

open MatrixReduction
open scoped Matrix.Norms.L2Operator

noncomputable section

/-!
# Deterministic statistical oracle for Candidate 2

This module connects the concrete operator-norm fitting program to the
already-proved periodic-channel curvature and density-matrix cone reduction.
The only sample-dependent input is an explicit bound on the empirical
forward-matrix error.  No concentration theorem is assumed or stated here.
-/

namespace Candidate2DeterministicOracle

/-- An approximate solution of the full calibrated forward fit satisfies the
ordered spectral-tail trace-norm oracle.  The constants include both the
empirical error `radius` and the optimization tolerance `delta`.

This is the complete deterministic Candidate-2 statistical reduction.  A
dimension-free covariance theorem is needed only to prove the displayed data
error premise with `radius` of order `sqrt(D/T)`. -/
theorem periodicApproximateForwardFit_orderedSpectralOracle
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
      (64 * radius + 32 * delta) (2 ^ n) := by
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
      (1 : ℝ) / 2 *
          hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
            (sigma.sub_isHermitian rho) ^ 2 ≤
        hermitianForwardEnergy sigma rho forward := by
    rw [hforwardDensity]
    exact h.finiteUnitaryCalibratedDensityChannel_curvature sigma rho
  have hforwardNonneg : 0 ≤ matrixOperatorNorm forward :=
    matrixOperatorNorm_nonneg forward
  have hetaNonneg : 0 ≤ (2 * radius + delta) / 4 := by
    positivity
  have hforwardScale :
      matrixOperatorNorm forward ≤ 4 * ((2 * radius + delta) / 4) := by
    convert hforwardBound using 1
    ring
  have horacle := densityHermitianOracle_of_matrix_bounds_and_forward_error
    sigma rho (2 ^ n) ((1 : ℝ) / 2)
      ((2 * radius + delta) / 4)
      (matrixOperatorNorm forward)
      (hermitianForwardEnergy sigma rho forward)
      (orderedSpectralTail rho)
      (by norm_num)
      hforwardNonneg hforwardScale
      (fun s _hs1 _hsD ↦ density_orderedSpectralTail_cone sigma rho s)
      hcurvature
      (hermitianForwardEnergy_le_traceNorm_mul_operatorNorm sigma rho forward)
  have hconstant :
      64 * ((2 * radius + delta) / 4) / ((1 : ℝ) / 2) =
        64 * radius + 32 * delta := by ring
  rw [hconstant] at horacle
  exact horacle

end Candidate2DeterministicOracle

end

end TomographyOracleCore
