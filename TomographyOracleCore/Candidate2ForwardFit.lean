import TomographyOracleCore.MatrixReduction

set_option maxHeartbeats 800000

namespace TomographyOracleCore

open MatrixReduction

/-!
# Deterministic forward fit for Candidate 2

This module isolates the deterministic inequality used after solving the
Candidate-2 operator-norm fitting problem.  It does not assume that the
linear map is injective, positive, or invertible.
-/

namespace Candidate2ForwardFit

variable {ι κ : Type*}
variable [Fintype ι] [DecidableEq ι]
variable [Fintype κ] [DecidableEq κ]

/-- Triangle inequality for the matrix operator norm used by the tomography
reduction. -/
theorem matrixOperatorNorm_add_le (A B : Matrix κ κ ℂ) :
    matrixOperatorNorm (A + B) ≤
      matrixOperatorNorm A + matrixOperatorNorm B := by
  open scoped Matrix.Norms.L2Operator in
    change ‖A + B‖ ≤ ‖A‖ + ‖B‖
    exact norm_add_le A B

/-- Any approximate minimizer of the forward fitting objective is within
twice the data error, plus its optimization tolerance, in forward operator
norm.  Only the displayed approximate-fit inequality is needed; in
particular, no inverse or conditioning assumption on `L` is hidden here. -/
theorem approximateForwardFit_error_le
    (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Q : Matrix κ κ ℂ) (X Xstar : Matrix ι ι ℂ) (delta : ℝ)
    (hfit :
      matrixOperatorNorm (Q - L X) ≤
        matrixOperatorNorm (Q - L Xstar) + delta) :
    matrixOperatorNorm (L X - L Xstar) ≤
      2 * matrixOperatorNorm (Q - L Xstar) + delta := by
  have hdecomp :
      L X - L Xstar = -(Q - L X) + (Q - L Xstar) := by
    abel
  calc
    matrixOperatorNorm (L X - L Xstar) =
        matrixOperatorNorm (-(Q - L X) + (Q - L Xstar)) := by
      rw [hdecomp]
    _ ≤ matrixOperatorNorm (-(Q - L X)) +
        matrixOperatorNorm (Q - L Xstar) :=
      matrixOperatorNorm_add_le _ _
    _ = matrixOperatorNorm (Q - L X) +
        matrixOperatorNorm (Q - L Xstar) := by
      rw [matrixOperatorNorm_neg]
    _ ≤ 2 * matrixOperatorNorm (Q - L Xstar) + delta := by
      linarith [hfit]

/-- Density-operator specialization of `approximateForwardFit_error_le`.
This is the deterministic Candidate-2 forward-fit guarantee. -/
theorem densityApproximateForwardFit_error_le
    (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ)
    (Q : Matrix κ κ ℂ) (sigma rho : DensityOperator ι) (delta : ℝ)
    (hfit :
      matrixOperatorNorm (Q - L sigma.matrix) ≤
        matrixOperatorNorm (Q - L rho.matrix) + delta) :
    matrixOperatorNorm (L sigma.matrix - L rho.matrix) ≤
      2 * matrixOperatorNorm (Q - L rho.matrix) + delta := by
  exact approximateForwardFit_error_le L Q sigma.matrix rho.matrix delta hfit

end Candidate2ForwardFit

end TomographyOracleCore
