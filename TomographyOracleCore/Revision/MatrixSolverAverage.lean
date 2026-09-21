import TomographyOracleCore.Revision.MatrixSolverChannel

/-! Feasibility and the operator-norm objective bound for the actual
arithmetic average of density iterates. -/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction
open scoped ComplexOrder InnerProductSpace BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ}

def averageDensity (rho : ℕ → DensityOperator (Fin D)) (J : ℕ) (hJ : 0 < J) :
    DensityOperator (Fin D) where
  matrix := (J : ℝ)⁻¹ • ∑ j ∈ Finset.range J, (rho j).matrix
  posSemidef := (Matrix.posSemidef_sum _ (fun j hj => (rho j).posSemidef)).smul
    (inv_nonneg.mpr (Nat.cast_nonneg J))
  trace_eq_one := by
    rw [Matrix.trace_smul, Matrix.trace_sum]
    simp only [DensityOperator.trace_eq_one, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, mul_one]
    have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hJ)
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change (((J : ℝ)⁻¹ : ℝ) : ℂ) * (J : ℂ) = 1
    rw [Complex.ofReal_inv, Complex.ofReal_natCast, inv_mul_cancel₀]
    exact_mod_cast (Nat.ne_of_gt hJ)

@[simp] theorem averageDensity_matrix (rho : ℕ → DensityOperator (Fin D))
    (J : ℕ) (hJ : 0 < J) :
    (averageDensity rho J hJ).matrix =
      (J : ℝ)⁻¹ • ∑ j ∈ Finset.range J, (rho j).matrix := rfl

theorem average_residual_identity
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ)
    (rho : ℕ → DensityOperator (Fin D)) (J : ℕ) (hJ : 0 < J) :
    Q - L (averageDensity rho J hJ).matrix =
      (J : ℝ)⁻¹ • ∑ j ∈ Finset.range J, (Q - L (rho j).matrix) := by
  rw [averageDensity_matrix, L.map_smul_of_tower, map_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    smul_sub]
  congr 1
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt hJ)

theorem average_objective_le
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ)
    (rho : ℕ → DensityOperator (Fin D)) (J : ℕ) (hJ : 0 < J) :
    matrixOperatorNorm (Q - L (averageDensity rho J hJ).matrix) ≤
      (∑ j ∈ Finset.range J, matrixOperatorNorm (Q - L (rho j).matrix)) / (J : ℝ) := by
  have hJpos : 0 < (J : ℝ) := by exact_mod_cast hJ
  change ‖Q - L (averageDensity rho J hJ).matrix‖ ≤
    (∑ j ∈ Finset.range J, ‖Q - L (rho j).matrix‖) / (J : ℝ)
  rw [average_residual_identity, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hJpos)]
  calc
    (J : ℝ)⁻¹ * ‖∑ j ∈ Finset.range J, (Q - L (rho j).matrix)‖ ≤
      (J : ℝ)⁻¹ * ∑ j ∈ Finset.range J, ‖Q - L (rho j).matrix‖ := by
        gcongr
        exact norm_sum_le _ _
    _ = (∑ j ∈ Finset.range J, ‖Q - L (rho j).matrix‖) / (J : ℝ) := by ring

theorem average_objective_gap_le
    (L : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ)
    (rho : ℕ → DensityOperator (Fin D)) (J : ℕ) (hJ : 0 < J)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - L (averageDensity rho J hJ).matrix) -
      matrixOperatorNorm (Q - L sigma.matrix) ≤
        (∑ j ∈ Finset.range J,
          (matrixOperatorNorm (Q - L (rho j).matrix) -
            matrixOperatorNorm (Q - L sigma.matrix))) / (J : ℝ) := by
  have havg := sub_le_sub_right (average_objective_le L Q rho J hJ)
    (matrixOperatorNorm (Q - L sigma.matrix))
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    sub_div, mul_div_cancel_left₀] 
  · exact havg
  · exact_mod_cast (Nat.ne_of_gt hJ)

end

end TomographyOracleCore.Revision.MatrixSolver
