import TomographyOracleCore.Revision.ConstantGradient
namespace TomographyOracleCore.Revision.MatrixSolver
open MatrixReduction
open scoped InnerProductSpace BigOperators ComplexOrder
noncomputable section
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

theorem periodicGradientSquareBudget_pos (D : ℕ) : 0 < periodicGradientSquareBudget D := by
  unfold periodicGradientSquareBudget
  positivity

def HasDimensionGradientBound (U : E → Matrix.unitaryGroup (Fin D) ℂ) : Prop :=
  ∀ v : EuclideanSpace ℂ (Fin D), v ≠ 0 → ∀ s : ℝ, |s| ≤ 1 →
    ‖forwardGradient U v s‖ ≤ Real.sqrt (periodicGradientSquareBudget D)

theorem periodic_hasDimensionGradientBound {n K : ℕ}
    (H : ChoKimBlockCondition n K) (hn : 0 < n) :
    HasDimensionGradientBound (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) := by
  intro v hv s hs
  exact periodic_forwardGradient_norm_le H hn v hv hs

theorem exactGradient_norm_le_dimension (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (hgradient : HasDimensionGradientBound U)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) :
    ‖exactGradient hD U Q hQ rho‖ ≤ Real.sqrt (periodicGradientSquareBudget D) := by
  classical
  unfold exactGradient
  split_ifs
  · simpa using Real.sqrt_nonneg (periodicGradientSquareBudget D)
  · exact hgradient _ (exactEigenvector_ne_zero hD U Q hQ rho) _
      (exactEigenSign_abs_le_one hD U Q hQ rho)

theorem exactIterate_average_fit_dimension (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (hgradient : HasDimensionGradientBound U)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h gamma : ℝ)
    (J : ℕ) (hh : 0 < h) (hJ : 0 < J)
    (hbudget : 1 ≤ h * (J : ℝ) * gamma)
    (hvariance : h * periodicGradientSquareBudget D ≤ gamma)
    (sigma : DensityOperator (Fin D))
    (hstart : ‖encode rho0.matrix - encode sigma.matrix‖ ^ 2 ≤ 1) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (averageDensity (exactIterate hD U Q hQ rho0 h) J hJ).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  let potential (j : ℕ) :=
    ‖encode (exactIterate hD U Q hQ rho0 h j).matrix - encode sigma.matrix‖ ^ 2
  let gap (j : ℕ) :=
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (exactIterate hD U Q hQ rho0 h j).matrix) -
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix)
  have hzero : potential 0 ≤ 1 := by
    simpa [potential] using hstart
  have hend : 0 ≤ potential J := sq_nonneg _
  have hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * periodicGradientSquareBudget D := by
    intro j hj
    rw [show potential (j + 1) =
      ‖encode (exactIterate hD U Q hQ rho0 h (j + 1)).matrix - encode sigma.matrix‖ ^ 2 from rfl,
      exactIterate_succ, encode_exactStep]
    let rhoj := exactIterate hD U Q hQ rho0 h j
    have hp := projected_subgradient_step rho0 (encode rhoj.matrix) (encode sigma.matrix)
      (exactGradient hD U Q hQ rhoj) (encode_density_mem sigma)
      h (Real.sqrt (periodicGradientSquareBudget D)) (gap j) hh.le (Real.sqrt_nonneg _)
      (exactGradient_supporting hD U Q hQ rhoj sigma)
      (exactGradient_norm_le_dimension hD U hgradient Q hQ rhoj)
    simpa only [Real.sq_sqrt (periodicGradientSquareBudget_pos D).le] using hp
  have hmean := solver_budget_bound_unit_radius potential gap h (Real.sqrt (periodicGradientSquareBudget D)) gamma J
    hh hJ hzero hend
    (by simpa only [Real.sq_sqrt (periodicGradientSquareBudget_pos D).le] using hstep)
    hbudget (by simpa only [Real.sq_sqrt (periodicGradientSquareBudget_pos D).le] using hvariance)
  have havg := average_objective_gap_le (finiteUnitaryFullCalibratedLinearChannel U)
    Q (exactIterate hD U Q hQ rho0 h) J hJ sigma
  change _ ≤ gamma at hmean
  have hfinal := havg.trans hmean
  linarith



/-- Actual iteration budget with linear, rather than quadratic, dimension dependence. -/
def dimensionIterationCount (D : ℕ) (gamma : ℝ) : ℕ :=
  Nat.ceil (periodicGradientSquareBudget D / gamma ^ 2)

theorem dimensionIterationCount_pos (D : ℕ) {gamma : ℝ} (hgamma : 0 < gamma) :
    0 < dimensionIterationCount D gamma := by
  apply Nat.ceil_pos.mpr
  exact div_pos (periodicGradientSquareBudget_pos D) (sq_pos_of_pos hgamma)

def dimensionProjectedSolve (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian) (gamma : ℝ) (hgamma : 0 < gamma) :
    DensityOperator (Fin D) :=
  averageDensity (exactIterate hD U Q hQ (maximallyMixedDensity D hD)
    (gamma / periodicGradientSquareBudget D)) (dimensionIterationCount D gamma)
    (dimensionIterationCount_pos D hgamma)

theorem dimensionProjectedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (hgradient : HasDimensionGradientBound U)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian) (gamma : ℝ) (hgamma : 0 < gamma)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (dimensionProjectedSolve hD U Q hQ gamma hgamma).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  have hG := periodicGradientSquareBudget_pos D
  have hc := Nat.le_ceil (periodicGradientSquareBudget D / gamma ^ 2)
  have hb : periodicGradientSquareBudget D ≤ (dimensionIterationCount D gamma : ℝ) * gamma ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hgamma)).mp hc
  apply exactIterate_average_fit_dimension hD U hgradient Q hQ
    (maximallyMixedDensity D hD) _ gamma _ (div_pos hgamma hG)
    (dimensionIterationCount_pos D hgamma) ?_ ?_ sigma (maximallyMixed_distance_sq_le_one hD sigma)
  · calc
      1 ≤ (dimensionIterationCount D gamma : ℝ) * gamma ^ 2 / periodicGradientSquareBudget D :=
        (le_div_iff₀ hG).mpr (by simpa using hb)
      _ = _ := by ring
  · rw [div_mul_cancel₀ _ hG.ne']

/-- At every dimension allowed by the periodic theorem, the certified outer
budget improves by at least 40000, apart from one new ceiling unit. -/
theorem dimensionIterationCount_fortyThousand_improvement (D : ℕ) (hD : 65536 ≤ D)
    (gamma : ℝ) :
    40000 * dimensionIterationCount D gamma ≤ exactIterationCount D gamma + 40000 := by
  have hDr : (65536 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hbase : 40000 * periodicGradientSquareBudget D ≤ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 := by
    unfold periodicGradientSquareBudget
    push_cast
    nlinarith
  have hquot := div_le_div_of_nonneg_right hbase (sq_nonneg gamma)
  rw [mul_div_assoc] at hquot
  have hx : 0 ≤ periodicGradientSquareBudget D / gamma ^ 2 := by
    exact div_nonneg (periodicGradientSquareBudget_pos D).le (sq_nonneg _)
  have hc := Nat.ceil_lt_add_one hx
  have ho := Nat.le_ceil (2 * ((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2)
  have hreal : (40000 : ℝ) * (dimensionIterationCount D gamma : ℝ) <
      (exactIterationCount D gamma : ℝ) + 40000 := by
    dsimp [dimensionIterationCount, exactIterationCount]
    nlinarith
  exact_mod_cast hreal.le

end
end TomographyOracleCore.Revision.MatrixSolver
