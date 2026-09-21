import TomographyOracleCore.Revision.MatrixSolverPhysical

namespace TomographyOracleCore.Revision.MatrixSolver
open MatrixReduction
open scoped ComplexOrder InnerProductSpace BigOperators
noncomputable section
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- Exact radius about the maximally mixed starting state. -/
theorem maximallyMixed_distance_sq (hD : 0 < D) (sigma : DensityOperator (Fin D)) :
    ‖encode (maximallyMixedDensity D hD).matrix - encode sigma.matrix‖ ^ 2 =
      ‖encode sigma.matrix‖ ^ 2 - (D : ℝ)⁻¹ := by
  have hi (rho : DensityOperator (Fin D)) :
      ⟪encode (maximallyMixedDensity D hD).matrix, encode rho.matrix⟫_ℝ = (D : ℝ)⁻¹ := by
    rw [real_inner_encode_eq_trace_of_hermitian _ _ (maximallyMixedDensity D hD).isHermitian]
    change (rho.matrix * ((D : ℝ)⁻¹ • 1)).trace.re = _
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, rho.trace_eq_one]
    simp
  have hn := hi (maximallyMixedDensity D hD)
  rw [real_inner_self_eq_norm_sq] at hn
  rw [norm_sub_sq_real, hi sigma, hn]
  ring

theorem maximallyMixed_distance_sq_le_one (hD : 0 < D) (sigma : DensityOperator (Fin D)) :
    ‖encode (maximallyMixedDensity D hD).matrix - encode sigma.matrix‖ ^ 2 ≤ 1 := by
  rw [maximallyMixed_distance_sq hD sigma]
  have hs := density_frobenius_norm_sq_le_one sigma
  have hd : 0 ≤ (D : ℝ)⁻¹ := by positivity
  linarith

/-- Unit initial squared radius halves the required potential budget. -/
theorem solver_budget_bound_unit_radius
    (potential gap : ℕ → ℝ) (h G gamma : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 0 < J)
    (hzero : potential 0 ≤ 1) (hend : 0 ≤ potential J)
    (hstep : ∀ j < J, potential (j + 1) ≤ potential j - 2 * h * gap j + h ^ 2 * G ^ 2)
    (hbudget : 1 ≤ h * (J : ℝ) * gamma) (hvariance : h * G ^ 2 ≤ gamma) :
    (∑ j ∈ Finset.range J, gap j) / (J : ℝ) ≤ gamma := by
  have ht := solver_telescope potential gap h G J hstep
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hm := mul_le_mul_of_nonneg_left hvariance (show 0 ≤ (J : ℝ) * h by positivity)
  have hmain : 2 * h * (∑ j ∈ Finset.range J, gap j) ≤ 2 * h * ((J : ℝ) * gamma) := by nlinarith
  have hsum : (∑ j ∈ Finset.range J, gap j) ≤ (J : ℝ) * gamma :=
    le_of_mul_le_mul_left hmain (show 0 < 2 * h by positivity)
  apply (div_le_iff₀ hJreal).2
  simpa [mul_comm] using hsum

theorem exactIterate_average_fit_unit_radius (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h gamma : ℝ)
    (J : ℕ) (hh : 0 < h) (hJ : 0 < J)
    (hbudget : 1 ≤ h * (J : ℝ) * gamma)
    (hvariance : h * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ gamma)
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
        h ^ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 := by
    intro j hj
    exact exactIterate_potential_step hD U Q hQ rho0 sigma h hh.le j
  have hmean := solver_budget_bound_unit_radius potential gap h ((D + 1 : ℕ) : ℝ) gamma J
    hh hJ hzero hend hstep hbudget hvariance
  have havg := average_objective_gap_le (finiteUnitaryFullCalibratedLinearChannel U)
    Q (exactIterate hD U Q hQ rho0 h) J hJ sigma
  change _ ≤ gamma at hmean
  have hfinal := havg.trans hmean
  linarith


/-- The actual mixed-start projected solver fits after ceil((d+1)^2/gamma^2)
iterations, compared with the former ceil(2*(d+1)^2/gamma^2). -/
theorem exactIterate_mixed_paper_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (gamma : ℝ) (hgamma : 0 < gamma) (J : ℕ) (hJ : 0 < J)
    (hiterations : ((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2 ≤ (J : ℝ))
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (averageDensity
        (exactIterate hD U Q hQ (maximallyMixedDensity D hD)
          (gamma / ((D + 1 : ℕ) : ℝ) ^ 2)) J hJ).matrix) ≤
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  have hG : 0 < ((D + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hprod : ((D + 1 : ℕ) : ℝ) ^ 2 ≤ (J : ℝ) * gamma ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hgamma)).1 hiterations
  apply exactIterate_average_fit_unit_radius hD U Q hQ (maximallyMixedDensity D hD)
    _ gamma J (div_pos hgamma hG) hJ ?_ ?_ sigma (maximallyMixed_distance_sq_le_one hD sigma)
  · calc
      1 ≤ (J : ℝ) * gamma ^ 2 / ((D + 1 : ℕ) : ℝ) ^ 2 :=
        (le_div_iff₀ hG).2 (by simpa using hprod)
      _ = gamma / ((D + 1 : ℕ) : ℝ) ^ 2 * (J : ℝ) * gamma := by ring
  · rw [div_mul_cancel₀ _ hG.ne']

def mixedIterationCount (D : ℕ) (gamma : ℝ) : ℕ :=
  Nat.ceil (((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2)

theorem mixedIterationCount_pos (D : ℕ) (gamma : ℝ) (hgamma : 0 < gamma) :
    0 < mixedIterationCount D gamma := by
  apply Nat.ceil_pos.mpr
  positivity

def mixedProjectedSolve (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian) (gamma : ℝ) (hgamma : 0 < gamma) :
    DensityOperator (Fin D) :=
  averageDensity (exactIterate hD U Q hQ (maximallyMixedDensity D hD)
    (gamma / ((D + 1 : ℕ) : ℝ) ^ 2)) (mixedIterationCount D gamma)
      (mixedIterationCount_pos D gamma hgamma)

theorem mixedProjectedSolve_fit (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian) (gamma : ℝ) (hgamma : 0 < gamma)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (mixedProjectedSolve hD U Q hQ gamma hgamma).matrix) ≤
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma :=
  exactIterate_mixed_paper_fit hD U Q hQ gamma hgamma _
    (mixedIterationCount_pos D gamma hgamma) (Nat.le_ceil _) sigma

/-- Exact comparison of the integer budgets, allowing only one ceiling unit. -/
theorem twice_mixedIterationCount_le_old_add_one (D : ℕ) (gamma : ℝ) :
    2 * mixedIterationCount D gamma ≤ exactIterationCount D gamma + 1 := by
  unfold mixedIterationCount exactIterationCount
  simp only [mul_div_assoc]
  let x : ℝ := ((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hc := Nat.ceil_lt_add_one hx
  have ho := Nat.le_ceil (2 * x)
  have hreal : (2 * Nat.ceil x : ℝ) < (Nat.ceil (2 * x) : ℝ) + 2 := by nlinarith
  have hnat : 2 * Nat.ceil x < Nat.ceil (2 * x) + 2 := by exact_mod_cast hreal
  change 2 * Nat.ceil x ≤ Nat.ceil (2 * x) + 1
  omega

/-- Total physical interface for the faster exact projected solve. -/
def guardedMixedProjectedSolve (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) := by
  classical
  exact if hQ : Q.IsHermitian then mixedProjectedSolve hD U Q hQ gamma hgamma
    else PhysicalMinimax.forwardMinimizer hD U Q

theorem guardedMixedProjectedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (guardedMixedProjectedSolve hD U gamma hgamma Q).matrix) ≤
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  classical
  unfold guardedMixedProjectedSolve
  split_ifs with hQ
  · exact mixedProjectedSolve_fit hD U Q hQ gamma hgamma sigma
  · exact (PhysicalMinimax.forwardMinimizer_le hD U Q sigma).trans
      (le_add_of_nonneg_right hgamma.le)

end
end TomographyOracleCore.Revision.MatrixSolver
