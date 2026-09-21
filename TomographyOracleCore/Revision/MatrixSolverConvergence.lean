import TomographyOracleCore.Revision.MatrixSolverSubgradient
import TomographyOracleCore.Revision.MatrixSolverAverage
import TomographyOracleCore.Revision.SolverPotential

/-! Exact projected subgradient iterates and the paper's O(G²/γ²)
universal forward-fitting guarantee. All geometric and matrix inputs are
proved in the imported modules. No solver contract is assumed. -/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def exactEigenIndex (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : Fin D := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  exact (exists_extreme_eigenvalue
    (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix)
    (residual_isHermitian U Q hQ rho)).choose

theorem exactEigenIndex_spec (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) =
      |(residual_isHermitian U Q hQ rho).eigenvalues (exactEigenIndex hD U Q hQ rho)| := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  exact (exists_extreme_eigenvalue
    (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix)
    (residual_isHermitian U Q hQ rho)).choose_spec

def exactEigenvector (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : EuclideanSpace ℂ (Fin D) :=
  (residual_isHermitian U Q hQ rho).eigenvectorBasis (exactEigenIndex hD U Q hQ rho)

def exactEigenSign (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : ℝ :=
  if (residual_isHermitian U Q hQ rho).eigenvalues (exactEigenIndex hD U Q hQ rho) < 0
    then -1 else 1

theorem exactEigenvector_norm (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : ‖exactEigenvector hD U Q hQ rho‖ = 1 :=
  (residual_isHermitian U Q hQ rho).eigenvectorBasis.norm_eq_one _

theorem exactEigenvector_ne_zero (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : exactEigenvector hD U Q hQ rho ≠ 0 := by
  intro hz
  have hn := exactEigenvector_norm hD U Q hQ rho
  simp [hz] at hn

theorem exactEigenSign_abs_le_one (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : |exactEigenSign hD U Q hQ rho| ≤ 1 := by
  unfold exactEigenSign
  split_ifs <;> norm_num

theorem exactEigen_signedRayleigh (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) :
    FinitePrecision.signedRayleigh (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix)
      (exactEigenvector hD U Q hQ rho) (exactEigenSign hD U Q hQ rho) =
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  rw [exactEigenvector, signedRayleigh_eigenvector, exactEigenIndex_spec hD U Q hQ rho]
  unfold exactEigenSign
  split_ifs with h
  · rw [abs_of_neg h]
    ring
  · rw [abs_of_nonneg (le_of_not_gt h)]
    ring

/-- The literal signed extreme-eigenprojector gradient from Proposition 4.1,
with the prescribed zero direction when the residual vanishes. -/
def exactGradient (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) : FrobeniusMatrix (Fin D) := by
  classical
  exact if Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix = 0 then 0
    else forwardGradient U (exactEigenvector hD U Q hQ rho) (exactEigenSign hD U Q hQ rho)

theorem exactGradient_norm_le (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho : DensityOperator (Fin D)) :
    ‖exactGradient hD U Q hQ rho‖ ≤ ((D + 1 : ℕ) : ℝ) := by
  classical
  unfold exactGradient
  split_ifs
  · simp only [norm_zero]
    positivity
  · exact forwardGradient_norm_le U _ (exactEigenvector_ne_zero hD U Q hQ rho)
      (exactEigenSign_abs_le_one hD U Q hQ rho)

theorem exactGradient_supporting (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) -
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) ≤
      ⟪exactGradient hD U Q hQ rho, encode rho.matrix - encode sigma.matrix⟫_ℝ := by
  classical
  unfold exactGradient
  split_ifs with hz
  · have hR : matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U rho.matrix) = 0 := by
      rw [hz]
      simp [matrixOperatorNorm]
    rw [hR, zero_sub, inner_zero_left]
    exact neg_nonpos.mpr (matrixOperatorNorm_nonneg _)
  · have hspec := exactEigen_signedRayleigh hD U Q hQ rho
    have ht := forwardGradient_subgradient U Q rho sigma (exactEigenvector hD U Q hQ rho)
      (epsilon := 0) (exactEigenSign_abs_le_one hD U Q hQ rho)
      (by simpa only [sub_zero] using hspec.ge)
    simpa only [add_zero] using ht

def exactStep (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h : ℝ)
    (rho : DensityOperator (Fin D)) : DensityOperator (Fin D) where
  matrix := decode (densityProjection rho0
    (encode rho.matrix - h • exactGradient hD U Q hQ rho))
  posSemidef := (densityProjection_mem rho0 _).1
  trace_eq_one := (densityProjection_mem rho0 _).2

@[simp] theorem encode_exactStep (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h : ℝ)
    (rho : DensityOperator (Fin D)) :
    encode (exactStep hD U Q hQ rho0 h rho).matrix =
      densityProjection rho0 (encode rho.matrix - h • exactGradient hD U Q hQ rho) := by
  exact encode_decode _

def exactIterate (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h : ℝ) : ℕ → DensityOperator (Fin D)
  | 0 => rho0
  | j + 1 => exactStep hD U Q hQ rho0 h (exactIterate hD U Q hQ rho0 h j)

@[simp] theorem exactIterate_zero (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h : ℝ) :
    exactIterate hD U Q hQ rho0 h 0 = rho0 := rfl

@[simp] theorem exactIterate_succ (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h : ℝ) (j : ℕ) :
    exactIterate hD U Q hQ rho0 h (j + 1) =
      exactStep hD U Q hQ rho0 h (exactIterate hD U Q hQ rho0 h j) := rfl

theorem exactIterate_potential_step (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 sigma : DensityOperator (Fin D)) (h : ℝ) (hh : 0 ≤ h) (j : ℕ) :
    ‖encode (exactIterate hD U Q hQ rho0 h (j + 1)).matrix - encode sigma.matrix‖ ^ 2 ≤
      ‖encode (exactIterate hD U Q hQ rho0 h j).matrix - encode sigma.matrix‖ ^ 2 -
        2 * h *
          (matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
            (exactIterate hD U Q hQ rho0 h j).matrix) -
            matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix)) +
        h ^ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 := by
  rw [exactIterate_succ, encode_exactStep]
  exact projected_subgradient_step rho0 _ _ _ (encode_density_mem sigma)
    h ((D + 1 : ℕ) : ℝ) _ hh (by positivity)
    (exactGradient_supporting hD U Q hQ _ sigma)
    (exactGradient_norm_le hD U Q hQ _)

/-- Actual projected matrix iterates obey the universal fitting guarantee.
Only the explicit step-size/iteration arithmetic remains as numeric premises. -/
theorem exactIterate_average_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (h gamma : ℝ)
    (J : ℕ) (hh : 0 < h) (hJ : 0 < J)
    (hbudget : 2 ≤ h * (J : ℝ) * gamma)
    (hvariance : h * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ gamma)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (averageDensity (exactIterate hD U Q hQ rho0 h) J hJ).matrix) ≤
        matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  let potential (j : ℕ) :=
    ‖encode (exactIterate hD U Q hQ rho0 h j).matrix - encode sigma.matrix‖ ^ 2
  let gap (j : ℕ) :=
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (exactIterate hD U Q hQ rho0 h j).matrix) -
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix)
  have hzero : potential 0 ≤ 2 := by
    simpa [potential] using density_frobenius_diameter_sq rho0 sigma
  have hend : 0 ≤ potential J := sq_nonneg _
  have hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * ((D + 1 : ℕ) : ℝ) ^ 2 := by
    intro j hj
    exact exactIterate_potential_step hD U Q hQ rho0 sigma h hh.le j
  have hmean := solver_budget_bound potential gap h ((D + 1 : ℕ) : ℝ) gamma J
    hh hJ hzero hend hstep hbudget hvariance
  have havg := average_objective_gap_le (finiteUnitaryFullCalibratedLinearChannel U)
    Q (exactIterate hD U Q hQ rho0 h) J hJ sigma
  change _ ≤ gamma at hmean
  have hfinal := havg.trans hmean
  linarith

/-- The step size and iteration threshold stated in Proposition 4.1
discharge all numeric solver premises. -/
theorem exactIterate_paper_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (gamma : ℝ) (hgamma : 0 < gamma)
    (J : ℕ) (hJ : 0 < J)
    (hiterations : 2 * ((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2 ≤ (J : ℝ))
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (averageDensity
        (exactIterate hD U Q hQ rho0 (gamma / ((D + 1 : ℕ) : ℝ) ^ 2)) J hJ).matrix) ≤
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma := by
  have hG : 0 < ((D + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hg2 : 0 < gamma ^ 2 := sq_pos_of_pos hgamma
  have hprod : 2 * ((D + 1 : ℕ) : ℝ) ^ 2 ≤ (J : ℝ) * gamma ^ 2 :=
    (div_le_iff₀ hg2).1 hiterations
  apply exactIterate_average_fit hD U Q hQ rho0 _ gamma J
    (div_pos hgamma hG) hJ
  · calc
      2 ≤ (J : ℝ) * gamma ^ 2 / ((D + 1 : ℕ) : ℝ) ^ 2 :=
        (le_div_iff₀ hG).2 (by simpa [mul_comm] using hprod)
      _ = gamma / ((D + 1 : ℕ) : ℝ) ^ 2 * (J : ℝ) * gamma := by ring
  · rw [div_mul_cancel₀ _ (ne_of_gt hG)]

/-- An explicit integer iteration budget at the requested objective accuracy. -/
def exactIterationCount (D : ℕ) (gamma : ℝ) : ℕ :=
  Nat.ceil (2 * ((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2)

theorem exactIterationCount_pos (D : ℕ) (gamma : ℝ) (hgamma : 0 < gamma) :
    0 < exactIterationCount D gamma := by
  apply Nat.ceil_pos.mpr
  positivity

theorem exactIterationCount_bound (D : ℕ) (gamma : ℝ) :
    2 * ((D + 1 : ℕ) : ℝ) ^ 2 / gamma ^ 2 ≤ (exactIterationCount D gamma : ℝ) :=
  Nat.le_ceil _

/-- At the paper's statistical tolerance the explicit outer iteration
count is at most `8*d*T`, proving the asserted O(dT) count. -/
theorem exactIterationCount_statistical_le (D T : ℕ) (hD : 0 < D) (hT : 0 < T) :
    exactIterationCount D (Real.sqrt ((D : ℝ) / (T : ℝ))) ≤ 8 * D * T := by
  have hd : 0 < (D : ℝ) := by exact_mod_cast hD
  have ht : 0 < (T : ℝ) := by exact_mod_cast hT
  have hd1 : 1 ≤ (D : ℝ) := by exact_mod_cast hD
  apply Nat.ceil_le.mpr
  rw [Real.sq_sqrt (div_nonneg hd.le ht.le)]
  norm_cast
  push_cast
  rw [div_div_eq_mul_div]
  apply (div_le_iff₀ hd).2
  have hs : ((D : ℝ) + 1) ^ 2 ≤ 4 * (D : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hs ht.le]

/-- The actual arithmetic average of the exact projected subgradient
iterates, with a concrete step size and a concrete iteration count. This
definition is an exact-real mathematical specification. -/
def exactProjectedSolve (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (gamma : ℝ) (hgamma : 0 < gamma) :
    DensityOperator (Fin D) :=
  averageDensity (exactIterate hD U Q hQ rho0
    (gamma / ((D + 1 : ℕ) : ℝ) ^ 2))
    (exactIterationCount D gamma) (exactIterationCount_pos D gamma hgamma)

/-- Unconditional exact-arithmetic forward fitting for Candidate 2.
Every matrix, projection, subgradient, and averaging assertion has been
proved; only the paper's dimension, Hermitian-input, and tolerance
conditions remain. -/
theorem exactProjectedSolve_fit (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (hQ : Q.IsHermitian)
    (rho0 : DensityOperator (Fin D)) (gamma : ℝ) (hgamma : 0 < gamma)
    (sigma : DensityOperator (Fin D)) :
    matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U
      (exactProjectedSolve hD U Q hQ rho0 gamma hgamma).matrix) ≤
      matrixOperatorNorm (Q - finiteUnitaryFullCalibratedLinearChannel U sigma.matrix) + gamma :=
  exactIterate_paper_fit hD U Q hQ rho0 gamma hgamma
    (exactIterationCount D gamma) (exactIterationCount_pos D gamma hgamma)
    (exactIterationCount_bound D gamma) sigma

end

end TomographyOracleCore.Revision.MatrixSolver
