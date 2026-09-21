import TomographyOracleCore.Revision.FinitePrecisionRayleigh
import TomographyOracleCore.Revision.MatrixSolverGeometry

/-! Exact extreme spectral witnesses for the actual Hermitian residual. -/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction FinitePrecision
open scoped ComplexOrder InnerProductSpace BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem exists_extreme_eigenvalue (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ∃ i : ι, matrixOperatorNorm A = |hA.eigenvalues i| := by
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun i => |hA.eigenvalues i|) Finset.univ_nonempty
  refine ⟨i, ?_⟩
  apply le_antisymm
  · change ‖A‖ ≤ |hA.eigenvalues i|
    conv_lhs => rw [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
    intro j
    simpa [Complex.norm_real, Real.norm_eq_abs] using hmax j (Finset.mem_univ j)
  · have h := A.toEuclideanLin.toContinuousLinearMap.le_opNorm (hA.eigenvectorBasis i)
    simpa only [LinearMap.coe_toContinuousLinearMap', toEuclideanLin_eigenvectorBasis,
      norm_smul, Complex.norm_real, Real.norm_eq_abs, hA.eigenvectorBasis.norm_eq_one,
      mul_one, matrixOperatorNorm] using h

theorem signedRayleigh_eigenvector
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) (s : ℝ) :
    signedRayleigh A (hA.eigenvectorBasis i) s = s * hA.eigenvalues i := by
  simp only [signedRayleigh, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply,
    LinearMap.coe_toContinuousLinearMap', toEuclideanLin_eigenvectorBasis,
    inner_smul_left, inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.norm_eq_one]
  simp

/-- Every Hermitian residual has a signed unit spectral witness attaining
its operator norm. This is proved from the finite-dimensional spectral
theorem; it is not supplied as an eigensolver hypothesis. -/
theorem exists_exact_signedRayleigh
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ∃ v : EuclideanSpace ℂ ι, ∃ s : ℝ,
      ‖v‖ = 1 ∧ |s| ≤ 1 ∧ signedRayleigh A v s = matrixOperatorNorm A := by
  obtain ⟨i, hi⟩ := exists_extreme_eigenvalue A hA
  refine ⟨hA.eigenvectorBasis i, if hA.eigenvalues i < 0 then -1 else 1,
    hA.eigenvectorBasis.norm_eq_one i, ?_, ?_⟩
  · split_ifs <;> norm_num
  · rw [signedRayleigh_eigenvector, hi]
    split_ifs with h
    · rw [abs_of_neg h]
      ring
    · rw [abs_of_nonneg (le_of_not_gt h)]
      ring

end

end TomographyOracleCore.Revision.MatrixSolver
