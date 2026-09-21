import TomographyOracleCore.Revision.AlgorithmResourcesPowerBridge
import TomographyOracleCore.Revision.MatrixSolverSpectral

/-! Operator norm and positivity certificates for rational spectral shifts. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixReduction MatrixSolver
open scoped BigOperators ComplexOrder InnerProductSpace Matrix.Norms.L2Operator

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem euclidean_norm_le_sum (x : EuclideanSpace ℂ ι) : ‖x‖ ≤ ∑ i, ‖x i‖ := by
  have hx : (∑ i, PiLp.single 2 i (x i)) = x := by
    ext j
    simp [PiLp.single_apply]
  calc
    ‖x‖ = ‖∑ i, PiLp.single 2 i (x i)‖ := by rw [hx]
    _ ≤ ∑ i, ‖(PiLp.single 2 i (x i) : EuclideanSpace ℂ ι)‖ :=
      norm_sum_le Finset.univ (fun i => (PiLp.single 2 i (x i) : EuclideanSpace ℂ ι))
    _ = ∑ i, ‖x i‖ := by simp

theorem matrixOperatorNorm_le_sum_entries (A : Matrix ι ι ℂ) :
    matrixOperatorNorm A ≤ ∑ i, ∑ j, ‖A i j‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  calc
    ‖A.toEuclideanLin.toContinuousLinearMap x‖ ≤
        ∑ i, ‖(A.toEuclideanLin.toContinuousLinearMap x) i‖ := euclidean_norm_le_sum _
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x j‖ := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
        Matrix.mulVec, dotProduct, norm_mul] using
        norm_sum_le Finset.univ (fun j => A i j * x j)
    _ ≤ ∑ i, ∑ j, ‖A i j‖ * ‖x‖ := by
      gcongr with i _ j _
      exact PiLp.norm_apply_le x j
    _ = (∑ i, ∑ j, ‖A i j‖) * ‖x‖ := by simp only [Finset.sum_mul]

theorem complexVectorNormSq_eq_euclidean_norm (v : ι → ℂ) :
    complexVectorNormSq v = ‖WithLp.toLp 2 v‖ ^ 2 := by
  simp [complexVectorNormSq, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]

theorem complexRayleigh_eq_rayleighQuotient (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    complexRayleigh A v =
      A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient (WithLp.toLp 2 v) := by
  unfold complexRayleigh ContinuousLinearMap.rayleighQuotient
  rw [complexVectorNormSq_eq_euclidean_norm]
  congr 1
  rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
  simp only [complexQuadratic, PiLp.inner_apply, RCLike.inner_apply,
    LinearMap.coe_toContinuousLinearMap', Matrix.toEuclideanLin_apply,
    PiLp.toLp_apply, starRingEnd_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem complexRayleigh_abs_le_norm (A : Matrix ι ι ℂ) (v : ι → ℂ) :
    |complexRayleigh A v| ≤ matrixOperatorNorm A := by
  rw [complexRayleigh_eq_rayleighQuotient]
  exact A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient_le_norm _

theorem complexQuadratic_sub (A B : Matrix ι ι ℂ) (v : ι → ℂ) :
    complexQuadratic (A - B) v = complexQuadratic A v - complexQuadratic B v := by
  simp [complexQuadratic, Matrix.sub_mulVec, mul_sub, Finset.sum_sub_distrib]

theorem complexQuadratic_smul_one (M : ℝ) (v : ι → ℂ) :
    complexQuadratic (M • (1 : Matrix ι ι ℂ)) v = M * complexVectorNormSq v := by
  simp only [complexQuadratic, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
    complexVectorNormSq, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [Complex.normSq_apply, Complex.mul_re, Complex.real_smul]
  ring

theorem scalar_shift_posDef (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (M : ℝ) (hM : matrixOperatorNorm A < M) :
    (M • (1 : Matrix ι ι ℂ) - A).PosDef := by
  have hH : (M • (1 : Matrix ι ι ℂ) - A).IsHermitian :=
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint M from rfl)).sub hA
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hH
  intro v hv
  apply Complex.pos_iff.mpr
  refine ⟨?_, (hH.im_star_dotProduct_mulVec_self v).symm⟩
  change 0 < complexQuadratic (M • (1 : Matrix ι ι ℂ) - A) v
  rw [complexQuadratic_sub, complexQuadratic_smul_one]
  have hn := complexVectorNormSq_pos v hv
  have hb := (le_abs_self (complexRayleigh A v)).trans (complexRayleigh_abs_le_norm A v)
  have hf := (div_le_iff₀ hn).mp hb
  nlinarith

theorem eigenvalue_abs_le_operatorNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    |hA.eigenvalues i| ≤ matrixOperatorNorm A := by
  have h := A.toEuclideanLin.toContinuousLinearMap.le_opNorm (hA.eigenvectorBasis i)
  simpa only [LinearMap.coe_toContinuousLinearMap', toEuclideanLin_eigenvectorBasis,
    norm_smul, Complex.norm_real, Real.norm_eq_abs, hA.eigenvectorBasis.norm_eq_one,
    mul_one, matrixOperatorNorm] using h

theorem qBestPowerColumn_operatorNorm_bound {d : ℕ}
    (hD : 0 < d) (A : Matrix (Fin d) (Fin d) QComplex)
    (hA : (castQMatrix A).PosDef) (k : ℕ) :
    matrixOperatorNorm (castQMatrix A) -
      (d : ℝ) * matrixOperatorNorm (castQMatrix A) / ((2 * k : ℕ) + 1 : ℝ) ≤
      (qRayleigh A (qPowerColumn A k (qBestPowerColumn hD A k)) : ℝ) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hD
  obtain ⟨j, hj⟩ := exists_extreme_eigenvalue (castQMatrix A) hA.isHermitian
  rw [abs_of_pos (hA.eigenvalues_pos j)] at hj
  have hmax : ∀ i, hA.isHermitian.eigenvalues i ≤ hA.isHermitian.eigenvalues j := by
    intro i
    rw [← hj]
    exact (le_abs_self _).trans (eigenvalue_abs_le_operatorNorm _ hA.isHermitian i)
  have h := qBestPowerColumn_spectral_bound hD A hA.posSemidef k j hmax
    (hA.eigenvalues_pos j)
  simpa only [← hj] using h

#print axioms qBestPowerColumn_operatorNorm_bound
#print axioms scalar_shift_posDef

end
end TomographyOracleCore.Revision.AlgorithmResources
