import TomographyOracleCore.MatrixReduction

namespace TomographyOracleCore

open MatrixReduction
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace DensityCompact

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Density matrices, viewed as a subset of the ambient finite-dimensional
matrix space equipped with its Euclidean operator-norm metric. -/
def densityMatrixSet : Set (Matrix ι ι ℂ) :=
  {A | A.PosSemidef ∧ A.trace = 1}

/-- Positive semidefiniteness is closed in the usual finite-dimensional
matrix topology. -/
theorem isClosed_posSemidefSet :
    IsClosed {A : Matrix ι ι ℂ | A.PosSemidef} := by
  have hhermitian : IsClosed {A : Matrix ι ι ℂ | A.IsHermitian} := by
    simpa [Matrix.IsHermitian, IsSelfAdjoint] using
      (isClosed_eq continuous_id.matrix_conjTranspose continuous_id)
  have hquadratic : ∀ x : ι → ℂ,
      IsClosed {A : Matrix ι ι ℂ |
        0 ≤ dotProduct (star x) (Matrix.mulVec A x)} := by
    intro x
    have hcontinuous : Continuous (fun A : Matrix ι ι ℂ =>
        dotProduct (star x) (Matrix.mulVec A x)) :=
      continuous_const.dotProduct
        (continuous_id.matrix_mulVec continuous_const)
    change IsClosed ((fun A : Matrix ι ι ℂ =>
      dotProduct (star x) (Matrix.mulVec A x)) ⁻¹' Set.Ici 0)
    exact isClosed_Ici.preimage hcontinuous
  have heq :
      {A : Matrix ι ι ℂ | A.PosSemidef} =
        {A | A.IsHermitian} ∩
          ⋂ x : ι → ℂ,
            {A | 0 ≤ dotProduct (star x) (Matrix.mulVec A x)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [heq]
  exact hhermitian.inter (isClosed_iInter hquadratic)

theorem isClosed_densityMatrixSet :
    IsClosed (densityMatrixSet : Set (Matrix ι ι ℂ)) := by
  have htrace : IsClosed {A : Matrix ι ι ℂ | A.trace = 1} :=
    isClosed_eq continuous_id.matrix_trace continuous_const
  simpa [densityMatrixSet, Set.ofPred_and] using
    (isClosed_posSemidefSet (ι := ι)).inter htrace

/-- A trace-one positive matrix has operator norm at most one. -/
theorem density_matrix_operator_norm_le_one (ρ : DensityOperator ι) :
    ‖ρ.matrix‖ ≤ 1 := by
  rw [ρ.isHermitian.spectral_theorem]
  simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).2
  intro i
  change ‖((ρ.isHermitian.eigenvalues i : ℝ) : ℂ)‖ ≤ 1
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (ρ.posSemidef.eigenvalues_nonneg i)]
  have hle : ρ.isHermitian.eigenvalues i ≤
      ∑ j, ρ.isHermitian.eigenvalues j :=
    Finset.single_le_sum
      (fun j _ => ρ.posSemidef.eigenvalues_nonneg j) (Finset.mem_univ i)
  rw [ρ.sum_eigenvalues_eq_one] at hle
  exact hle

theorem isBounded_densityMatrixSet :
    Bornology.IsBounded (densityMatrixSet : Set (Matrix ι ι ℂ)) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨1, ?_⟩
  intro A hA
  exact density_matrix_operator_norm_le_one
    ({ matrix := A, posSemidef := hA.1, trace_eq_one := hA.2 } :
      DensityOperator ι)

/-- The finite-dimensional density-matrix set is compact in operator norm. -/
theorem isCompact_densityMatrixSet :
    IsCompact (densityMatrixSet : Set (Matrix ι ι ℂ)) := by
  letI : ProperSpace (Matrix ι ι ℂ) := FiniteDimensional.proper ℂ _
  exact Metric.isCompact_iff_isClosed_bounded.mpr
    ⟨isClosed_densityMatrixSet, isBounded_densityMatrixSet⟩

theorem densityOperator_matrix_injective :
    Function.Injective (DensityOperator.matrix :
      DensityOperator ι → Matrix ι ι ℂ) := by
  intro ρ σ h
  cases ρ with
  | mk ρ hρ htρ =>
    cases σ with
    | mk σ hσ htσ =>
      simp only at h
      subst σ
      rfl

/-- The chosen metric on density operators is the operator-norm metric of
their underlying matrices. -/
noncomputable instance densityOperatorMetricSpace :
    MetricSpace (DensityOperator ι) :=
  MetricSpace.induced DensityOperator.matrix densityOperator_matrix_injective
    inferInstance

theorem range_densityOperator_matrix :
    Set.range (DensityOperator.matrix : DensityOperator ι → Matrix ι ι ℂ) =
      densityMatrixSet := by
  ext A
  constructor
  · rintro ⟨ρ, rfl⟩
    exact ⟨ρ.posSemidef, ρ.trace_eq_one⟩
  · intro hA
    let ρ : DensityOperator ι :=
      { matrix := A, posSemidef := hA.1, trace_eq_one := hA.2 }
    exact ⟨ρ, rfl⟩

/-- The whole density-operator state space is compact in the induced matrix
operator-norm metric. -/
theorem isCompact_univ_densityOperator :
    IsCompact (Set.univ : Set (DensityOperator ι)) := by
  have hisometry : Isometry
      (DensityOperator.matrix : DensityOperator ι → Matrix ι ι ℂ) :=
    fun _ _ => rfl
  rw [hisometry.isEmbedding.isCompact_iff]
  simpa [Set.image_univ, range_densityOperator_matrix] using
    (isCompact_densityMatrixSet (ι := ι))

end DensityCompact

end TomographyOracleCore
