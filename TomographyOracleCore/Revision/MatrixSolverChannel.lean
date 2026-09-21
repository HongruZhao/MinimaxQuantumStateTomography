import TomographyOracleCore.Revision.MatrixSolverGeometry
import TomographyOracleCore.Candidate2FullCalibratedChannel
import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-! The finite projective measurement channel in Frobenius geometry. -/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem encode_complex_smul (c : ℂ) (A : Matrix ι ι ℂ) :
    encode (c • A) = c • encode A := rfl

@[simp] theorem encode_sum {α : Type*} (s : Finset α) (A : α → Matrix ι ι ℂ) :
    encode (∑ a ∈ s, A a) = ∑ a ∈ s, encode (A a) := by
  ext ij
  simp [encode, Matrix.sum_apply]

theorem inner_encode_eq_trace (A B : Matrix ι ι ℂ) :
    ⟪encode A, encode B⟫_ℂ = (B * A.conjTranspose).trace := by
  simp only [encode, PiLp.inner_apply, RCLike.inner_apply, Matrix.trace,
    Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rfl

theorem real_inner_frobenius_eq_re (x y : FrobeniusMatrix ι) :
    ⟪x, y⟫_ℝ = (⟪x, y⟫_ℂ).re := by
  change (∑ ij, (inner ℂ (x ij) (y ij)).re) = (∑ ij, inner ℂ (x ij) (y ij)).re
  rw [Complex.re_sum]

theorem real_inner_encode_eq_trace (A B : Matrix ι ι ℂ) :
    ⟪encode A, encode B⟫_ℝ = (B * A.conjTranspose).trace.re := by
  rw [real_inner_frobenius_eq_re, inner_encode_eq_trace]

theorem real_inner_encode_eq_trace_of_hermitian
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ⟪encode A, encode B⟫_ℝ = (B * A).trace.re := by
  rw [real_inner_encode_eq_trace, hA.eq]

theorem norm_encode_sq_eq_trace (A : Matrix ι ι ℂ) :
    ‖encode A‖ ^ 2 = (A * A.conjTranspose).trace.re := by
  rw [← real_inner_self_eq_norm_sq, real_inner_encode_eq_trace]

section OrthonormalProjection

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
variable {B : Type*} [Fintype B]

def orthonormalPinching (p : B → V) (x : V) : V :=
  ∑ b, ⟪p b, x⟫_ℂ • p b

theorem orthonormalPinching_contract (p : B → V) (hp : Orthonormal ℂ p) (x : V) :
    ‖orthonormalPinching p x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  have he := hp.inner_sum (fun b => ⟪p b, x⟫_ℂ) (fun b => ⟪p b, x⟫_ℂ) Finset.univ
  have hre := congrArg Complex.re he
  simp only [inner_self_eq_norm_sq_to_K, Complex.conj_mul'] at hre
  have hnorm : ‖orthonormalPinching p x‖ ^ 2 = ∑ b, ‖⟪p b, x⟫_ℂ‖ ^ 2 := by
    simpa [orthonormalPinching, Complex.re_sum, ← Complex.ofReal_pow,
      Complex.normSq_eq_norm_sq] using hre
  rw [hnorm]
  exact hp.sum_inner_products_le x

theorem orthonormalPinching_selfAdjoint (p : B → V) (x y : V) :
    ⟪orthonormalPinching p x, y⟫_ℂ = ⟪x, orthonormalPinching p y⟫_ℂ := by
  simp only [orthonormalPinching, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, inner_conj_symm, mul_comm]

end OrthonormalProjection

section FiniteChannel

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

theorem measurement_projector_mul_trace
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b c : Fin D) :
    (finiteUnitaryMeasurementProjector U b *
      finiteUnitaryMeasurementProjector U c).trace = if b = c then 1 else 0 := by
  unfold finiteUnitaryMeasurementProjector
  have hU : U.1 * U.1.conjTranspose = 1 := U.2.2
  calc
    ((U.1.conjTranspose * finiteComputationalBasisProjector b * U.1) *
      (U.1.conjTranspose * finiteComputationalBasisProjector c * U.1)).trace =
        (U.1.conjTranspose *
          (finiteComputationalBasisProjector b * finiteComputationalBasisProjector c) * U.1).trace := by
      congr 1
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc U.1 U.1.conjTranspose, hU,
        Matrix.one_mul]
    _ = (finiteComputationalBasisProjector b * finiteComputationalBasisProjector c).trace := by
      rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    _ = if b = c then 1 else 0 := by
      simp [finiteComputationalBasisProjector, Matrix.trace_single_mul, Matrix.single_apply, eq_comm]

theorem orthonormal_measurementProjectors (U : Matrix.unitaryGroup (Fin D) ℂ) :
    Orthonormal ℂ (fun b => encode (finiteUnitaryMeasurementProjector U b)) := by
  rw [orthonormal_iff_ite]
  intro b c
  rw [inner_encode_eq_trace,
    (finiteUnitaryMeasurementProjector_posSemidef U b).isHermitian.eq,
    measurement_projector_mul_trace]
  simp only [eq_comm]

def frobeniusChannel (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (x : FrobeniusMatrix (Fin D)) : FrobeniusMatrix (Fin D) :=
  (Fintype.card E : ℝ)⁻¹ • ∑ e, orthonormalPinching
    (fun b => encode (finiteUnitaryMeasurementProjector (U e) b)) x

theorem frobeniusChannel_contract (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (x : FrobeniusMatrix (Fin D)) : ‖frobeniusChannel U x‖ ≤ ‖x‖ := by
  have hcard : 0 < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  calc
    ‖frobeniusChannel U x‖ = (Fintype.card E : ℝ)⁻¹ *
      ‖∑ e, orthonormalPinching
        (fun b => encode (finiteUnitaryMeasurementProjector (U e) b)) x‖ := by
      rw [frobeniusChannel, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hcard)]
    _ ≤ (Fintype.card E : ℝ)⁻¹ * (∑ e : E, ‖x‖) := by
      gcongr
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun e he =>
        orthonormalPinching_contract _ (orthonormal_measurementProjectors (U e)) x)
    _ = ‖x‖ := by simp [ne_of_gt hcard]

theorem frobeniusChannel_selfAdjoint (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (x y : FrobeniusMatrix (Fin D)) :
    ⟪frobeniusChannel U x, y⟫_ℂ = ⟪x, frobeniusChannel U y⟫_ℂ := by
  simp only [frobeniusChannel, RCLike.real_smul_eq_coe_smul (K := ℂ),
    inner_smul_real_left, inner_smul_real_right,
    sum_inner, inner_sum, orthonormalPinching_selfAdjoint]

/-- The Hilbert-space channel is exactly the channel of the finite physical
measurement experiment, on every complex matrix. -/
theorem frobeniusChannel_eq_encode_linearChannel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    frobeniusChannel U (encode A) = encode (finiteUnitaryProjectiveLinearChannel U A) := by
  simp only [frobeniusChannel, orthonormalPinching,
    finiteUnitaryProjectiveLinearChannel_apply, encode_complex_smul, encode_sum]
  have hs : (((Fintype.card E : ℝ)⁻¹ : ℝ) : ℂ) = (Fintype.card E : ℂ)⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  change (((Fintype.card E : ℝ)⁻¹ : ℝ) : ℂ) • _ = _
  rw [hs]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  rw [inner_encode_eq_trace,
    (finiteUnitaryMeasurementProjector_posSemidef (U e) b).isHermitian.eq]

theorem finite_channel_frobenius_contract
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (A : Matrix (Fin D) (Fin D) ℂ) :
    ‖encode (finiteUnitaryProjectiveLinearChannel U A)‖ ≤ ‖encode A‖ := by
  rw [← frobeniusChannel_eq_encode_linearChannel]
  exact frobeniusChannel_contract U (encode A)

theorem finite_channel_frobenius_selfAdjoint
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    ⟪encode (finiteUnitaryProjectiveLinearChannel U A), encode B⟫_ℝ =
      ⟪encode A, encode (finiteUnitaryProjectiveLinearChannel U B)⟫_ℝ := by
  rw [← frobeniusChannel_eq_encode_linearChannel, ← frobeniusChannel_eq_encode_linearChannel]
  rw [real_inner_frobenius_eq_re, real_inner_frobenius_eq_re, frobeniusChannel_selfAdjoint]

theorem density_frobenius_norm_sq_le_one (ρ : DensityOperator (Fin D)) :
    ‖encode ρ.matrix‖ ^ 2 ≤ 1 := by
  rw [norm_encode_sq_eq_trace, ρ.isHermitian.eq]
  have hop : matrixOperatorNorm ρ.matrix ≤ 1 := by
    exact DensityCompact.density_matrix_operator_norm_le_one ρ
  calc
    (ρ.matrix * ρ.matrix).trace.re ≤ ‖(ρ.matrix * ρ.matrix).trace‖ := Complex.re_le_norm _
    _ ≤ hermitianTraceNorm ρ.matrix ρ.isHermitian * matrixOperatorNorm ρ.matrix :=
      norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm ρ.matrix ρ.matrix ρ.isHermitian
    _ ≤ 1 := by simpa [density_hermitianTraceNorm_eq_one] using hop

theorem density_frobenius_diameter_sq (ρ σ : DensityOperator (Fin D)) :
    ‖encode ρ.matrix - encode σ.matrix‖ ^ 2 ≤ 2 := by
  have hD : 0 < D := by
    by_contra h
    have hzero : D = 0 := by omega
    subst D
    have ht := ρ.trace_eq_one
    simp [Matrix.trace] at ht
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  rw [norm_sub_sq_real, real_inner_encode_eq_trace_of_hermitian _ _ ρ.isHermitian]
  have hρ := density_frobenius_norm_sq_le_one ρ
  have hσ := density_frobenius_norm_sq_le_one σ
  have hp := trace_mul_re_nonnegative_of_posSemidef σ.matrix ρ.matrix σ.posSemidef ρ.posSemidef
  linarith

theorem densitySet_diameter_sq (x y : FrobeniusMatrix (Fin D))
    (hx : x ∈ densitySet) (hy : y ∈ densitySet) : ‖x - y‖ ^ 2 ≤ 2 := by
  let ρ : DensityOperator (Fin D) := ⟨decode x, hx.1, hx.2⟩
  let σ : DensityOperator (Fin D) := ⟨decode y, hy.1, hy.2⟩
  simpa [ρ, σ] using density_frobenius_diameter_sq ρ σ

end FiniteChannel

end

end TomographyOracleCore.Revision.MatrixSolver
