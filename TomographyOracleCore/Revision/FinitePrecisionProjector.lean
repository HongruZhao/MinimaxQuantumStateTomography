import TomographyOracleCore.Revision.MatrixSolverGeometry
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Normalized rank-one projectors without square roots

The projector `vv*/‖v‖²` is positive semidefinite and trace one whenever
`v ≠ 0`. It is an exact rational operation when the coordinates of `v`
are rational complex numbers. No exact unit-vector normalization is
required for either the projection oracle or the subgradient direction.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open MatrixReduction Matrix
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedProjector (v : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  (‖v‖ ^ 2)⁻¹ • Matrix.vecMulVec (fun i => v i) (star (fun i => v i))

theorem normalizedProjector_posSemidef (v : EuclideanSpace ℂ ι) :
    (normalizedProjector v).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star (fun i => v i)).smul
    (inv_nonneg.mpr (sq_nonneg ‖v‖))

theorem vecMulVec_trace_eq_norm_sq (v : EuclideanSpace ℂ ι) :
    (Matrix.vecMulVec (fun i => v i) (star (fun i => v i))).trace =
      ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.trace_vecMulVec, EuclideanSpace.norm_sq_eq]
  simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow,
    ← Complex.mul_conj, ← Complex.normSq_eq_norm_sq, starRingEnd_apply]

theorem normalizedProjector_trace_eq_one
    (v : EuclideanSpace ℂ ι) (hv : v ≠ 0) :
    (normalizedProjector v).trace = 1 := by
  rw [normalizedProjector, Matrix.trace_smul, vecMulVec_trace_eq_norm_sq]
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hv)
  apply Complex.ext
  · simpa only [Complex.smul_re, Complex.ofReal_re, Complex.one_re, smul_eq_mul]
      using inv_mul_cancel₀ hn
  · simp only [Complex.smul_im, Complex.ofReal_im, Complex.one_im, smul_zero]

/-- The returned atom is an actual density matrix. -/
def normalizedProjectorDensity (v : EuclideanSpace ℂ ι) (hv : v ≠ 0) :
    DensityOperator ι where
  matrix := normalizedProjector v
  posSemidef := normalizedProjector_posSemidef v
  trace_eq_one := normalizedProjector_trace_eq_one v hv

@[simp] theorem normalizedProjectorDensity_matrix
    (v : EuclideanSpace ℂ ι) (hv : v ≠ 0) :
    (normalizedProjectorDensity v hv).matrix = normalizedProjector v := rfl

/-- Trace pairing with the exact normalized rational projector is the
usual Rayleigh quotient of the represented matrix. -/
theorem trace_mul_normalizedProjector_re_eq_rayleigh
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) :
    (A * normalizedProjector v).trace.re =
      A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient v := by
  rw [normalizedProjector, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, Complex.smul_re]
  simp only [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply]
  have hinner :
      ((A *ᵥ fun i => v i) ⬝ᵥ star (fun i => v i)).re =
      (inner ℂ (A.toEuclideanLin v) v).re := by
    have hc : ((A *ᵥ fun i => v i) ⬝ᵥ star (fun i => v i)) =
        inner ℂ v (A.toEuclideanLin v) := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, dotProduct,
        Pi.star_apply, Matrix.toEuclideanLin_apply, starRingEnd_apply]
    rw [hc]
    exact inner_re_symm (𝕜 := ℂ) v (A.toEuclideanLin v)
  rw [smul_eq_mul, hinner]
  change (‖v‖ ^ 2)⁻¹ * (inner ℂ (A.toEuclideanLin v) v).re =
    (inner ℂ (A.toEuclideanLin v) v).re / ‖v‖ ^ 2
  ring

/-- A positive extreme Rayleigh approximation for `M I - A` is an
approximate linear minimizer of `trace(A rho)` over *all* density matrices.
This connects the rational power search to the inner projection routine.
The bound uses the actual matrix trace/operator duality already proved in
the project, rather than an assumed optimization oracle. -/
theorem normalizedProjector_linear_minimizer_of_shift
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (hv : v ≠ 0)
    (M delta : ℝ)
    (happrox : matrixOperatorNorm (M • (1 : Matrix ι ι ℂ) - A) - delta ≤
      (M • (1 : Matrix ι ι ℂ) - A).toEuclideanLin.toContinuousLinearMap.rayleighQuotient v)
    (rho : DensityOperator ι) :
    (normalizedProjector v * A).trace.re ≤ (rho.matrix * A).trace.re + delta := by
  let B : Matrix ι ι ℂ := M • (1 : Matrix ι ι ℂ) - A
  have hP : (normalizedProjector v * B).trace.re =
      M - (normalizedProjector v * A).trace.re := by
    dsimp [B]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, normalizedProjector_trace_eq_one v hv]
    simp
  have hrho : (rho.matrix * B).trace.re = M - (rho.matrix * A).trace.re := by
    dsimp [B]
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub,
      Matrix.trace_smul, rho.trace_eq_one]
    simp
  have hdual : (rho.matrix * B).trace.re ≤ matrixOperatorNorm B := by
    calc
      (rho.matrix * B).trace.re ≤ ‖(rho.matrix * B).trace‖ := Complex.re_le_norm _
      _ = ‖(B * rho.matrix).trace‖ := by rw [Matrix.trace_mul_comm]
      _ ≤ hermitianTraceNorm rho.matrix rho.isHermitian * matrixOperatorNorm B :=
        norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm rho.matrix B rho.isHermitian
      _ = matrixOperatorNorm B := by rw [density_hermitianTraceNorm_eq_one, one_mul]
  have hRayleigh := trace_mul_normalizedProjector_re_eq_rayleigh B v
  rw [Matrix.trace_mul_comm] at hRayleigh
  change matrixOperatorNorm B - delta ≤ B.toEuclideanLin.toContinuousLinearMap.rayleighQuotient v at happrox
  rw [← hRayleigh, hP] at happrox
  rw [hrho] at hdual
  linarith

end

end TomographyOracleCore.Revision.FinitePrecision
