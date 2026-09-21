import TomographyOracleCore.Revision.PauliOmegaProjection

namespace TomographyOracleCore.Revision.FourthVectorBoundary

open MatrixReduction CliffordFourthOmega PauliOmegaProjection
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder

noncomputable section

variable {ι α β : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def vectorFourth (u : EuclideanSpace ℂ ι) : EuclideanSpace ℂ (FourthIndex ι) :=
  WithLp.toLp 2 (fun x => u x.1 * u x.2.1 * u x.2.2.1 * u x.2.2.2)

def vectorProjector (u : EuclideanSpace ℂ ι) : Matrix ι ι ℂ :=
  Matrix.vecMulVec (fun i => u i) (star (fun i => u i))

theorem trace_mul_vectorProjector (A : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    (A * vectorProjector u).trace = ⟪u, A.toEuclideanLin u⟫_ℂ := by
  rw [vectorProjector, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec]
  simp only [PiLp.inner_apply, RCLike.inner_apply, dotProduct,
    Pi.star_apply, Matrix.toEuclideanLin_apply, starRingEnd_apply]

theorem vectorProjector_fourth (u : EuclideanSpace ℂ ι) :
    vectorProjector (vectorFourth u) =
      matrixTensorFour (vectorProjector u) (vectorProjector u)
        (vectorProjector u) (vectorProjector u) := by
  ext x y
  simp only [vectorProjector, vectorFourth, Matrix.vecMulVec_apply, Pi.star_apply,
    matrixTensorFour_apply, star_mul]
  ring

theorem trace_matrixTensorFour (A B C D : Matrix ι ι ℂ) :
    (matrixTensorFour A B C D).trace = A.trace * B.trace * C.trace * D.trace := by
  simp only [matrixTensorFour, Matrix.trace_kronecker]
  ring

/-- Fourth tensor powers have the exact fourth-power expectation. -/
theorem inner_fourth_tensor (A : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    ⟪vectorFourth u,
      (matrixTensorFour A A A A).toEuclideanLin (vectorFourth u)⟫_ℂ =
      ⟪u, A.toEuclideanLin u⟫_ℂ ^ 4 := by
  rw [← trace_mul_vectorProjector, vectorProjector_fourth, ← matrixTensorFour_mul,
    trace_matrixTensorFour, trace_mul_vectorProjector]
  ring

def coefficientMatrix (u : EuclideanSpace ℂ (α × β)) : Matrix α β ℂ :=
  fun i j => u (i, j)

def reducedState (u : EuclideanSpace ℂ (α × β)) : Matrix α α ℂ :=
  coefficientMatrix u * (coefficientMatrix u).conjTranspose

theorem reducedState_posSemidef (u : EuclideanSpace ℂ (α × β)) :
    (reducedState u).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem reducedState_trace (u : EuclideanSpace ℂ (α × β)) :
    (reducedState u).trace = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [reducedState, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, coefficientMatrix]
  simp_rw [← starRingEnd_apply, Complex.mul_conj']
  rw [Fintype.sum_prod_type]
  push_cast
  rfl

def reducedDensity (u : EuclideanSpace ℂ (α × β)) (hu : ‖u‖ = 1) :
    DensityOperator α where
  matrix := reducedState u
  posSemidef := reducedState_posSemidef u
  trace_eq_one := by rw [reducedState_trace, hu]; norm_num

/-- The reduced matrix is the actual partial trace, as witnessed by every
local matrix expectation. -/
theorem inner_local_eq_trace_reduced
    (A : Matrix α α ℂ) (u : EuclideanSpace ℂ (α × β)) :
    ⟪u, (A ⊗ₖ (1 : Matrix β β ℂ)).toEuclideanLin u⟫_ℂ =
      (A * reducedState u).trace := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, Matrix.toEuclideanLin_apply,
    Matrix.mulVec, dotProduct, WithLp.ofLp_toLp,
    Matrix.kronecker_apply, Fintype.sum_prod_type, Matrix.one_apply]
  simp only [mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  simp only [reducedState, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, coefficientMatrix, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  simp only [starRingEnd_apply]
  ring

end
end TomographyOracleCore.Revision.FourthVectorBoundary
