import TomographyOracleCore.Revision.FourthVectorBoundary
import TomographyOracleCore.Revision.MatrixProjectionBoundary

namespace TomographyOracleCore.Revision.FourthLocalEmbedding

open FourthVectorBoundary CliffordFourthOmega PauliOmegaProjection MatrixProjectionBoundary
open MatrixReduction
open scoped BigOperators InnerProductSpace Matrix Kronecker ComplexOrder

noncomputable section

local instance (K : ℕ) : DecidableEq (PauliBinaryWord K) :=
  fun a b => Fintype.decidablePiFintype a b

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

def fourthProductEquiv (α β : Type*) :
    FourthIndex (α × β) ≃ FourthIndex α × FourthIndex β where
  toFun x := ((x.1.1, x.2.1.1, x.2.2.1.1, x.2.2.2.1),
    (x.1.2, x.2.1.2, x.2.2.1.2, x.2.2.2.2))
  invFun x := ((x.1.1, x.2.1), (x.1.2.1, x.2.2.1),
    (x.1.2.2.1, x.2.2.2.1), (x.1.2.2.2, x.2.2.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Embed an operator on the first four registers, preserving the ancilla. -/
def localFourthEmbedding :
    Matrix (FourthIndex α) (FourthIndex α) ℂ →ₗ[ℂ]
      Matrix (FourthIndex (α × β)) (FourthIndex (α × β)) ℂ where
  toFun A := (Matrix.reindexAlgEquiv ℂ ℂ (fourthProductEquiv α β).symm)
    (A ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ))
  map_add' A B := by simp only [Matrix.add_kronecker, map_add]
  map_smul' c A := by simp only [Matrix.smul_kronecker, map_smul, RingHom.id_apply]

theorem localFourthEmbedding_mul
    (A B : Matrix (FourthIndex α) (FourthIndex α) ℂ) :
    localFourthEmbedding (β := β) (A * B) =
      localFourthEmbedding (β := β) A * localFourthEmbedding (β := β) B := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (fourthProductEquiv α β).symm)
    ((A * B) ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ)) = _
  have ht : (A * B) ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ) =
      (A ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ)) *
        (B ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ)) := by
    simpa only [one_mul] using Matrix.mul_kronecker_mul A B
      (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ)
      (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ)
  rw [ht, map_mul]
  rfl

theorem localFourthEmbedding_hermitian
    (A : Matrix (FourthIndex α) (FourthIndex α) ℂ) (hA : A.IsHermitian) :
    (localFourthEmbedding (β := β) A).IsHermitian := by
  change (Matrix.reindex (fourthProductEquiv α β).symm (fourthProductEquiv α β).symm
    (A ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ))).conjTranspose = _
  rw [Matrix.conjTranspose_reindex, Matrix.conjTranspose_kronecker, hA.eq,
    Matrix.conjTranspose_one]
  rfl

/-- Reassociation of the literal Kronecker entries. -/
theorem fourth_tensor_product_reindex (A : Matrix α α ℂ) (B : Matrix β β ℂ) :
    (Matrix.reindexAlgEquiv ℂ ℂ (fourthProductEquiv α β).symm)
      (matrixTensorFour A A A A ⊗ₖ matrixTensorFour B B B B) =
        matrixTensorFour (A ⊗ₖ B) (A ⊗ₖ B) (A ⊗ₖ B) (A ⊗ₖ B) := by
  ext x y
  simp only [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply, Equiv.symm_symm, fourthProductEquiv,
    Equiv.coe_fn_mk, Matrix.kroneckerMap_apply, matrixTensorFour_apply]
  ring

theorem localFourthEmbedding_tensor (A : Matrix α α ℂ) :
    localFourthEmbedding (β := β) (matrixTensorFour A A A A) =
      matrixTensorFour (A ⊗ₖ (1 : Matrix β β ℂ)) (A ⊗ₖ 1) (A ⊗ₖ 1) (A ⊗ₖ 1) := by
  change (Matrix.reindexAlgEquiv ℂ ℂ (fourthProductEquiv α β).symm)
    (matrixTensorFour A A A A ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ)) = _
  rw [← matrixTensorFour_one]
  exact fourth_tensor_product_reindex A 1

/-- The actual exceptional operator on a subsystem of an entangled state. -/
def localPauliFourthOmega (K : ℕ) :
    Matrix (FourthIndex (PauliBinaryWord K × β))
      (FourthIndex (PauliBinaryWord K × β)) ℂ :=
  localFourthEmbedding (β := β) (pauliFourthOmega K)

theorem localPauliFourthOmega_apply (K : ℕ)
    (x y : FourthIndex (PauliBinaryWord K × β)) :
    localPauliFourthOmega (β := β) K x y =
      pauliFourthOmega K (fourthProductEquiv (PauliBinaryWord K) β x).1
        (fourthProductEquiv (PauliBinaryWord K) β y).1 *
      (if (fourthProductEquiv (PauliBinaryWord K) β x).2 =
        (fourthProductEquiv (PauliBinaryWord K) β y).2 then 1 else 0) := by
  change (pauliFourthOmega K ⊗ₖ (1 : Matrix (FourthIndex β) (FourthIndex β) ℂ))
    (fourthProductEquiv (PauliBinaryWord K) β x)
    (fourthProductEquiv (PauliBinaryWord K) β y) = _
  rw [Matrix.kroneckerMap_apply, Matrix.one_apply]

theorem localPauliFourthOmega_expectation
    (K : ℕ) (u : EuclideanSpace ℂ (PauliBinaryWord K × β)) (hu : ‖u‖ = 1) :
    (⟪vectorFourth u,
      (localPauliFourthOmega (β := β) K).toEuclideanLin (vectorFourth u)⟫_ℂ).re =
      phaseFreePauliFourthBoundary K (reducedDensity u hu) := by
  unfold localPauliFourthOmega pauliFourthOmega
  rw [map_smul, map_sum, map_smul, map_sum, LinearMap.smul_apply]
  simp only [LinearMap.sum_apply, inner_smul_right, inner_sum]
  simp_rw [pauliFourthPower, localFourthEmbedding_tensor,
    inner_fourth_tensor, inner_local_eq_trace_reduced]
  have hreal (p : PauliLabel K) :
      (hermitianBinaryPauliMatrix K p * reducedState u).trace =
        ((realBinaryHermitianPauliCoefficient K (reducedState u) p : ℝ) : ℂ) := by
    have h := binaryHermitianPauliCoefficient_eq_re K (reducedState u)
      (reducedState_posSemidef u).isHermitian p
    exact h
  simp_rw [hreal]
  change (((2 : ℂ) ^ K)⁻¹ *
    ∑ p : PauliLabel K,
      (realBinaryHermitianPauliCoefficient K (reducedState u) p : ℂ) ^ 4).re = _
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_pow, ← Complex.ofReal_inv,
    ← Complex.ofReal_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

def localPauliFourthProjection (K : ℕ) :
    Matrix (FourthIndex (PauliBinaryWord K × β))
      (FourthIndex (PauliBinaryWord K × β)) ℂ :=
  localFourthEmbedding (β := β) (pauliFourthProjection K)

theorem localPauliFourthProjection_hermitian (K : ℕ) :
    (localPauliFourthProjection (β := β) K).IsHermitian :=
  localFourthEmbedding_hermitian _ (pauliFourthProjection_hermitian K)

theorem localPauliFourthProjection_idempotent (K : ℕ) :
    localPauliFourthProjection (β := β) K * localPauliFourthProjection (β := β) K =
      localPauliFourthProjection (β := β) K := by
  unfold localPauliFourthProjection
  rw [← localFourthEmbedding_mul, pauliFourthProjection_idempotent]

theorem localPauliFourthOmega_eq_scaled_projection (K : ℕ) :
    localPauliFourthOmega (β := β) K =
      (2 : ℂ) ^ K • localPauliFourthProjection (β := β) K := by
  unfold localPauliFourthOmega localPauliFourthProjection
  rw [pauliFourthOmega_eq_scaled_projection, map_smul]

/-- The entangled boundary inequality for the actual subsystem Omega,
followed by any commuting unitary. -/
theorem localPauliFourthOmega_unitary_bound
    (K : ℕ)
    (U : Matrix.unitaryGroup (FourthIndex (PauliBinaryWord K × β)) ℂ)
    (hcomm : localPauliFourthProjection (β := β) K * U.val =
      U.val * localPauliFourthProjection (β := β) K)
    (u : EuclideanSpace ℂ (PauliBinaryWord K × β)) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u,
      (localPauliFourthOmega (β := β) K * U.val).toEuclideanLin (vectorFourth u)⟫_ℂ‖ ≤ 1 := by
  let Q := localPauliFourthProjection (β := β) K
  let v := vectorFourth u
  have hb := norm_inner_projection_unitary_le_diagonal Q U
    (localPauliFourthProjection_hermitian K)
    (localPauliFourthProjection_idempotent K) hcomm v
  have hd : 0 ≤ (2 : ℝ) ^ K := by positivity
  have hscale : (2 : ℂ) ^ K = ((2 : ℝ) ^ K : ℝ) := by norm_cast
  calc
    _ = (2 : ℝ) ^ K * ‖⟪v, (Q * U.val).toEuclideanLin v⟫_ℂ‖ := by
      rw [localPauliFourthOmega_eq_scaled_projection, Matrix.smul_mul,
        map_smul, LinearMap.smul_apply, inner_smul_right, norm_mul, hscale,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
    _ ≤ (2 : ℝ) ^ K * (⟪v, Q.toEuclideanLin v⟫_ℂ).re :=
      mul_le_mul_of_nonneg_left hb hd
    _ = (⟪vectorFourth u,
      (localPauliFourthOmega (β := β) K).toEuclideanLin (vectorFourth u)⟫_ℂ).re := by
      rw [localPauliFourthOmega_eq_scaled_projection, map_smul,
        LinearMap.smul_apply, inner_smul_right, hscale, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      rfl
    _ = phaseFreePauliFourthBoundary K (reducedDensity u hu) :=
      localPauliFourthOmega_expectation K u hu
    _ ≤ 1 := phaseFreePauliFourthBoundary_le_one K _

theorem localPauliFourthOmega_unitary_bound_of_commute
    (K : ℕ)
    (U : Matrix.unitaryGroup (FourthIndex (PauliBinaryWord K × β)) ℂ)
    (hcomm : localPauliFourthOmega (β := β) K * U.val =
      U.val * localPauliFourthOmega (β := β) K)
    (u : EuclideanSpace ℂ (PauliBinaryWord K × β)) (hu : ‖u‖ = 1) :
    ‖⟪vectorFourth u,
      (localPauliFourthOmega (β := β) K * U.val).toEuclideanLin (vectorFourth u)⟫_ℂ‖ ≤ 1 := by
  apply localPauliFourthOmega_unitary_bound K U ?_ u hu
  rw [localPauliFourthOmega_eq_scaled_projection, Matrix.smul_mul, Matrix.mul_smul] at hcomm
  have h := congrArg (fun A => ((2 : ℂ) ^ K)⁻¹ • A) hcomm
  have hd : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  simpa only [smul_smul, inv_mul_cancel₀ hd, one_smul] using h

end
end TomographyOracleCore.Revision.FourthLocalEmbedding
