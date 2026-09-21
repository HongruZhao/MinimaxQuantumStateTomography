import TomographyOracleCore.PeriodicCliffordFourthBoundary

namespace TomographyOracleCore.Revision.MatrixProjectionBoundary

open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def matrixEuclideanStarMonoidHom : Matrix ι ι ℂ →⋆*
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) where
  toFun := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
  map_one' := map_one (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
  map_mul' := map_mul (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))
  map_star' := map_star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ))

def matrixUnitaryIsometry (U : Matrix.unitaryGroup ι ℂ) :
    EuclideanSpace ℂ ι ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  Unitary.linearIsometryEquiv (Unitary.map matrixEuclideanStarMonoidHom U)

@[simp]
theorem matrixUnitaryIsometry_apply (U : Matrix.unitaryGroup ι ℂ)
    (u : EuclideanSpace ℂ ι) :
    matrixUnitaryIsometry U u = U.val.toEuclideanLin u := rfl

theorem toEuclideanLin_mul_apply (A B : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) :
    (A * B).toEuclideanLin u = A.toEuclideanLin (B.toEuclideanLin u) := by
  change (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) (A * B) u =
    (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) A
      ((Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)) B u)
  rw [map_mul]
  rfl

/-- Matrix form of the projection-isometry boundary bound. All operator
conditions here are elementary matrix equalities. -/
theorem norm_inner_projection_unitary_le_diagonal
    (Q : Matrix ι ι ℂ) (U : Matrix.unitaryGroup ι ℂ)
    (hQ : Q.IsHermitian) (hQQ : Q * Q = Q)
    (hQU : Q * U.val = U.val * Q) (u : EuclideanSpace ℂ ι) :
    ‖⟪u, (Q * U.val).toEuclideanLin u⟫_ℂ‖ ≤
      (⟪u, Q.toEuclideanLin u⟫_ℂ).re := by
  have hself : ∀ x y, ⟪Q.toEuclideanLin x, y⟫_ℂ = ⟪x, Q.toEuclideanLin y⟫_ℂ :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hQ
  have hid (x : EuclideanSpace ℂ ι) :
      Q.toEuclideanLin (Q.toEuclideanLin x) = Q.toEuclideanLin x := by
    rw [← toEuclideanLin_mul_apply, hQQ]
  have hcomm (x : EuclideanSpace ℂ ι) :
      Q.toEuclideanLin (matrixUnitaryIsometry U x) =
        matrixUnitaryIsometry U (Q.toEuclideanLin x) := by
    simp only [matrixUnitaryIsometry_apply, ← toEuclideanLin_mul_apply, hQU]
  have h := norm_inner_projection_isometry_le_diagonal Q.toEuclideanLin
    (matrixUnitaryIsometry U).toLinearIsometry hself hid hcomm u
  change ‖⟪u, Q.toEuclideanLin (matrixUnitaryIsometry U u)⟫_ℂ‖ ≤ _ at h
  simpa only [toEuclideanLin_mul_apply, matrixUnitaryIsometry_apply] using h

end
end TomographyOracleCore.Revision.MatrixProjectionBoundary
