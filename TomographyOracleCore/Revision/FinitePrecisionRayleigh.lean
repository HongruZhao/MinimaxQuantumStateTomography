import TomographyOracleCore.MatrixReduction
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
# Approximate extreme Rayleigh directions

The signed Rayleigh quotient is normalized by `‖v‖²`, so a rational vector
can be used without computing its generally irrational unit normalization.
An approximate extreme quotient supplies an epsilon-subgradient of the
actual matrix operator norm. No eigensolver is assumed or axiomatized.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open MatrixReduction
open scoped InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized signed quadratic form of the represented matrix. -/
def signedRayleigh (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (s : ℝ) : ℝ :=
  s * A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient v

/-- Every signed Rayleigh functional with `|s| ≤ 1` is dominated by the
matrix operator norm, for every vector (including zero). -/
theorem signedRayleigh_le_operatorNorm
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) {s : ℝ}
    (hs : |s| ≤ 1) : signedRayleigh A v s ≤ matrixOperatorNorm A := by
  have hR := A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient_le_norm v
  calc
    signedRayleigh A v s ≤ |signedRayleigh A v s| := le_abs_self _
    _ = |s| * |A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient v| :=
      abs_mul _ _
    _ ≤ 1 * |A.toEuclideanLin.toContinuousLinearMap.rayleighQuotient v| := by
      gcongr
    _ ≤ matrixOperatorNorm A := by simpa [matrixOperatorNorm] using hR

theorem signedRayleigh_sub
    (A B : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) (s : ℝ) :
    signedRayleigh (A - B) v s = signedRayleigh A v s - signedRayleigh B v s := by
  simp [signedRayleigh, ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply, inner_sub_left, sub_div,
    mul_sub]

/-- A certified approximate extreme quotient gives the full affine
supporting inequality, simultaneously for every comparator matrix.
This is the finite-precision spectral input to subgradient descent. -/
theorem approximate_rayleigh_epsilon_subgradient
    (A : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) {s epsilon : ℝ}
    (hs : |s| ≤ 1)
    (happrox : matrixOperatorNorm A - epsilon ≤ signedRayleigh A v s)
    (B : Matrix ι ι ℂ) :
    matrixOperatorNorm A - matrixOperatorNorm B ≤
      signedRayleigh (A - B) v s + epsilon := by
  have hB := signedRayleigh_le_operatorNorm B v hs
  rw [signedRayleigh_sub]
  linarith

/-- The same supporting inequality after any concrete complex-linear
forward map; its conclusion is stated directly for the paper's objective. -/
theorem approximate_rayleigh_forward_epsilon_subgradient
    (L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ)
    (Q X : Matrix ι ι ℂ) (v : EuclideanSpace ℂ ι) {s epsilon : ℝ}
    (hs : |s| ≤ 1)
    (happrox : matrixOperatorNorm (Q - L X) - epsilon ≤
      signedRayleigh (Q - L X) v s)
    (Z : Matrix ι ι ℂ) :
    matrixOperatorNorm (Q - L X) - matrixOperatorNorm (Q - L Z) ≤
      signedRayleigh (L (Z - X)) v s + epsilon := by
  have h := approximate_rayleigh_epsilon_subgradient (Q - L X) v hs happrox (Q - L Z)
  have hdiff : Q - L X - (Q - L Z) = L (Z - X) := by
    rw [map_sub]
    abel
  rwa [hdiff] at h

end

end TomographyOracleCore.Revision.FinitePrecision
