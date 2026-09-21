import TomographyOracleCore.FiniteNet
import TomographyOracleCore.MatrixReduction
import TomographyOracleCore.RobustNoise

namespace TomographyOracleCore

open MatrixReduction
open scoped InnerProductSpace Matrix.Norms.L2Operator

/-!
# Forward-matrix geometry

This file proves trace/operator duality and covering inequalities for Hermitian matrices.
-/

/-- Energy pairing between a Hermitian state error and a forward matrix. -/
def hermitianForwardEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma rho : DensityOperator ι) (forward : Matrix ι ι ℂ) : ℝ :=
  (forward * (sigma.matrix - rho.matrix)).trace.re

/-- Trace/operator duality automatically supplies the energy upper bound;
it is not an additional scientific hypothesis. -/
theorem hermitianForwardEnergy_le_traceNorm_mul_operatorNorm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma rho : DensityOperator ι) (forward : Matrix ι ι ℂ) :
    hermitianForwardEnergy sigma rho forward ≤
      hermitianTraceNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) * matrixOperatorNorm forward := by
  let delta := sigma.matrix - rho.matrix
  have hduality :=
    norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm delta forward
      (sigma.sub_isHermitian rho)
  calc
    hermitianForwardEnergy sigma rho forward
        ≤ |hermitianForwardEnergy sigma rho forward| := le_abs_self _
    _ ≤ ‖(forward * delta).trace‖ := by
      simpa [hermitianForwardEnergy, delta] using
        Complex.abs_re_le_norm ((forward * delta).trace)
    _ ≤ hermitianTraceNorm delta (sigma.sub_isHermitian rho) *
          matrixOperatorNorm forward := hduality

/-- Real quadratic form associated with a Hermitian forward matrix. -/
noncomputable def hermitianQuadraticValue
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (u : EuclideanSpace ℂ ι) : ℝ :=
  (⟪u, A.toEuclideanLin u⟫_ℂ).re

/-- Changing the unit direction by `d` changes its quadratic form by at most
`2 * ||A||op * d`. -/
theorem hermitianQuadraticValue_sub_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (x u : EuclideanSpace ℂ ι)
    (hx : ‖x‖ = 1) (hu : ‖u‖ = 1) :
    |hermitianQuadraticValue A x - hermitianQuadraticValue A u| ≤
      2 * matrixOperatorNorm A * ‖x - u‖ := by
  let T := A.toEuclideanLin
  have hidentity :
      ⟪x, T x⟫_ℂ - ⟪u, T u⟫_ℂ =
        ⟪x - u, T x⟫_ℂ + ⟪u, T (x - u)⟫_ℂ := by
    simp [map_sub]
  have hTx : ‖T x‖ ≤ matrixOperatorNorm A * ‖x‖ := by
    simpa [T, matrixOperatorNorm] using
      A.toEuclideanLin.toContinuousLinearMap.le_opNorm x
  have hTsub : ‖T (x - u)‖ ≤
      matrixOperatorNorm A * ‖x - u‖ := by
    simpa [T, matrixOperatorNorm] using
      A.toEuclideanLin.toContinuousLinearMap.le_opNorm (x - u)
  have hcomplex :
      ‖⟪x, T x⟫_ℂ - ⟪u, T u⟫_ℂ‖ ≤
        2 * matrixOperatorNorm A * ‖x - u‖ := by
    rw [hidentity]
    calc
      ‖⟪x - u, T x⟫_ℂ + ⟪u, T (x - u)⟫_ℂ‖
          ≤ ‖⟪x - u, T x⟫_ℂ‖ +
              ‖⟪u, T (x - u)⟫_ℂ‖ := norm_add_le _ _
      _ ≤ ‖x - u‖ * ‖T x‖ + ‖u‖ * ‖T (x - u)‖ :=
        add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
      _ ≤ ‖x - u‖ * (matrixOperatorNorm A * ‖x‖) +
          ‖u‖ * (matrixOperatorNorm A * ‖x - u‖) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hTx (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hTsub (norm_nonneg _))
      _ = 2 * matrixOperatorNorm A * ‖x - u‖ := by
        rw [hx, hu]
        ring
  have hre :
      hermitianQuadraticValue A x - hermitianQuadraticValue A u =
        (⟪x, T x⟫_ℂ - ⟪u, T u⟫_ℂ).re := by
    simp [hermitianQuadraticValue, T]
  rw [hre]
  exact (Complex.abs_re_le_norm _).trans hcomplex

/-- The actual complex quarter-net lifts directional quadratic-form control
to the Hermitian operator norm. -/
theorem matrixOperatorNorm_le_netError_add_half
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (net : Finset (EuclideanSpace ℂ ι)) (hnet : net.Nonempty)
    (hunit : ∀ u ∈ net, ‖u‖ = 1)
    (hcover : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 →
      ∃ u ∈ net, ‖x - u‖ ≤ (1 : ℝ) / 4)
    (netError : ℝ)
    (hnetError : ∀ u ∈ net,
      |hermitianQuadraticValue A u| ≤ netError) :
    matrixOperatorNorm A ≤ netError + matrixOperatorNorm A / 2 := by
  obtain ⟨u₀, hu₀⟩ := hnet
  have hnetError_nonneg : 0 ≤ netError :=
    (abs_nonneg (hermitianQuadraticValue A u₀)).trans
      (hnetError u₀ hu₀)
  have hbound : ∀ i : ι,
      |hA.eigenvalues i| ≤ netError + matrixOperatorNorm A / 2 := by
    intro i
    let x := hA.eigenvectorBasis i
    have hx : ‖x‖ = 1 := hA.eigenvectorBasis.norm_eq_one i
    obtain ⟨u, hu, hdist⟩ := hcover x hx
    have hquad := hermitianQuadraticValue_sub_le A x u hx (hunit u hu)
    have hop_nonneg : 0 ≤ matrixOperatorNorm A := matrixOperatorNorm_nonneg A
    have hquad_half :
        |hermitianQuadraticValue A x - hermitianQuadraticValue A u| ≤
          matrixOperatorNorm A / 2 := by
      calc
        |hermitianQuadraticValue A x - hermitianQuadraticValue A u|
            ≤ 2 * matrixOperatorNorm A * ‖x - u‖ := hquad
        _ ≤ 2 * matrixOperatorNorm A * ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hdist
            (mul_nonneg (by norm_num) hop_nonneg)
        _ = matrixOperatorNorm A / 2 := by ring
    have hxeigen : hermitianQuadraticValue A x = hA.eigenvalues i := by
      simp [hermitianQuadraticValue, x,
        toEuclideanLin_eigenvectorBasis,
        hA.eigenvectorBasis.norm_eq_one]
    calc
      |hA.eigenvalues i| = |hermitianQuadraticValue A x| := by rw [hxeigen]
      _ ≤ |hermitianQuadraticValue A u| +
          |hermitianQuadraticValue A x - hermitianQuadraticValue A u| := by
        have hsum : hermitianQuadraticValue A x =
            hermitianQuadraticValue A u +
              (hermitianQuadraticValue A x - hermitianQuadraticValue A u) := by
          ring
        calc
          |hermitianQuadraticValue A x| =
              |hermitianQuadraticValue A u +
                (hermitianQuadraticValue A x -
                  hermitianQuadraticValue A u)| := congrArg abs hsum
          _ ≤ |hermitianQuadraticValue A u| +
              |hermitianQuadraticValue A x -
                hermitianQuadraticValue A u| := abs_add_le _ _
      _ ≤ netError + matrixOperatorNorm A / 2 :=
        add_le_add (hnetError u hu) hquad_half
  have hspectral :
      matrixOperatorNorm A =
        ‖fun i ↦ ((hA.eigenvalues i : ℝ) : ℂ)‖ := by
    change ‖A‖ = _
    rw (occs := .pos [1]) [hA.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
      CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
      Matrix.l2_opNorm_diagonal]
    congr 1
  rw (occs := .pos [1]) [hspectral]
  apply (pi_norm_le_iff_of_nonneg
    (add_nonneg hnetError_nonneg
      (div_nonneg (matrixOperatorNorm_nonneg A) (by norm_num)))).2
  intro i
  change ‖((hA.eigenvalues i : ℝ) : ℂ)‖ ≤
    netError + matrixOperatorNorm A / 2
  simpa [Complex.norm_real, Real.norm_eq_abs] using hbound i

/-- Absorbed factor-two form of the quarter-net lifting inequality. -/
theorem matrixOperatorNorm_le_two_netError
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (net : Finset (EuclideanSpace ℂ ι)) (hnet : net.Nonempty)
    (hunit : ∀ u ∈ net, ‖u‖ = 1)
    (hcover : ∀ x : EuclideanSpace ℂ ι, ‖x‖ = 1 →
      ∃ u ∈ net, ‖x - u‖ ≤ (1 : ℝ) / 4)
    (netError : ℝ)
    (hnetError : ∀ u ∈ net,
      |hermitianQuadraticValue A u| ≤ netError) :
    matrixOperatorNorm A ≤ 2 * netError := by
  have h := matrixOperatorNorm_le_netError_add_half A hA net hnet hunit
    hcover netError hnetError
  linarith


end TomographyOracleCore
