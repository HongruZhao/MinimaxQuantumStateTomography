import TomographyOracleCore.BinaryPauliOneCopyCurvature
import TomographyOracleCore.BinaryCliffordPauliCosetEnsemble

namespace TomographyOracleCore

open MatrixReduction
open scoped BigOperators Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

/-!
# Fourth-copy Pauli boundary estimates

This file isolates the arbitrary-entangled-boundary calculation used in the
fourth-moment transfer for the periodic shallow Clifford circuit.  The
concrete phase-free Pauli functional below is

`2^(-K) * sum_P (tr(P rho))^4`.

The proof is entirely finite dimensional.  Its two inputs are proved in the
existing binary-Pauli library: Hermitian-Pauli Parseval and unitarity of every
Hermitian Pauli.  No fourth-design or probabilistic assertion is used here.
-/

section AbstractProjectionBoundary

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Cauchy--Schwarz inside the range of an orthogonal projection, in the
exact form needed for a fourth-copy sector followed by a replica
permutation.  `Q` is specified by its self-adjointness and idempotence, and
`V` is a norm-preserving linear map commuting with `Q`.

This theorem is deliberately stated without a finite-dimensional or Pauli
assumption: once a concrete fourth-copy operator is identified with a
positive scalar times such a `Q`, the heterogeneous-sector boundary step is
automatic. -/
theorem norm_inner_projection_isometry_le_diagonal
    (Q : E →ₗ[ℂ] E) (V : E →ₗᵢ[ℂ] E)
    (hself : ∀ x y, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ)
    (hid : ∀ x, Q (Q x) = Q x)
    (hcomm : ∀ x, Q (V x) = V (Q x))
    (v : E) :
    ‖⟪v, Q (V v)⟫_ℂ‖ ≤ (⟪v, Q v⟫_ℂ).re := by
  have hmixed : ⟪v, Q (V v)⟫_ℂ = ⟪Q v, V (Q v)⟫_ℂ := by
    calc
      ⟪v, Q (V v)⟫_ℂ = ⟪Q v, V v⟫_ℂ := (hself v (V v)).symm
      _ = ⟪Q v, Q (V v)⟫_ℂ := by
        rw [← hself]
        rw [hid]
      _ = ⟪Q v, V (Q v)⟫_ℂ := by rw [hcomm]
  have hdiagonal : ⟪v, Q v⟫_ℂ = ⟪Q v, Q v⟫_ℂ := by
    calc
      ⟪v, Q v⟫_ℂ = ⟪Q v, v⟫_ℂ := (hself v v).symm
      _ = ⟪Q v, Q v⟫_ℂ := by
        rw [← hself]
        rw [hid]
  calc
    ‖⟪v, Q (V v)⟫_ℂ‖ = ‖⟪Q v, V (Q v)⟫_ℂ‖ :=
      congrArg norm hmixed
    _ ≤ ‖Q v‖ * ‖V (Q v)‖ := norm_inner_le_norm _ _
    _ = ‖Q v‖ ^ 2 := by rw [V.norm_map, pow_two]
    _ = (⟪Q v, Q v⟫_ℂ).re := by
      rw [inner_self_eq_norm_sq_to_K]
      change ‖Q v‖ ^ 2 = (((‖Q v‖ : ℂ) ^ 2).re)
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    _ = (⟪v, Q v⟫_ℂ).re := congrArg Complex.re hdiagonal.symm

/-- Scalar-rescaled form corresponding to `Omega = d * Pi`. -/
theorem norm_inner_scaled_projection_isometry_le_diagonal
    (Q : E →ₗ[ℂ] E) (V : E →ₗᵢ[ℂ] E)
    (hself : ∀ x y, ⟪Q x, y⟫_ℂ = ⟪x, Q y⟫_ℂ)
    (hid : ∀ x, Q (Q x) = Q x)
    (hcomm : ∀ x, Q (V x) = V (Q x))
    (d : ℝ) (hd : 0 ≤ d) (v : E) :
    ‖(d : ℂ) * ⟪v, Q (V v)⟫_ℂ‖ ≤
      d * (⟪v, Q v⟫_ℂ).re := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  exact mul_le_mul_of_nonneg_left
    (norm_inner_projection_isometry_le_diagonal Q V hself hid hcomm v) hd

end AbstractProjectionBoundary

/-- The real Hermitian-Pauli coordinate of a matrix. -/
def realBinaryHermitianPauliCoefficient
    (K : ℕ)
    (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (p : PauliLabel K) : ℝ :=
  (binaryHermitianPauliCoefficient K X p).re

/-- Exact Hilbert--Schmidt Parseval identity for the concrete Hermitian binary
Pauli basis.  This is the matrix form of
`sum_P (tr(P X))^2 = 2^K tr(X^2)` for Hermitian `X`. -/
theorem realBinaryHermitianPauli_parseval
    (K : ℕ)
    (X : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (hX : X.IsHermitian) :
    (∑ p : PauliLabel K,
        realBinaryHermitianPauliCoefficient K X p ^ 2) =
      (2 : ℝ) ^ K * (X * X).trace.re := by
  classical
  have hidDiagonal : ∀ p : PauliLabel K,
      LinearMap.id (R := ℂ)
          (M := Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
          (hermitianBinaryPauliMatrix K p) =
        ((1 : ℝ) : ℂ) • hermitianBinaryPauliMatrix K p := by
    intro p
    simp
  have henergy := complexLinearPauliChannel_energy_eq K
    (LinearMap.id (R := ℂ)
      (M := Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (fun _ : PauliLabel K ↦ (1 : ℝ)) hidDiagonal X hX
  have hdpos : 0 < (2 : ℝ) ^ K := by positivity
  change (∑ p : PauliLabel K,
      (binaryHermitianPauliCoefficient K X p).re ^ 2) = _
  have henergy' : (X * X).trace.re =
      ((2 : ℝ) ^ K)⁻¹ *
        ∑ p : PauliLabel K,
          (binaryHermitianPauliCoefficient K X p).re ^ 2 := by
    simpa using henergy
  rw [henergy']
  field_simp

/-- Every concrete Hermitian binary Pauli has matrix operator norm one. -/
theorem matrixOperatorNorm_hermitianBinaryPauli_eq_one
    (K : ℕ) (p : PauliLabel K) :
    matrixOperatorNorm (hermitianBinaryPauliMatrix K p) = 1 := by
  change ‖hermitianBinaryPauliMatrix K p‖ = 1
  exact CStarRing.norm_of_mem_unitary
    (hermitianBinaryPauliMatrix_mem_unitaryGroup K p)

/-- A Hermitian-Pauli expectation in a density operator belongs to
`[-1,1]`. -/
theorem abs_realBinaryHermitianPauliCoefficient_density_le_one
    (K : ℕ)
    (rho : DensityOperator (PauliBinaryWord K))
    (p : PauliLabel K) :
    |realBinaryHermitianPauliCoefficient K rho.matrix p| ≤ 1 := by
  have hdual := norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm
    rho.matrix (hermitianBinaryPauliMatrix K p) rho.isHermitian
  have htraceNorm : hermitianTraceNorm rho.matrix rho.isHermitian = 1 :=
    density_hermitianTraceNorm_eq_one rho
  calc
    |realBinaryHermitianPauliCoefficient K rho.matrix p| ≤
        ‖(hermitianBinaryPauliMatrix K p * rho.matrix).trace‖ := by
      exact Complex.abs_re_le_norm _
    _ ≤ hermitianTraceNorm rho.matrix rho.isHermitian *
          matrixOperatorNorm (hermitianBinaryPauliMatrix K p) := hdual
    _ = 1 := by
      rw [htraceNorm, matrixOperatorNorm_hermitianBinaryPauli_eq_one]
      norm_num

/-- Every eigenvalue of a density operator is at most one. -/
theorem densityOperator_eigenvalue_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator ι) (i : ι) :
    rho.isHermitian.eigenvalues i ≤ 1 := by
  rw [← rho.sum_eigenvalues_eq_one]
  exact Finset.single_le_sum
    (fun j _ ↦ rho.posSemidef.eigenvalues_nonneg j)
    (Finset.mem_univ i)

/-- The purity of a finite-dimensional density operator is at most one. -/
theorem densityOperator_trace_sq_re_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator ι) :
    (rho.matrix * rho.matrix).trace.re ≤ 1 := by
  have htrace := trace_sq_eq_hermitianFrobeniusSq
    rho.matrix rho.isHermitian
  have hre := congrArg Complex.re htrace
  have hsum :
      (∑ i, rho.isHermitian.eigenvalues i ^ 2) ≤
        ∑ i, rho.isHermitian.eigenvalues i := by
    apply Finset.sum_le_sum
    intro i hi
    have hnonneg := rho.posSemidef.eigenvalues_nonneg i
    have hle := densityOperator_eigenvalue_le_one rho i
    nlinarith
  rw [rho.sum_eigenvalues_eq_one] at hsum
  simpa [hermitianFrobeniusSq] using hre.trans_le hsum

/-- The phase-free fourth-copy Pauli boundary scalar.  For a reduced state
`rho_A`, this is exactly `d_A⁻¹ ∑_P (tr(P rho_A))^4`. -/
def phaseFreePauliFourthBoundary
    (K : ℕ)
    (rho : DensityOperator (PauliBinaryWord K)) : ℝ :=
  ((2 : ℝ) ^ K)⁻¹ *
    ∑ p : PauliLabel K,
      realBinaryHermitianPauliCoefficient K rho.matrix p ^ 4

/-- The arbitrary-entangled reduced-state boundary is nonnegative. -/
theorem phaseFreePauliFourthBoundary_nonneg
    (K : ℕ)
    (rho : DensityOperator (PauliBinaryWord K)) :
    0 ≤ phaseFreePauliFourthBoundary K rho := by
  unfold phaseFreePauliFourthBoundary
  positivity

/-- Concrete phase-free Pauli fourth-boundary inequality.  It holds for
every density operator, and hence in particular for the reduced density
operator of an arbitrarily entangled pure state. -/
theorem phaseFreePauliFourthBoundary_le_one
    (K : ℕ)
    (rho : DensityOperator (PauliBinaryWord K)) :
    phaseFreePauliFourthBoundary K rho ≤ 1 := by
  classical
  let c : PauliLabel K → ℝ :=
    fun p ↦ realBinaryHermitianPauliCoefficient K rho.matrix p
  have hfour_two : (∑ p : PauliLabel K, c p ^ 4) ≤
      ∑ p : PauliLabel K, c p ^ 2 := by
    apply Finset.sum_le_sum
    intro p hp
    have habs := abs_realBinaryHermitianPauliCoefficient_density_le_one
      K rho p
    have hsquare : c p ^ 2 ≤ 1 := by
      change |c p| ≤ 1 at habs
      exact (sq_le_one_iff_abs_le_one (c p)).mpr habs
    have hnonneg : 0 ≤ c p ^ 2 := sq_nonneg _
    nlinarith [sq_nonneg (c p ^ 2)]
  have hparseval : (∑ p : PauliLabel K, c p ^ 2) =
      (2 : ℝ) ^ K * (rho.matrix * rho.matrix).trace.re := by
    simpa [c] using
      realBinaryHermitianPauli_parseval K rho.matrix rho.isHermitian
  have hpurity := densityOperator_trace_sq_re_le_one rho
  have hdnonneg : 0 ≤ (2 : ℝ) ^ K := by positivity
  have hsum : (∑ p : PauliLabel K, c p ^ 4) ≤ (2 : ℝ) ^ K := by
    calc
      _ ≤ ∑ p : PauliLabel K, c p ^ 2 := hfour_two
      _ = (2 : ℝ) ^ K * (rho.matrix * rho.matrix).trace.re := hparseval
      _ ≤ (2 : ℝ) ^ K * 1 :=
        mul_le_mul_of_nonneg_left hpurity hdnonneg
      _ = (2 : ℝ) ^ K := mul_one _
  have hdpos : 0 < (2 : ℝ) ^ K := by positivity
  change ((2 : ℝ) ^ K)⁻¹ * ∑ p : PauliLabel K, c p ^ 4 ≤ 1
  rw [inv_mul_eq_div]
  exact (div_le_one hdpos).2 hsum

/-- Absolute-value form used by the periodic fourth-moment contraction. -/
theorem abs_phaseFreePauliFourthBoundary_le_one
    (K : ℕ)
    (rho : DensityOperator (PauliBinaryWord K)) :
    |phaseFreePauliFourthBoundary K rho| ≤ 1 := by
  rw [abs_of_nonneg (phaseFreePauliFourthBoundary_nonneg K rho)]
  exact phaseFreePauliFourthBoundary_le_one K rho

end

end TomographyOracleCore
