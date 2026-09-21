import TomographyOracleCore.MathlibImports
import TomographyOracleCore.Structural
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Algebra.Order.Chebyshev

namespace TomographyOracleCore

open scoped ComplexOrder InnerProductSpace

/-!
# Typed matrix layer for the tomography reduction

This file begins replacing the scalar `reduction` input by statements about
finite-dimensional complex density operators.  It deliberately does not
postulate a matrix cone inequality.  Instead it supplies the definitions and
the singular-value inequalities on which such a proof can be built.
-/

namespace MatrixReduction

/-- A finite-dimensional density operator: a positive-semidefinite complex
matrix with trace one. -/
structure DensityOperator (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι ℂ
  posSemidef : matrix.PosSemidef
  trace_eq_one : matrix.trace = 1

namespace DensityOperator

variable {ι : Type*} [Fintype ι]

instance : Coe (DensityOperator ι) (Matrix ι ι ℂ) :=
  ⟨DensityOperator.matrix⟩

/-- Every density operator is Hermitian. -/
theorem isHermitian (ρ : DensityOperator ι) : ρ.matrix.IsHermitian :=
  ρ.posSemidef.isHermitian

/-- The estimation error `sigma - rho` is Hermitian. -/
theorem sub_isHermitian (σ ρ : DensityOperator ι) :
    (σ.matrix - ρ.matrix).IsHermitian :=
  σ.isHermitian.sub ρ.isHermitian

/-- The difference of two density operators has trace zero. -/
theorem trace_sub_eq_zero (σ ρ : DensityOperator ι) :
    (σ.matrix - ρ.matrix).trace = 0 := by
  rw [Matrix.trace_sub, σ.trace_eq_one, ρ.trace_eq_one, sub_self]

/-- The (real) eigenvalues of a density operator sum to one. -/
theorem sum_eigenvalues_eq_one [DecidableEq ι] (ρ : DensityOperator ι) :
    ∑ i, ρ.isHermitian.eigenvalues i = 1 := by
  apply Complex.ofReal_injective
  have h := ρ.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.trace_eq_one] at h
  rw [Complex.ofReal_sum Finset.univ]
  simpa using h.symm

end DensityOperator

section SingularNorms

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Schatten one functional, defined as the finite sum of the singular
values of the Euclidean linear map represented by `A`.

This is the trace norm as a value.  We avoid declaring a `Norm` instance until
the triangle inequality has been established. -/
noncomputable def traceNorm (A : Matrix ι ι ℂ) : ℝ :=
  A.toEuclideanLin.singularValues.sum fun _ x => x

/-- The sum of squared singular values.  Its square root is the
Hilbert--Schmidt/Frobenius norm. -/
noncomputable def frobeniusSq (A : Matrix ι ι ℂ) : ℝ :=
  A.toEuclideanLin.singularValues.sum fun _ x => x ^ 2

/-- The Frobenius norm, defined spectrally. -/
noncomputable def frobeniusNorm (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt (frobeniusSq A)

/-- Matrix rank, expressed as the dimension of the range of the represented
linear map. -/
noncomputable def matrixRank (A : Matrix ι ι ℂ) : ℕ :=
  Module.finrank ℂ A.toEuclideanLin.range

theorem traceNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ traceNorm A := by
  apply Finsupp.sum_nonneg
  intro i hi
  exact A.toEuclideanLin.singularValues_nonneg i

theorem frobeniusSq_nonneg (A : Matrix ι ι ℂ) : 0 ≤ frobeniusSq A := by
  apply Finsupp.sum_nonneg
  intro i hi
  exact sq_nonneg _

theorem frobeniusNorm_nonneg (A : Matrix ι ι ℂ) : 0 ≤ frobeniusNorm A :=
  Real.sqrt_nonneg _

@[simp]
theorem traceNorm_zero : traceNorm (0 : Matrix ι ι ℂ) = 0 := by
  simp [traceNorm]

@[simp]
theorem frobeniusSq_zero : frobeniusSq (0 : Matrix ι ι ℂ) = 0 := by
  simp [frobeniusSq]

@[simp]
theorem frobeniusNorm_zero : frobeniusNorm (0 : Matrix ι ι ℂ) = 0 := by
  simp [frobeniusNorm]

/-- The spectral Frobenius norm squares to the sum of squared singular
values. -/
theorem frobeniusNorm_sq (A : Matrix ι ι ℂ) :
    frobeniusNorm A ^ 2 = frobeniusSq A := by
  exact Real.sq_sqrt (frobeniusSq_nonneg A)

/-- The trace norm vanishes exactly at the zero matrix. -/
theorem traceNorm_eq_zero_iff (A : Matrix ι ι ℂ) : traceNorm A = 0 ↔ A = 0 := by
  let T := A.toEuclideanLin
  constructor
  · intro h
    have hsum :
        ∑ i ∈ T.singularValues.support, T.singularValues i = 0 := by
      simpa [traceNorm, Finsupp.sum, T] using h
    have hall : ∀ i ∈ T.singularValues.support, T.singularValues i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => T.singularValues_nonneg i).mp hsum
    have hsv : T.singularValues = 0 := by
      ext i
      by_cases hi : i ∈ T.singularValues.support
      · simpa using hall i hi
      · exact Finsupp.notMem_support_iff.mp hi
    have hT : T = 0 := (T.singularValues_eq_zero_iff).mp hsv
    exact Matrix.toEuclideanLin.injective (by simpa [T] using hT)
  · rintro rfl
    exact traceNorm_zero

/-- The squared Frobenius functional vanishes exactly at the zero matrix. -/
theorem frobeniusSq_eq_zero_iff (A : Matrix ι ι ℂ) : frobeniusSq A = 0 ↔ A = 0 := by
  let T := A.toEuclideanLin
  constructor
  · intro h
    have hsum :
        ∑ i ∈ T.singularValues.support, T.singularValues i ^ 2 = 0 := by
      simpa [frobeniusSq, Finsupp.sum, T] using h
    have hall : ∀ i ∈ T.singularValues.support, T.singularValues i ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (T.singularValues i)).mp hsum
    have hsv : T.singularValues = 0 := by
      ext i
      by_cases hi : i ∈ T.singularValues.support
      · exact sq_eq_zero_iff.mp (hall i hi)
      · exact Finsupp.notMem_support_iff.mp hi
    have hT : T = 0 := (T.singularValues_eq_zero_iff).mp hsv
    exact Matrix.toEuclideanLin.injective (by simpa [T] using hT)
  · rintro rfl
    exact frobeniusSq_zero

/-- The Frobenius norm vanishes exactly at the zero matrix. -/
theorem frobeniusNorm_eq_zero_iff (A : Matrix ι ι ℂ) :
    frobeniusNorm A = 0 ↔ A = 0 := by
  rw [frobeniusNorm, Real.sqrt_eq_zero']
  exact ⟨fun h => (frobeniusSq_eq_zero_iff A).mp (le_antisymm h (frobeniusSq_nonneg A)),
    fun h => h ▸ by simp⟩

/-- Matrix rank is bounded by the ambient Hilbert-space dimension. -/
theorem matrixRank_le_card (A : Matrix ι ι ℂ) : matrixRank A ≤ Fintype.card ι := by
  simpa [matrixRank, finrank_euclideanSpace] using A.toEuclideanLin.finrank_range_le

/-- Cauchy--Schwarz for singular values: the squared trace norm is at most
rank times squared Frobenius norm. -/
theorem traceNorm_sq_le_rank_mul_frobeniusSq (A : Matrix ι ι ℂ) :
    traceNorm A ^ 2 ≤ (matrixRank A : ℝ) * frobeniusSq A := by
  let T := A.toEuclideanLin
  have hcs :
      (∑ i ∈ T.singularValues.support, T.singularValues i) ^ 2 ≤
        (T.singularValues.support.card : ℝ) *
          ∑ i ∈ T.singularValues.support, T.singularValues i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  simpa [traceNorm, frobeniusSq, matrixRank, T,
    Finsupp.sum, LinearMap.card_support_singularValues] using hcs

/-- The usual rank comparison between Schatten one and Frobenius norms. -/
theorem traceNorm_le_sqrt_rank_mul_frobeniusNorm (A : Matrix ι ι ℂ) :
    traceNorm A ≤ Real.sqrt (matrixRank A) * frobeniusNorm A := by
  have hrank : 0 ≤ (matrixRank A : ℝ) := Nat.cast_nonneg _
  have hfrobSq : 0 ≤ frobeniusSq A := frobeniusSq_nonneg A
  have hsquare :
      traceNorm A ^ 2 ≤
        (Real.sqrt (matrixRank A) * frobeniusNorm A) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrank, frobeniusNorm_sq]
    exact traceNorm_sq_le_rank_mul_frobeniusSq A
  exact (sq_le_sq₀ (traceNorm_nonneg A)
    (mul_nonneg (Real.sqrt_nonneg _) (frobeniusNorm_nonneg A))).mp hsquare

end SingularNorms

section HermitianSpectralNorm

/-!
The tomography error is Hermitian.  On that subspace we can build the
Schatten-one norm directly from the absolute eigenvalues and prove its norm
laws without first developing a general singular-value perturbation theory.
The key argument uses the spectral sign of a Hermitian matrix as a dual
witness.  This is definitionally the intended trace loss on state
differences; no ordering of `IsHermitian.eigenvalues` is used below.
-/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Scalar sign, embedded in `ℂ`, used to construct the spectral sign
matrix. -/
noncomputable def spectralSignCoeff (x : ℝ) : ℂ :=
  if x < 0 then -1 else if 0 < x then 1 else 0

theorem norm_spectralSignCoeff_le_one (x : ℝ) :
    ‖spectralSignCoeff x‖ ≤ 1 := by
  unfold spectralSignCoeff
  split_ifs <;> norm_num

theorem spectralSignCoeff_mul (x : ℝ) :
    spectralSignCoeff x * (x : ℂ) = (|x| : ℝ) := by
  unfold spectralSignCoeff
  split_ifs with hneg hpos
  · rw [abs_of_neg hneg]
    push_cast
    ring
  · rw [abs_of_pos hpos]
    ring
  · have hx : x = 0 := le_antisymm (not_lt.mp hpos) (not_lt.mp hneg)
    simp [hx]

/-- The spectral sign of a Hermitian matrix. -/
noncomputable def spectralSign (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
    (Matrix.diagonal (spectralSignCoeff ∘ hA.eigenvalues))

/-- Hermitian Schatten-one norm: the sum of the absolute eigenvalues. -/
noncomputable def hermitianTraceNorm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, |hA.eigenvalues i|

/-- The matrix operator norm, expressed through the represented continuous
linear map so it does not depend on opening a scoped matrix-norm instance. -/
noncomputable def matrixOperatorNorm (A : Matrix ι ι ℂ) : ℝ :=
  ‖A.toEuclideanLin.toContinuousLinearMap‖

open scoped Matrix.Norms.L2Operator in
theorem spectralSign_l2OperatorNorm_le_one
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖spectralSign A hA‖ ≤ 1 := by
  simp only [spectralSign, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i =>
    norm_spectralSignCoeff_le_one _

/-- The sign witness attains the Hermitian trace norm. -/
theorem trace_spectralSign_mul
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (spectralSign A hA * A).trace = hermitianTraceNorm A hA := by
  rw (occs := .pos [2]) [hA.spectral_theorem]
  change (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (spectralSignCoeff ∘ hA.eigenvalues)) *
    Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))).trace = _
  rw [← map_mul]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
    hermitianTraceNorm, Matrix.diagonal_mul_diagonal, Function.comp_apply]
  refine (Finset.sum_congr rfl
    (g := fun i => ((|hA.eigenvalues i| : ℝ) : ℂ)) ?_).trans ?_
  · intro i hi
    exact spectralSignCoeff_mul _
  · exact (Complex.ofReal_sum (Finset.univ : Finset ι)
      (fun i : ι => (|hA.eigenvalues i| : ℝ))).symm

theorem hermitianTraceNorm_nonneg
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    0 ≤ hermitianTraceNorm A hA := by
  exact Finset.sum_nonneg fun i _ => abs_nonneg _

/-- For a positive-semidefinite matrix, the Hermitian trace norm is its
trace. -/
theorem hermitianTraceNorm_psd_eq_re_trace
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) :
    hermitianTraceNorm A hA.isHermitian = A.trace.re := by
  rw [hermitianTraceNorm]
  simp_rw [abs_of_nonneg (hA.eigenvalues_nonneg _)]
  have ht := hA.isHermitian.trace_eq_sum_eigenvalues
  rw [ht]
  simp

/-- Density operators have Hermitian trace norm one. -/
theorem density_hermitianTraceNorm_eq_one (ρ : DensityOperator ι) :
    hermitianTraceNorm ρ.matrix ρ.isHermitian = 1 := by
  rw [hermitianTraceNorm_psd_eq_re_trace ρ.matrix ρ.posSemidef,
    ρ.trace_eq_one]
  norm_num

/-- Eigenvector equation expressed through `Matrix.toEuclideanLin`. -/
theorem toEuclideanLin_eigenvectorBasis
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    A.toEuclideanLin (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
  change A.toEuclideanLin (hA.eigenvectorBasis i) =
    (hA.eigenvalues i : ℝ) • hA.eigenvectorBasis i
  apply PiLp.ext
  intro j
  exact congrFun (hA.mulVec_eigenvectorBasis i) j

/-- The same eigenvector equation in the explicit standard basis. -/
theorem toLin_eigenvectorBasis
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) :
    Matrix.toLin (EuclideanSpace.basisFun ι ℂ).toBasis
        (EuclideanSpace.basisFun ι ℂ).toBasis A (hA.eigenvectorBasis i) =
      (hA.eigenvalues i : ℂ) • hA.eigenvectorBasis i := by
  exact toEuclideanLin_eigenvectorBasis A hA i

/-- Trace/operator duality for a Hermitian trace-class factor. -/
theorem norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖(B * A).trace‖ ≤
      hermitianTraceNorm A hA * matrixOperatorNorm B := by
  let e := (EuclideanSpace.basisFun ι ℂ).toBasis
  rw [← Matrix.trace_toLin_eq (B * A) e, Matrix.toLin_mul e e]
  dsimp [e]
  rw [LinearMap.trace_eq_sum_inner _ hA.eigenvectorBasis]
  simp_rw [LinearMap.comp_apply, toLin_eigenvectorBasis]
  simp_rw [map_smul, inner_smul_right]
  calc
    ‖∑ i, (hA.eigenvalues i : ℂ) *
        ⟪hA.eigenvectorBasis i,
          B.toEuclideanLin (hA.eigenvectorBasis i)⟫_ℂ‖
      ≤ ∑ i, ‖(hA.eigenvalues i : ℂ) *
        ⟪hA.eigenvectorBasis i,
          B.toEuclideanLin (hA.eigenvectorBasis i)⟫_ℂ‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i, |hA.eigenvalues i| * matrixOperatorNorm B := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      gcongr
      calc
        ‖⟪hA.eigenvectorBasis i,
            B.toEuclideanLin (hA.eigenvectorBasis i)⟫_ℂ‖
          ≤ ‖hA.eigenvectorBasis i‖ *
              ‖B.toEuclideanLin (hA.eigenvectorBasis i)‖ :=
            norm_inner_le_norm _ _
        _ ≤ 1 * (matrixOperatorNorm B * 1) := by
          rw [hA.eigenvectorBasis.norm_eq_one]
          gcongr
          simpa [matrixOperatorNorm, hA.eigenvectorBasis.norm_eq_one] using
            B.toEuclideanLin.toContinuousLinearMap.le_opNorm
              (hA.eigenvectorBasis i)
        _ = matrixOperatorNorm B := by ring
    _ = hermitianTraceNorm A hA * matrixOperatorNorm B := by
      simp [hermitianTraceNorm, Finset.sum_mul]

theorem matrixOperatorNorm_spectralSign_le_one
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    matrixOperatorNorm (spectralSign A hA) ≤ 1 := by
  open scoped Matrix.Norms.L2Operator in
    change ‖spectralSign A hA‖ ≤ 1
    exact spectralSign_l2OperatorNorm_le_one A hA

/-- Triangle inequality for the Hermitian trace norm, proved using the sign
of `A + B` as a dual witness. -/
theorem hermitianTraceNorm_triangle
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hermitianTraceNorm (A + B) (hA.add hB) ≤
      hermitianTraceNorm A hA + hermitianTraceNorm B hB := by
  let S := spectralSign (A + B) (hA.add hB)
  have hw := trace_spectralSign_mul (A + B) (hA.add hB)
  have hSA := norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm A S hA
  have hSB := norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm B S hB
  have hS : matrixOperatorNorm S ≤ 1 :=
    matrixOperatorNorm_spectralSign_le_one _ _
  calc
    hermitianTraceNorm (A + B) (hA.add hB) =
        ‖(S * (A + B)).trace‖ := by
      rw [hw, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hermitianTraceNorm_nonneg _ _)]
    _ = ‖(S * A).trace + (S * B).trace‖ := by
      rw [mul_add, Matrix.trace_add]
    _ ≤ ‖(S * A).trace‖ + ‖(S * B).trace‖ := norm_add_le _ _
    _ ≤ hermitianTraceNorm A hA * matrixOperatorNorm S +
        hermitianTraceNorm B hB * matrixOperatorNorm S :=
      add_le_add hSA hSB
    _ ≤ hermitianTraceNorm A hA * 1 + hermitianTraceNorm B hB * 1 := by
      gcongr <;> exact hermitianTraceNorm_nonneg _ _
    _ = hermitianTraceNorm A hA + hermitianTraceNorm B hB := by ring

theorem matrixOperatorNorm_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ matrixOperatorNorm A := norm_nonneg _

theorem matrixOperatorNorm_mul_le (A B : Matrix ι ι ℂ) :
    matrixOperatorNorm (A * B) ≤
      matrixOperatorNorm A * matrixOperatorNorm B := by
  open scoped Matrix.Norms.L2Operator in
    change ‖A * B‖ ≤ ‖A‖ * ‖B‖
    exact Matrix.l2_opNorm_mul A B

theorem matrixOperatorNorm_neg (A : Matrix ι ι ℂ) :
    matrixOperatorNorm (-A) = matrixOperatorNorm A := by
  simp [matrixOperatorNorm]

private theorem hermitianTraceNorm_neg_le
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm (-A) hA.neg ≤ hermitianTraceNorm A hA := by
  let S := spectralSign (-A) hA.neg
  have hw := trace_spectralSign_mul (-A) hA.neg
  have hd := norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm A (-S) hA
  have hS : matrixOperatorNorm (-S) ≤ 1 := by
    rw [matrixOperatorNorm_neg]
    exact matrixOperatorNorm_spectralSign_le_one _ _
  calc
    hermitianTraceNorm (-A) hA.neg = ‖(S * (-A)).trace‖ := by
      rw [hw, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hermitianTraceNorm_nonneg _ _)]
    _ = ‖((-S) * A).trace‖ := by rw [neg_mul, mul_neg]
    _ ≤ hermitianTraceNorm A hA * matrixOperatorNorm (-S) := hd
    _ ≤ hermitianTraceNorm A hA * 1 :=
      mul_le_mul_of_nonneg_left hS (hermitianTraceNorm_nonneg _ _)
    _ = hermitianTraceNorm A hA := mul_one _

/-- Symmetry of the Hermitian trace norm. -/
theorem hermitianTraceNorm_neg
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm (-A) hA.neg = hermitianTraceNorm A hA := by
  apply le_antisymm (hermitianTraceNorm_neg_le A hA)
  have h := hermitianTraceNorm_neg_le (-A) hA.neg
  simpa using h

/-- Subtraction form of the Hermitian trace-norm triangle inequality. -/
theorem hermitianTraceNorm_sub_triangle
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hermitianTraceNorm (A - B) (hA.sub hB) ≤
      hermitianTraceNorm A hA + hermitianTraceNorm B hB := by
  have h := hermitianTraceNorm_triangle A (-B) hA hB.neg
  rw [hermitianTraceNorm_neg B hB] at h
  simpa [sub_eq_add_neg] using h

/-- The Hermitian trace loss between any two density operators is at most
two. -/
theorem density_hermitianTraceNorm_sub_le_two
    (σ ρ : DensityOperator ι) :
    hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) ≤ 2 := by
  have htri := hermitianTraceNorm_triangle σ.matrix (-ρ.matrix)
    σ.isHermitian ρ.isHermitian.neg
  rw [hermitianTraceNorm_neg ρ.matrix ρ.isHermitian,
    density_hermitianTraceNorm_eq_one σ,
    density_hermitianTraceNorm_eq_one ρ] at htri
  norm_num at htri
  simpa [sub_eq_add_neg] using htri

/-- A Hermitian sandwich `P A P` is Hermitian. -/
theorem sandwich_isHermitian
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian) :
    (P * A * P).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [hP.eq, hA.eq, mul_assoc]

/-- Compression by a Hermitian operator-norm contraction cannot increase the
Hermitian trace norm. -/
theorem hermitianTraceNorm_sandwich_le
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian)
    (hPnorm : matrixOperatorNorm P ≤ 1) :
    hermitianTraceNorm (P * A * P) (sandwich_isHermitian P A hP hA) ≤
      hermitianTraceNorm A hA := by
  let C := P * A * P
  let hC : C.IsHermitian := sandwich_isHermitian P A hP hA
  let S := spectralSign C hC
  have hw := trace_spectralSign_mul C hC
  have hSnorm : matrixOperatorNorm S ≤ 1 :=
    matrixOperatorNorm_spectralSign_le_one _ _
  have hPSP : matrixOperatorNorm (P * S * P) ≤ 1 := by
    calc
      matrixOperatorNorm (P * S * P) ≤
          matrixOperatorNorm (P * S) * matrixOperatorNorm P :=
        matrixOperatorNorm_mul_le _ _
      _ ≤ (matrixOperatorNorm P * matrixOperatorNorm S) *
          matrixOperatorNorm P :=
        mul_le_mul_of_nonneg_right (matrixOperatorNorm_mul_le P S)
          (matrixOperatorNorm_nonneg P)
      _ ≤ (1 * 1) * 1 := by
        gcongr <;> exact matrixOperatorNorm_nonneg _
      _ = 1 := by ring
  have htrace : (S * C).trace = ((P * S * P) * A).trace := by
    calc
      (S * C).trace = (S * (P * A) * P).trace := by simp [C, mul_assoc]
      _ = (P * S * (P * A)).trace := Matrix.trace_mul_cycle _ _ _
      _ = ((P * S * P) * A).trace := by simp [mul_assoc]
  have hd :=
    norm_trace_mul_le_hermitianTraceNorm_mul_operatorNorm A (P * S * P) hA
  calc
    hermitianTraceNorm (P * A * P) (sandwich_isHermitian P A hP hA) =
        hermitianTraceNorm C hC := by rfl
    _ = ‖(S * C).trace‖ := by
      rw [hw, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hermitianTraceNorm_nonneg _ _)]
    _ = ‖((P * S * P) * A).trace‖ := by rw [htrace]
    _ ≤ hermitianTraceNorm A hA * matrixOperatorNorm (P * S * P) := hd
    _ ≤ hermitianTraceNorm A hA * 1 :=
      mul_le_mul_of_nonneg_left hPSP (hermitianTraceNorm_nonneg _ _)
    _ = hermitianTraceNorm A hA := mul_one _

/-- A Hermitian sandwich of a positive-semidefinite matrix is
positive-semidefinite. -/
theorem sandwich_posSemidef
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.PosSemidef) :
    (P * A * P).PosSemidef := by
  have h := hA.conjTranspose_mul_mul_same P
  rwa [hP.eq] at h

/-- Trace of an idempotent sandwich. -/
theorem trace_sandwich_of_isIdempotent
    (P A : Matrix ι ι ℂ) (hP : IsIdempotentElem P) :
    (P * A * P).trace = (P * A).trace := by
  calc
    _ = (P * P * A).trace := Matrix.trace_mul_cycle _ _ _
    _ = _ := by rw [hP]

/-- The complementary matrix of an idempotent is idempotent. -/
theorem isIdempotentElem_one_sub
    (P : Matrix ι ι ℂ) (hP : IsIdempotentElem P) :
    IsIdempotentElem (1 - P) := by
  rw [IsIdempotentElem]
  calc
    (1 - P) * (1 - P) = 1 - P - P + P * P := by noncomm_ring
    _ = 1 - P - P + P := by rw [hP]
    _ = 1 - P := by noncomm_ring

/-- The traces of the two diagonal blocks induced by an idempotent sum to
the total trace. -/
theorem trace_projection_blocks
    (P A : Matrix ι ι ℂ) (hP : IsIdempotentElem P) :
    (P * A * P).trace + ((1 - P) * A * (1 - P)).trace = A.trace := by
  rw [trace_sandwich_of_isIdempotent P A hP,
    trace_sandwich_of_isIdempotent (1 - P) A
      (isIdempotentElem_one_sub P hP)]
  rw [← Matrix.trace_add]
  congr 1
  noncomm_ring

/-- Exact tail relation resulting from trace-zero state differences.  With
`Q = I - P` and `Delta = sigma - rho`, it says
`tr(Q sigma Q) + tr(Q rho Q) = -tr(P Delta P) + 2 tr(Q rho Q)`.
This is the deterministic identity used in the PSD cone proof. -/
theorem density_projection_tail_relation
    (σ ρ : DensityOperator ι) (P : Matrix ι ι ℂ)
    (hP : IsIdempotentElem P) :
    let Δ := σ.matrix - ρ.matrix
    let Q := 1 - P
    (Q * σ.matrix * Q).trace.re + (Q * ρ.matrix * Q).trace.re =
      -(P * Δ * P).trace.re + 2 * (Q * ρ.matrix * Q).trace.re := by
  dsimp
  have hz := trace_projection_blocks P (σ.matrix - ρ.matrix) hP
  rw [σ.trace_sub_eq_zero ρ] at hz
  have hmat :
      (1 - P) * (σ.matrix - ρ.matrix) * (1 - P) =
        (1 - P) * σ.matrix * (1 - P) -
          (1 - P) * ρ.matrix * (1 - P) := by
    noncomm_ring
  have hc :
      ((1 - P) * (σ.matrix - ρ.matrix) * (1 - P)).trace =
        ((1 - P) * σ.matrix * (1 - P)).trace -
          ((1 - P) * ρ.matrix * (1 - P)).trace := by
    rw [hmat, Matrix.trace_sub]
  rw [hc] at hz
  have hre := congrArg Complex.re hz
  simp only [Complex.add_re, Complex.sub_re, Complex.zero_re] at hre
  linarith

/-- The Hermitian spectral norm is independent of the proof of Hermiticity
and respects equality of its matrix argument. -/
theorem hermitianTraceNorm_congr
    {A B : Matrix ι ι ℂ} (h : A = B)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    hermitianTraceNorm A hA = hermitianTraceNorm B hB := by
  subst B
  rfl

/-- The complement of a Hermitian matrix is Hermitian. -/
theorem one_sub_isHermitian
    (P : Matrix ι ι ℂ) (hP : P.IsHermitian) : (1 - P).IsHermitian :=
  Matrix.isHermitian_one.sub hP

/-- Absolute trace is bounded by the Hermitian trace norm. -/
theorem abs_re_trace_le_hermitianTraceNorm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    |A.trace.re| ≤ hermitianTraceNorm A hA := by
  have ht := hA.trace_eq_sum_eigenvalues
  have hre := congrArg Complex.re ht
  simp at hre
  rw [hre, hermitianTraceNorm]
  exact Finset.abs_sum_le_sum_abs _ _

/-- PSD feasibility controls the complementary error block by the leading
error block plus twice the spectral tail.  This is the trace part of the
matrix cone inequality. -/
theorem density_complement_block_traceNorm_le
    (σ ρ : DensityOperator ι) (P : Matrix ι ι ℂ)
    (hP : P.IsHermitian) (hid : IsIdempotentElem P) :
    let Δ := σ.matrix - ρ.matrix
    let Q := 1 - P
    hermitianTraceNorm (Q * Δ * Q)
        (sandwich_isHermitian Q Δ (one_sub_isHermitian P hP)
          (σ.sub_isHermitian ρ)) ≤
      hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP (σ.sub_isHermitian ρ)) +
        2 * (Q * ρ.matrix * Q).trace.re := by
  dsimp
  let Q : Matrix ι ι ℂ := 1 - P
  let Δ := σ.matrix - ρ.matrix
  have hQ : Q.IsHermitian := one_sub_isHermitian P hP
  have hΔ : Δ.IsHermitian := σ.sub_isHermitian ρ
  let X := Q * σ.matrix * Q
  let Y := Q * ρ.matrix * Q
  have hX : X.PosSemidef :=
    sandwich_posSemidef Q σ.matrix hQ σ.posSemidef
  have hY : Y.PosSemidef :=
    sandwich_posSemidef Q ρ.matrix hQ ρ.posSemidef
  have hmat : X - Y = Q * Δ * Q := by
    simp [X, Y, Δ]
    noncomm_ring
  have hsub :=
    hermitianTraceNorm_sub_triangle X Y hX.isHermitian hY.isHermitian
  have heqNorm :
      hermitianTraceNorm (Q * Δ * Q)
          (sandwich_isHermitian Q Δ hQ hΔ) =
        hermitianTraceNorm (X - Y)
          (hX.isHermitian.sub hY.isHermitian) := by
    exact hermitianTraceNorm_congr hmat.symm _ _
  have hsub' :
      hermitianTraceNorm (Q * Δ * Q)
          (sandwich_isHermitian Q Δ hQ hΔ) ≤ X.trace.re + Y.trace.re := by
    rw [heqNorm]
    calc
      hermitianTraceNorm (X - Y) (hX.isHermitian.sub hY.isHermitian) ≤
          hermitianTraceNorm X hX.isHermitian +
            hermitianTraceNorm Y hY.isHermitian := hsub
      _ = X.trace.re + Y.trace.re := by
        rw [hermitianTraceNorm_psd_eq_re_trace X hX,
          hermitianTraceNorm_psd_eq_re_trace Y hY]
  have hrel := density_projection_tail_relation σ ρ P hid
  dsimp [Q, Δ] at hrel
  have htr :
      -(P * Δ * P).trace.re ≤
        hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) :=
    le_trans (neg_le_abs _) (abs_re_trace_le_hermitianTraceNorm _ _)
  calc
    _ ≤ X.trace.re + Y.trace.re := hsub'
    _ = -(P * Δ * P).trace.re + 2 * (Q * ρ.matrix * Q).trace.re := by
      simpa [X, Y, Q, Δ] using hrel
    _ ≤ hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) +
        2 * (Q * ρ.matrix * Q).trace.re := by linarith

/-- Spectral rank: the number of nonzero eigenvalues. -/
noncomputable def hermitianRank
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℕ :=
  (Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card

/-- Sum of squared Hermitian eigenvalues. -/
noncomputable def hermitianFrobeniusSq
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  ∑ i, hA.eigenvalues i ^ 2

/-- Hermitian Frobenius norm. -/
noncomputable def hermitianFrobeniusNorm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℝ :=
  Real.sqrt (hermitianFrobeniusSq A hA)

theorem hermitianFrobeniusSq_nonneg
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    0 ≤ hermitianFrobeniusSq A hA := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

theorem hermitianFrobeniusNorm_nonneg
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    0 ≤ hermitianFrobeniusNorm A hA :=
  Real.sqrt_nonneg _

theorem hermitianFrobeniusNorm_sq
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianFrobeniusNorm A hA ^ 2 = hermitianFrobeniusSq A hA :=
  Real.sq_sqrt (hermitianFrobeniusSq_nonneg A hA)

theorem hermitianTraceNorm_sq_le_rank_mul_frobeniusSq
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm A hA ^ 2 ≤
      (hermitianRank A hA : ℝ) * hermitianFrobeniusSq A hA := by
  let s := Finset.univ.filter fun i => hA.eigenvalues i ≠ 0
  have hsum_abs :
      (∑ i ∈ s, |hA.eigenvalues i|) = ∑ i, |hA.eigenvalues i| := by
    apply Finset.sum_filter_of_ne
    intro i hi hne
    contrapose! hne
    simp [hne]
  have hsum_sq :
      (∑ i ∈ s, hA.eigenvalues i ^ 2) =
        ∑ i, hA.eigenvalues i ^ 2 := by
    apply Finset.sum_filter_of_ne
    intro i hi hne
    contrapose! hne
    simp [hne]
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := s) (f := fun i => |hA.eigenvalues i|)
  rw [hsum_abs] at hcs
  simp_rw [sq_abs] at hcs
  rw [hsum_sq] at hcs
  simpa [hermitianTraceNorm, hermitianRank, hermitianFrobeniusSq, s]
    using hcs

/-- Hermitian Schatten rank inequality. -/
theorem hermitianTraceNorm_le_sqrt_rank_mul_frobeniusNorm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm A hA ≤
      Real.sqrt (hermitianRank A hA) * hermitianFrobeniusNorm A hA := by
  have hrank : 0 ≤ (hermitianRank A hA : ℝ) := Nat.cast_nonneg _
  have hsquare :
      hermitianTraceNorm A hA ^ 2 ≤
        (Real.sqrt (hermitianRank A hA) *
          hermitianFrobeniusNorm A hA) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hrank, hermitianFrobeniusNorm_sq]
    exact hermitianTraceNorm_sq_le_rank_mul_frobeniusSq A hA
  exact (sq_le_sq₀ (hermitianTraceNorm_nonneg A hA)
    (mul_nonneg (Real.sqrt_nonneg _)
      (hermitianFrobeniusNorm_nonneg A hA))).mp hsquare

theorem hermitianRank_eq_rank
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianRank A hA = A.rank := by
  rw [hermitianRank, hA.rank_eq_card_non_zero_eigs]
  exact (Fintype.card_subtype (fun i => hA.eigenvalues i ≠ 0)).symm

/-!
## Projection block geometry

For a Hermitian projection `P`, the error is split into its tangent part
`P A + (I-P) A P` and complementary block `(I-P) A (I-P)`.  The following
lemmas prove the trace-norm cone inequality directly from positivity, rank,
and Hilbert--Schmidt orthogonality.  No cone estimate is assumed.
-/

/-- Tangent component relative to a projection. -/
noncomputable def projectionTangent
    (P A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  P * A + (1 - P) * A * P

/-- Complementary diagonal block relative to a projection. -/
noncomputable def projectionRemainder
    (P A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (1 - P) * A * (1 - P)

theorem projectionTangent_isHermitian
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian) :
    (projectionTangent P A).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [projectionTangent, hP.eq, hA.eq, mul_assoc]
  noncomm_ring

theorem projectionRemainder_isHermitian
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian) :
    (projectionRemainder P A).IsHermitian := by
  exact sandwich_isHermitian (1 - P) A (one_sub_isHermitian P hP) hA

/-- Algebraic tangent-plus-remainder decomposition. -/
theorem projectionTangent_add_remainder
    (P A : Matrix ι ι ℂ) :
    projectionTangent P A + projectionRemainder P A = A := by
  simp [projectionTangent, projectionRemainder]
  noncomm_ring

theorem matrix_rank_add_le (A B : Matrix ι ι ℂ) :
    (A + B).rank ≤ A.rank + B.rank := by
  let e := (EuclideanSpace.basisFun ι ℂ).toBasis
  rw [Matrix.rank_eq_finrank_range_toLin (A + B) e e,
    Matrix.rank_eq_finrank_range_toLin A e e,
    Matrix.rank_eq_finrank_range_toLin B e e]
  rw [map_add]
  change Module.finrank ℂ ((Matrix.toLin e e A + Matrix.toLin e e B).range) ≤ _
  exact (Submodule.finrank_mono (LinearMap.range_add_le _ _)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

/-- The projection tangent space has rank at most twice the projection rank. -/
theorem projectionTangent_rank_le (P A : Matrix ι ι ℂ) :
    (projectionTangent P A).rank ≤ 2 * P.rank := by
  calc
    (projectionTangent P A).rank ≤
        (P * A).rank + ((1 - P) * A * P).rank := matrix_rank_add_le _ _
    _ ≤ P.rank + P.rank := by
      gcongr
      · exact Matrix.rank_mul_le_left _ _
      · exact Matrix.rank_mul_le_right ((1 - P) * A) P
    _ = 2 * P.rank := by omega

/-- For a Hermitian matrix, trace of the square is its squared Frobenius
norm. -/
theorem trace_sq_eq_hermitianFrobeniusSq
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (A * A).trace = hermitianFrobeniusSq A hA := by
  rw (occs := .pos [1, 2]) [hA.spectral_theorem]
  rw [← map_mul]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
    Matrix.diagonal_mul_diagonal, Function.comp_apply,
    hermitianFrobeniusSq]
  refine (Finset.sum_congr rfl
    (g := fun i => ((hA.eigenvalues i ^ 2 : ℝ) : ℂ)) ?_).trans ?_
  · intro i hi
    push_cast
    rw [pow_two]
    rfl
  · exact (Complex.ofReal_sum (Finset.univ : Finset ι)
      (fun i : ι => hA.eigenvalues i ^ 2)).symm

theorem projection_complements_mul_zero
    (P : Matrix ι ι ℂ) (hid : IsIdempotentElem P) :
    P * (1 - P) = 0 := by
  calc
    P * (1 - P) = P - P * P := by noncomm_ring
    _ = 0 := by rw [hid]; exact sub_self P

theorem complement_mul_projection_zero
    (P : Matrix ι ι ℂ) (hid : IsIdempotentElem P) :
    (1 - P) * P = 0 := by
  calc
    (1 - P) * P = P - P * P := by noncomm_ring
    _ = 0 := by rw [hid]; exact sub_self P

theorem trace_projectionTangent_mul_remainder_zero
    (P A : Matrix ι ι ℂ) (hid : IsIdempotentElem P) :
    (projectionTangent P A * projectionRemainder P A).trace = 0 := by
  let Q : Matrix ι ι ℂ := 1 - P
  have hPQ : P * Q = 0 := by
    simpa [Q] using projection_complements_mul_zero P hid
  have hQP : Q * P = 0 := by
    simpa [Q] using complement_mul_projection_zero P hid
  have hfirst : ((P * A) * (Q * A * Q)).trace = 0 := by
    calc
      ((P * A) * (Q * A * Q)).trace =
          (Q * A * Q * P * A).trace := by
        rw [show ((P * A) * (Q * A * Q)).trace =
          (P * A * (Q * A * Q)).trace by simp [mul_assoc]]
        exact Matrix.trace_mul_cycle P A (Q * A * Q)
      _ = 0 := by simp [hQP, mul_assoc]
  have hsecond : ((Q * A * P) * (Q * A * Q)).trace = 0 := by
    have hm : (Q * A * P) * (Q * A * Q) = 0 := by
      calc
        (Q * A * P) * (Q * A * Q) = Q * A * (P * Q) * A * Q := by
          noncomm_ring
        _ = 0 := by rw [hPQ]; simp
    rw [hm, Matrix.trace_zero]
  dsimp [projectionTangent, projectionRemainder]
  change (((P * A) + (Q * A * P)) * (Q * A * Q)).trace = 0
  rw [add_mul, Matrix.trace_add, hfirst, hsecond, add_zero]

theorem trace_projectionRemainder_mul_tangent_zero
    (P A : Matrix ι ι ℂ) (hid : IsIdempotentElem P) :
    (projectionRemainder P A * projectionTangent P A).trace = 0 := by
  calc
    (projectionRemainder P A * projectionTangent P A).trace =
        (projectionTangent P A * projectionRemainder P A).trace := by
      simpa using Matrix.trace_mul_cycle
        (projectionRemainder P A) (1 : Matrix ι ι ℂ)
        (projectionTangent P A)
    _ = 0 := trace_projectionTangent_mul_remainder_zero P A hid

/-- Exact Hilbert--Schmidt Pythagoras identity for the projection blocks. -/
theorem projectionTangent_frobeniusSq_add_remainder
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian)
    (hid : IsIdempotentElem P) :
    hermitianFrobeniusSq (projectionTangent P A)
        (projectionTangent_isHermitian P A hP hA) +
      hermitianFrobeniusSq (projectionRemainder P A)
        (projectionRemainder_isHermitian P A hP hA) =
      hermitianFrobeniusSq A hA := by
  let T := projectionTangent P A
  let R := projectionRemainder P A
  have hT : T.IsHermitian := projectionTangent_isHermitian P A hP hA
  have hR : R.IsHermitian := projectionRemainder_isHermitian P A hP hA
  have hD : T + R = A := projectionTangent_add_remainder P A
  have hTR : (T * R).trace = 0 :=
    trace_projectionTangent_mul_remainder_zero P A hid
  have hRT : (R * T).trace = 0 :=
    trace_projectionRemainder_mul_tangent_zero P A hid
  have hsquare : A * A = T * T + T * R + R * T + R * R := by
    rw [← hD]
    noncomm_ring
  have htrace : (A * A).trace = (T * T).trace + (R * R).trace := by
    rw [hsquare]
    simp only [Matrix.trace_add, hTR, hRT, add_zero]
  rw [trace_sq_eq_hermitianFrobeniusSq A hA,
    trace_sq_eq_hermitianFrobeniusSq T hT,
    trace_sq_eq_hermitianFrobeniusSq R hR] at htrace
  exact_mod_cast htrace.symm

theorem projectionTangent_frobeniusSq_le
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian)
    (hid : IsIdempotentElem P) :
    hermitianFrobeniusSq (projectionTangent P A)
        (projectionTangent_isHermitian P A hP hA) ≤
      hermitianFrobeniusSq A hA := by
  have hsum := projectionTangent_frobeniusSq_add_remainder P A hP hA hid
  have hrem := hermitianFrobeniusSq_nonneg (projectionRemainder P A)
    (projectionRemainder_isHermitian P A hP hA)
  linarith

theorem projectionTangent_frobeniusNorm_le
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian)
    (hid : IsIdempotentElem P) :
    hermitianFrobeniusNorm (projectionTangent P A)
        (projectionTangent_isHermitian P A hP hA) ≤
      hermitianFrobeniusNorm A hA := by
  exact Real.sqrt_le_sqrt
    (projectionTangent_frobeniusSq_le P A hP hA hid)

theorem projectionTangent_hermitianRank_le
    (P A : Matrix ι ι ℂ) (hP : P.IsHermitian) (hA : A.IsHermitian) :
    hermitianRank (projectionTangent P A)
        (projectionTangent_isHermitian P A hP hA) ≤ 2 * P.rank := by
  rw [hermitianRank_eq_rank]
  exact projectionTangent_rank_le P A

theorem projection_tangent_compression
    (P A : Matrix ι ι ℂ) (hid : IsIdempotentElem P) :
    P * projectionTangent P A * P = P * A * P := by
  simp only [projectionTangent, mul_add, add_mul]
  have hPQ := projection_complements_mul_zero P hid
  have hPP : P * P = P := hid
  calc
    P * (P * A) * P + P * ((1 - P) * A * P) * P =
        (P * P) * A * P + (P * (1 - P)) * A * (P * P) := by
      simp only [mul_assoc]
    _ = P * A * P := by rw [hPQ, hPP]; simp

/-- The full deterministic PSD projection-cone inequality.  Its premises
state only that `P` is an orthogonal projection of rank at most `s`; the cone
bound itself is derived. -/
theorem density_projection_cone
    (σ ρ : DensityOperator ι) (P : Matrix ι ι ℂ) (s : ℕ)
    (hP : P.IsHermitian) (hid : IsIdempotentElem P)
    (hPnorm : matrixOperatorNorm P ≤ 1) (hPrank : P.rank ≤ s) :
    let Δ := σ.matrix - ρ.matrix
    let Q := 1 - P
    hermitianTraceNorm Δ (σ.sub_isHermitian ρ) ≤
      2 * (Q * ρ.matrix * Q).trace.re +
        4 * Real.sqrt s *
          hermitianFrobeniusNorm Δ (σ.sub_isHermitian ρ) := by
  dsimp
  let Δ := σ.matrix - ρ.matrix
  let Q : Matrix ι ι ℂ := 1 - P
  let T := projectionTangent P Δ
  let R := projectionRemainder P Δ
  have hΔ : Δ.IsHermitian := σ.sub_isHermitian ρ
  have hT : T.IsHermitian := projectionTangent_isHermitian P Δ hP hΔ
  have hR : R.IsHermitian := projectionRemainder_isHermitian P Δ hP hΔ
  have hdec : T + R = Δ := projectionTangent_add_remainder P Δ
  have htri : hermitianTraceNorm Δ hΔ ≤
      hermitianTraceNorm T hT + hermitianTraceNorm R hR := by
    have ht := hermitianTraceNorm_triangle T R hT hR
    exact (hermitianTraceNorm_congr hdec (hT.add hR) hΔ).symm ▸ ht
  have hrem : hermitianTraceNorm R hR ≤
      hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) +
        2 * (Q * ρ.matrix * Q).trace.re := by
    change hermitianTraceNorm ((1 - P) * Δ * (1 - P)) _ ≤
      hermitianTraceNorm (P * Δ * P) _ +
        2 * ((1 - P) * ρ.matrix * (1 - P)).trace.re
    simpa [Δ] using density_complement_block_traceNorm_le σ ρ P hP hid
  have hcompress0 := hermitianTraceNorm_sandwich_le P T hP hT hPnorm
  have hPTP : P * T * P = P * Δ * P := by
    simpa [T] using projection_tangent_compression P Δ hid
  have hcompress :
      hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) ≤
        hermitianTraceNorm T hT := by
    rw [← hermitianTraceNorm_congr hPTP
      (sandwich_isHermitian P T hP hT)
      (sandwich_isHermitian P Δ hP hΔ)]
    exact hcompress0
  have hTrankNat : T.rank ≤ 2 * s :=
    (projectionTangent_rank_le P Δ).trans (Nat.mul_le_mul_left 2 hPrank)
  have hTrank : hermitianRank T hT ≤ 2 * s := by
    rw [hermitianRank_eq_rank]
    exact hTrankNat
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hcast : (hermitianRank T hT : ℝ) ≤ 2 * (s : ℝ) := by
    exact_mod_cast hTrank
  have hsqrt : Real.sqrt (hermitianRank T hT) ≤ 2 * Real.sqrt s := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (Nat.cast_nonneg _), mul_pow, Real.sq_sqrt hs]
    nlinarith
  have hTfrob := projectionTangent_frobeniusNorm_le P Δ hP hΔ hid
  have hTbound : hermitianTraceNorm T hT ≤
      2 * Real.sqrt s * hermitianFrobeniusNorm Δ hΔ := by
    calc
      hermitianTraceNorm T hT ≤
          Real.sqrt (hermitianRank T hT) *
            hermitianFrobeniusNorm T hT :=
        hermitianTraceNorm_le_sqrt_rank_mul_frobeniusNorm T hT
      _ ≤ (2 * Real.sqrt s) * hermitianFrobeniusNorm T hT := by
        gcongr
        exact hermitianFrobeniusNorm_nonneg T hT
      _ ≤ (2 * Real.sqrt s) * hermitianFrobeniusNorm Δ hΔ := by
        gcongr
      _ = 2 * Real.sqrt s * hermitianFrobeniusNorm Δ hΔ := rfl
  calc
    hermitianTraceNorm Δ hΔ ≤
        hermitianTraceNorm T hT + hermitianTraceNorm R hR := htri
    _ ≤ hermitianTraceNorm T hT +
        (hermitianTraceNorm (P * Δ * P)
          (sandwich_isHermitian P Δ hP hΔ) +
            2 * (Q * ρ.matrix * Q).trace.re) := by gcongr
    _ ≤ hermitianTraceNorm T hT +
        (hermitianTraceNorm T hT +
            2 * (Q * ρ.matrix * Q).trace.re) := by gcongr
    _ ≤ 2 * (2 * Real.sqrt s * hermitianFrobeniusNorm Δ hΔ) +
        2 * (Q * ρ.matrix * Q).trace.re := by linarith
    _ = 2 * (Q * ρ.matrix * Q).trace.re +
        4 * Real.sqrt s * hermitianFrobeniusNorm Δ hΔ := by ring

end HermitianSpectralNorm

section CurvatureReduction

/-- A typed version of the curvature/duality energy step.  Once the quadratic
curvature is bounded below by `a * f^2` and the empirical energy above by
`x * h`, it follows that `f^2 ≤ (h/a) * x`.

In tomography `x` is trace-norm error, `f` is Frobenius error, and `h` is the
dual forward-operator error. -/
theorem frobenius_energy_control
    (a x f h energy : ℝ)
    (ha : 0 < a) (hlower : a * f ^ 2 ≤ energy)
    (hupper : energy ≤ x * h) :
    f ^ 2 ≤ (h / a) * x := by
  have hax : a * f ^ 2 ≤ x * h := hlower.trans hupper
  calc
    f ^ 2 ≤ (x * h) / a := (le_div_iff₀ ha).2 (by nlinarith [hax])
    _ = (h / a) * x := by ring

/-- Combining a genuine matrix-level cone inequality with curvature gives
the desired scalar square-root reduction.  Unlike the old placeholder, the
energy hypotheses are exposed separately and the nonlinear step is proved. -/
theorem reduction_of_cone_curvature
    (s : ℕ) (a x tail f h energy : ℝ)
    (ha : 0 < a) (hx : 0 ≤ x) (hh : 0 ≤ h)
    (hcone : x ≤ 2 * tail + 4 * Real.sqrt s * f)
    (hlower : a * f ^ 2 ≤ energy)
    (hupper : energy ≤ x * h)
    (_hf : 0 ≤ f) :
    x ≤ 2 * tail +
      4 * Real.sqrt ((s : ℝ) * h / a) * Real.sqrt x := by
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg _
  have hz : 0 ≤ (s : ℝ) * h / a :=
    div_nonneg (mul_nonneg hs hh) ha.le
  have hf2 : f ^ 2 ≤ (h / a) * x :=
    frobenius_energy_control a x f h energy ha hlower hupper
  have hscaled : (Real.sqrt s * f) ^ 2 ≤ ((s : ℝ) * h / a) * x := by
    calc
      (Real.sqrt s * f) ^ 2 = (s : ℝ) * f ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hs]
      _ ≤ (s : ℝ) * ((h / a) * x) :=
        mul_le_mul_of_nonneg_left hf2 hs
      _ = ((s : ℝ) * h / a) * x := by ring
  have hcone' : x ≤ 2 * tail + 4 * (Real.sqrt s * f) := by
    simpa [mul_assoc] using hcone
  exact reduction_of_cone_and_energy x tail (Real.sqrt s * f)
    ((s : ℝ) * h / a) hx hz hcone' hscaled

/-- Matrix-specialized curvature reduction for the difference of two density
operators.  This theorem discharges all scalar square-root algebra.  Its three
remaining matrix premises are exactly the future lemmas to prove:

* the PSD block/cone inequality `hcone`;
* restricted curvature `hlower`;
* trace/operator duality applied to the forward error, `hupper`.

In particular, the desired square-root conclusion itself is not assumed. -/
theorem density_trace_reduction_of_matrix_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ ρ : DensityOperator ι) (s : ℕ)
    (a tail h energy : ℝ)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hcone :
      traceNorm (σ.matrix - ρ.matrix) ≤
        2 * tail + 4 * Real.sqrt s * frobeniusNorm (σ.matrix - ρ.matrix))
    (hlower :
      a * frobeniusNorm (σ.matrix - ρ.matrix) ^ 2 ≤ energy)
    (hupper :
      energy ≤ traceNorm (σ.matrix - ρ.matrix) * h) :
    traceNorm (σ.matrix - ρ.matrix) ≤
      2 * tail +
        4 * Real.sqrt ((s : ℝ) * h / a) *
          Real.sqrt (traceNorm (σ.matrix - ρ.matrix)) := by
  exact reduction_of_cone_curvature s a
    (traceNorm (σ.matrix - ρ.matrix)) tail
    (frobeniusNorm (σ.matrix - ρ.matrix)) h energy ha
    (traceNorm_nonneg _) hh hcone hlower hupper (frobeniusNorm_nonneg _)

/-- Hermitian-specialized curvature reduction.  Unlike the earlier
singular-value endpoint, all norm laws needed for this version have been
proved above on the Hermitian state-difference subspace. -/
theorem density_hermitianTrace_reduction_of_matrix_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ ρ : DensityOperator ι) (s : ℕ)
    (a tail h energy : ℝ)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hcone :
      hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) ≤
        2 * tail + 4 * Real.sqrt s *
          hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
            (σ.sub_isHermitian ρ))
    (hlower :
      a * hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
          (σ.sub_isHermitian ρ) ^ 2 ≤ energy)
    (hupper :
      energy ≤ hermitianTraceNorm (σ.matrix - ρ.matrix)
          (σ.sub_isHermitian ρ) * h) :
    hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) ≤
      2 * tail +
        4 * Real.sqrt ((s : ℝ) * h / a) *
          Real.sqrt (hermitianTraceNorm (σ.matrix - ρ.matrix)
            (σ.sub_isHermitian ρ)) := by
  exact reduction_of_cone_curvature s a
    (hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ)) tail
    (hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
      (σ.sub_isHermitian ρ)) h energy ha
    (hermitianTraceNorm_nonneg _ _) hh hcone hlower hupper
    (hermitianFrobeniusNorm_nonneg _ _)

/-- Projection-tail version of the density reduction.  The PSD cone input is
fully discharged by `density_projection_cone`; only the statistical energy
bounds remain. -/
theorem density_hermitianTrace_reduction_of_projection_bounds
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ ρ : DensityOperator ι) (P : Matrix ι ι ℂ) (s : ℕ)
    (a h energy : ℝ)
    (hP : P.IsHermitian) (hid : IsIdempotentElem P)
    (hPnorm : matrixOperatorNorm P ≤ 1) (hPrank : P.rank ≤ s)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hlower :
      a * hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
          (σ.sub_isHermitian ρ) ^ 2 ≤ energy)
    (hupper :
      energy ≤ hermitianTraceNorm (σ.matrix - ρ.matrix)
          (σ.sub_isHermitian ρ) * h) :
    let Q := 1 - P
    hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) ≤
      2 * (Q * ρ.matrix * Q).trace.re +
        4 * Real.sqrt ((s : ℝ) * h / a) *
          Real.sqrt (hermitianTraceNorm (σ.matrix - ρ.matrix)
            (σ.sub_isHermitian ρ)) := by
  dsimp
  apply density_hermitianTrace_reduction_of_matrix_bounds σ ρ s a
    (((1 - P) * ρ.matrix * (1 - P)).trace.re) h energy ha hh
  · exact density_projection_cone σ ρ P s hP hid hPnorm hPrank
  · exact hlower
  · exact hupper

end CurvatureReduction

end MatrixReduction

end TomographyOracleCore
