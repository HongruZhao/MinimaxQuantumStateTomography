import TomographyOracleCore.DensityCompact
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-! Frobenius geometry of the actual density-matrix constraint set.

Matrices are flattened into a Euclidean space so that the Hilbert projection
theorem applies to the Frobenius norm, without changing the operator-norm
instance used elsewhere in the tomography library. The projection below is
an exact-arithmetic specification; its computable approximation is a separate
obligation.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

abbrev FrobeniusMatrix (ι : Type*) [Fintype ι] := EuclideanSpace ℂ (ι × ι)

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def encode (A : Matrix ι ι ℂ) : FrobeniusMatrix ι :=
  WithLp.toLp 2 (fun ij => A ij.1 ij.2)

def decode (x : FrobeniusMatrix ι) : Matrix ι ι ℂ := fun i j => x (i, j)

@[simp] theorem decode_encode (A : Matrix ι ι ℂ) : decode (encode A) = A := rfl

@[simp] theorem encode_decode (x : FrobeniusMatrix ι) : encode (decode x) = x := by
  ext ij
  rfl

@[simp] theorem encode_add (A B : Matrix ι ι ℂ) :
    encode (A + B) = encode A + encode B := rfl

@[simp] theorem encode_sub (A B : Matrix ι ι ℂ) :
    encode (A - B) = encode A - encode B := rfl

@[simp] theorem encode_smul (c : ℝ) (A : Matrix ι ι ℂ) :
    encode (c • A) = c • encode A := rfl

@[simp] theorem decode_add (x y : FrobeniusMatrix ι) :
    decode (x + y) = decode x + decode y := rfl

@[simp] theorem decode_sub (x y : FrobeniusMatrix ι) :
    decode (x - y) = decode x - decode y := rfl

@[simp] theorem decode_smul (c : ℝ) (x : FrobeniusMatrix ι) :
    decode (c • x) = c • decode x := rfl

theorem norm_encode_sq (A : Matrix ι ι ℂ) :
    ‖encode A‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [encode, Fintype.sum_prod_type]

theorem continuous_decode : Continuous (decode : FrobeniusMatrix ι → Matrix ι ι ℂ) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact PiLp.continuous_apply 2 _ (i, j)

def densitySet : Set (FrobeniusMatrix ι) :=
  {x | (decode x).PosSemidef ∧ (decode x).trace = 1}

theorem encode_density_mem (ρ : DensityOperator ι) : encode ρ.matrix ∈ densitySet :=
  ⟨ρ.posSemidef, ρ.trace_eq_one⟩

theorem isClosed_densitySet : IsClosed (densitySet : Set (FrobeniusMatrix ι)) :=
  DensityCompact.isClosed_densityMatrixSet.preimage continuous_decode

theorem convex_densitySet : Convex ℝ (densitySet : Set (FrobeniusMatrix ι)) := by
  intro x hx y hy a b ha hb hab
  constructor
  · change (a • decode x + b • decode y).PosSemidef
    exact (hx.1.smul ha).add (hy.1.smul hb)
  · change (a • decode x + b • decode y).trace = 1
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hx.2, hy.2,
      ← add_smul, hab, one_smul]

def densityProjection (ρ₀ : DensityOperator ι) (x : FrobeniusMatrix ι) :
    FrobeniusMatrix ι :=
  Classical.choose (exists_norm_eq_iInf_of_complete_convex
    ⟨encode ρ₀.matrix, encode_density_mem ρ₀⟩
    isClosed_densitySet.isComplete convex_densitySet x)

theorem densityProjection_mem (ρ₀ : DensityOperator ι) (x : FrobeniusMatrix ι) :
    densityProjection ρ₀ x ∈ densitySet :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    ⟨encode ρ₀.matrix, encode_density_mem ρ₀⟩
    isClosed_densitySet.isComplete convex_densitySet x)).1

theorem densityProjection_minimizes (ρ₀ : DensityOperator ι) (x : FrobeniusMatrix ι) :
    ‖x - densityProjection ρ₀ x‖ =
      ⨅ y : (densitySet : Set (FrobeniusMatrix ι)), ‖x - (y : FrobeniusMatrix ι)‖ :=
  (Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex
    ⟨encode ρ₀.matrix, encode_density_mem ρ₀⟩
    isClosed_densitySet.isComplete convex_densitySet x)).2

theorem densityProjection_variational (ρ₀ : DensityOperator ι)
    (x y : FrobeniusMatrix ι) (hy : y ∈ densitySet) :
    ⟪x - densityProjection ρ₀ x, y - densityProjection ρ₀ x⟫_ℝ ≤ 0 :=
  (norm_eq_iInf_iff_real_inner_le_zero convex_densitySet
    (densityProjection_mem ρ₀ x)).1 (densityProjection_minimizes ρ₀ x) y hy

theorem densityProjection_distance_sq_le (ρ₀ : DensityOperator ι)
    (x y : FrobeniusMatrix ι) (hy : y ∈ densitySet) :
    ‖densityProjection ρ₀ x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  have hv := densityProjection_variational ρ₀ x y hy
  have hn := sq_nonneg ‖x - densityProjection ρ₀ x‖
  have he := norm_sub_sq_real (x - densityProjection ρ₀ x)
    (y - densityProjection ρ₀ x)
  rw [sub_sub_sub_cancel_right] at he
  rw [norm_sub_rev (y : FrobeniusMatrix ι)] at he
  nlinarith

/-- The matrix-valued exact projection is a genuine positive semidefinite,
trace-one matrix. No projection oracle is assumed. -/
def projectedDensity (ρ₀ : DensityOperator ι) (A : Matrix ι ι ℂ) : DensityOperator ι where
  matrix := decode (densityProjection ρ₀ (encode A))
  posSemidef := (densityProjection_mem ρ₀ (encode A)).1
  trace_eq_one := (densityProjection_mem ρ₀ (encode A)).2

/-- Actual Frobenius projection supplies the matrix potential estimate used
by projected subgradient descent. The two analytic premises describe the
selected subgradient, not a projection or convergence assumption. -/
theorem projected_subgradient_step (ρ₀ : DensityOperator ι)
    (x y g : FrobeniusMatrix ι) (hy : y ∈ densitySet)
    (h G gap : ℝ) (hh : 0 ≤ h) (hG : 0 ≤ G)
    (hsubgradient : gap ≤ ⟪g, x - y⟫_ℝ) (hgradient : ‖g‖ ≤ G) :
    ‖densityProjection ρ₀ (x - h • g) - y‖ ^ 2 ≤
      ‖x - y‖ ^ 2 - 2 * h * gap + h ^ 2 * G ^ 2 := by
  have hp := densityProjection_distance_sq_le ρ₀ (x - h • g) y hy
  have he := norm_sub_sq_real (x - y) (h • g)
  rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg hh,
    real_inner_comm g (x - y)] at he
  have hsq : ‖g‖ ^ 2 ≤ G ^ 2 := sq_le_sq₀ (norm_nonneg _) hG |>.2 hgradient
  have hmul := mul_le_mul_of_nonneg_left hsubgradient (show 0 ≤ 2 * h by positivity)
  have hvar := mul_le_mul_of_nonneg_left hsq (sq_nonneg h)
  have heq : x - h • g - y = x - y - h • g := by abel
  rw [heq] at hp
  nlinarith

end

end TomographyOracleCore.Revision.MatrixSolver
