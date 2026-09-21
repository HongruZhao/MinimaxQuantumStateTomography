import TomographyOracleCore.Revision.AlgorithmResourcesPowerArithmetic
import TomographyOracleCore.Revision.FinitePrecisionProjector
import TomographyOracleCore.Revision.FinitePrecisionFrankWolfe

/-!
# Executable rational density atoms and projection iteration

These definitions contain only rational arithmetic and finite matrix
operations. Their interpretation as complex density matrices is proved
below. In particular the rank-one atom requires no square-root operation.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open MatrixReduction MatrixSolver AlgorithmResources Matrix
open scoped ComplexOrder InnerProductSpace BigOperators

set_option maxHeartbeats 1000000

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def castQVector (v : ι → QComplex) : EuclideanSpace ℂ ι :=
  WithLp.toLp 2 (fun i => qComplexToComplex (v i))

theorem castQVector_ne_zero {v : ι → QComplex} (hv : v ≠ 0) :
    castQVector v ≠ 0 := by
  intro h
  apply hv
  funext i
  apply qComplexToComplex_injective
  have hi := congrArg (fun w : EuclideanSpace ℂ ι => w i) h
  simpa [castQVector] using hi

theorem qVectorNormSq_cast (v : ι → QComplex) :
    (qVectorNormSq v : ℝ) = ‖castQVector v‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [qVectorNormSq, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  change (qNormSq (v i) : ℝ) = ‖qComplexToComplex (v i)‖ ^ 2
  rw [← Complex.normSq_eq_norm_sq, qComplexToComplex_normSq]

@[simp] theorem castQMatrix_add (A B : Matrix ι ι QComplex) :
    castQMatrix (A + B) = castQMatrix A + castQMatrix B := by
  ext i j
  exact map_add qComplexToComplex _ _

@[simp] theorem castQMatrix_sub (A B : Matrix ι ι QComplex) :
    castQMatrix (A - B) = castQMatrix A - castQMatrix B := by
  ext i j
  exact map_sub qComplexToComplex _ _

@[simp] theorem castQMatrix_rat_smul (a : ℚ) (A : Matrix ι ι QComplex) :
    castQMatrix (a • A) = (a : ℝ) • castQMatrix A := by
  ext i j
  change qComplexToComplex (a • A i j) = (a : ℝ) • qComplexToComplex (A i j)
  simpa using map_ratCast_smul qComplexToComplex ℚ ℝ a (A i j)

@[simp] theorem castQMatrix_vecMulVec (v w : ι → QComplex) :
    castQMatrix (vecMulVec v w) =
      vecMulVec (fun i => qComplexToComplex (v i))
        (fun i => qComplexToComplex (w i)) := by
  ext i j
  exact map_mul qComplexToComplex _ _

/-- Exact rational-complex atom produced from a nonzero direction. -/
def qNormalizedProjector (v : ι → QComplex) : Matrix ι ι QComplex :=
  (qVectorNormSq v)⁻¹ • vecMulVec v (star v)

/-- The executable rational formula denotes the normalized PSD rank-one
projector used in the analytic convergence proof. -/
theorem cast_qNormalizedProjector (v : ι → QComplex) :
    castQMatrix (qNormalizedProjector v) = normalizedProjector (castQVector v) := by
  rw [qNormalizedProjector, castQMatrix_rat_smul, castQMatrix_vecMulVec]
  simp only [Rat.cast_inv, qVectorNormSq_cast, normalizedProjector, castQVector]
  congr 2
  funext i
  exact qComplexToComplex_star (v i)

theorem qNormalizedProjector_posSemidef (v : ι → QComplex) :
    (castQMatrix (qNormalizedProjector v)).PosSemidef := by
  rw [cast_qNormalizedProjector]
  exact normalizedProjector_posSemidef _

theorem qNormalizedProjector_trace_eq_one (v : ι → QComplex) (hv : v ≠ 0) :
    (castQMatrix (qNormalizedProjector v)).trace = 1 := by
  rw [cast_qNormalizedProjector]
  exact normalizedProjector_trace_eq_one _ (castQVector_ne_zero hv)

/-- A total executable atom routine, using a supplied nonzero fallback
direction only when the candidate direction is zero. -/
def qSafeNormalizedProjector (v v0 : ι → QComplex) : Matrix ι ι QComplex :=
  if v = 0 then qNormalizedProjector v0 else qNormalizedProjector v

theorem qSafeNormalizedProjector_feasible
    (v v0 : ι → QComplex) (hv0 : v0 ≠ 0) :
    (castQMatrix (qSafeNormalizedProjector v v0)).PosSemidef ∧
      (castQMatrix (qSafeNormalizedProjector v v0)).trace = 1 := by
  by_cases hv : v = 0
  · simp only [qSafeNormalizedProjector, if_pos hv]
    exact ⟨qNormalizedProjector_posSemidef _, qNormalizedProjector_trace_eq_one _ hv0⟩
  · simp only [qSafeNormalizedProjector, if_neg hv]
    exact ⟨qNormalizedProjector_posSemidef _, qNormalizedProjector_trace_eq_one _ hv⟩

/-- Executable rational conditional-gradient projection. All coefficients
are rational; the local linear oracle receives the actual rational matrix
gradient `X - Y` of the squared-distance objective. -/
def qApproximateProjection
    (linearOracle : Matrix ι ι QComplex → Matrix ι ι QComplex)
    (X0 Y : Matrix ι ι QComplex) (N : ℕ) : Matrix ι ι QComplex :=
  fwRationalIterate (fun X => linearOracle (X - Y)) X0 N

/-- Every matrix produced by the executable rational recursion remains
positive semidefinite with trace exactly one. -/
theorem qApproximateProjection_feasible
    (linearOracle : Matrix ι ι QComplex → Matrix ι ι QComplex)
    (X0 Y : Matrix ι ι QComplex)
    (h0 : (castQMatrix X0).PosSemidef ∧ (castQMatrix X0).trace = 1)
    (horacle : ∀ A, (castQMatrix (linearOracle A)).PosSemidef ∧
      (castQMatrix (linearOracle A)).trace = 1) (N : ℕ) :
    (castQMatrix (qApproximateProjection linearOracle X0 Y N)).PosSemidef ∧
      (castQMatrix (qApproximateProjection linearOracle X0 Y N)).trace = 1 := by
  induction N with
  | zero => exact h0
  | succ N ih =>
      change (castQMatrix
        ((1 - fwWeight N) • qApproximateProjection linearOracle X0 Y N +
          fwWeight N • linearOracle (qApproximateProjection linearOracle X0 Y N - Y))).PosSemidef ∧ _
      rw [castQMatrix_add, castQMatrix_rat_smul, castQMatrix_rat_smul]
      have hv := horacle (qApproximateProjection linearOracle X0 Y N - Y)
      have ha : (0 : ℝ) ≤ (1 - fwWeight N : ℚ) := by
        push_cast
        exact sub_nonneg.mpr (fwWeight_le_one N)
      have hb := fwWeight_nonneg N
      constructor
      · exact (ih.1.smul ha).add (hv.1.smul hb)
      · change (castQMatrix
          ((1 - fwWeight N) • qApproximateProjection linearOracle X0 Y N +
            fwWeight N • linearOracle (qApproximateProjection linearOracle X0 Y N - Y))).trace = 1
        rw [castQMatrix_add, castQMatrix_rat_smul, castQMatrix_rat_smul,
          Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, ih.2, hv.2]
        rw [← add_smul]
        norm_cast
        norm_num

end TomographyOracleCore.Revision.FinitePrecision
