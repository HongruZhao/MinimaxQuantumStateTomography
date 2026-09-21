import TomographyOracleCore.Revision.FinitePrecisionRationalProjection
import TomographyOracleCore.Revision.MatrixSolverChannel

/-! Exact rational-complex input arithmetic.

These are executable operations on supplied rational projector arrays and
sample matrices. The interpretation theorems connect them to the actual
finite measurement channel. An array containing an entire Clifford ensemble
can be superpolynomial in the matrix dimension: no polynomial bound for
constructing that array is asserted here. The separate Pauli representation
is the intended route for avoiding that enumeration.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision
open scoped BigOperators InnerProductSpace

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

@[simp] theorem castQMatrix_sum {α : Type*} (s : Finset α)
    (A : α → Matrix ι ι QComplex) :
    castQMatrix (∑ a ∈ s, A a) = ∑ a ∈ s, castQMatrix (A a) := by
  ext i j
  simp [castQMatrix, Matrix.map_apply, Matrix.sum_apply, map_sum]

@[simp] theorem castQMatrix_qcomplex_smul (c : QComplex) (A : Matrix ι ι QComplex) :
    castQMatrix (c • A) = qComplexToComplex c • castQMatrix A := by
  ext i j
  exact map_mul qComplexToComplex _ _

@[simp] theorem castQMatrix_one :
    castQMatrix (1 : Matrix ι ι QComplex) = 1 := by
  ext i j
  change qComplexToComplex (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> simp only [map_one, map_zero]

@[simp] theorem qComplexToComplex_trace (A : Matrix ι ι QComplex) :
    qComplexToComplex A.trace = (castQMatrix A).trace := by
  simp [Matrix.trace, Matrix.diag_apply, castQMatrix, map_sum]

def rationalProjectiveChannel {D : ℕ} {E : Type*} [Fintype E]
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  (Fintype.card E : ℚ)⁻¹ • ∑ e, ∑ b, (A * P e b).trace • P e b

def rationalCalibratedChannel {D : ℕ} {E : Type*} [Fintype E]
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  ((D + 1 : ℕ) : ℚ) • rationalProjectiveChannel P A - A.trace • 1

def rationalEmpiricalForward {D T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) QComplex) :
    Matrix (Fin D) (Fin D) QComplex :=
  (((D + 1 : ℕ) : ℚ) / (T : ℚ)) • ∑ t, sample t - 1

theorem cast_rationalProjectiveChannel {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (hP : ∀ e b, castQMatrix (P e b) = finiteUnitaryMeasurementProjector (U e) b)
    (A : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalProjectiveChannel P A) =
      finiteUnitaryProjectiveLinearChannel U (castQMatrix A) := by
  rw [rationalProjectiveChannel, castQMatrix_rat_smul]
  simp only [castQMatrix_sum, castQMatrix_qcomplex_smul, qComplexToComplex_trace,
    castQMatrix_mul, hP, finiteUnitaryProjectiveLinearChannel_apply]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  change (((((Fintype.card E : ℚ)⁻¹ : ℚ) : ℝ) : ℂ)) = (Fintype.card E : ℂ)⁻¹
  simp only [Rat.cast_inv, Rat.cast_natCast, Complex.ofReal_inv, Complex.ofReal_natCast]

theorem cast_rationalCalibratedChannel {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (hP : ∀ e b, castQMatrix (P e b) = finiteUnitaryMeasurementProjector (U e) b)
    (A : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalCalibratedChannel P A) =
      finiteUnitaryFullCalibratedLinearChannel U (castQMatrix A) := by
  rw [rationalCalibratedChannel, castQMatrix_sub, castQMatrix_rat_smul,
    cast_rationalProjectiveChannel U P hP, castQMatrix_qcomplex_smul,
    qComplexToComplex_trace, castQMatrix_one, finiteUnitaryFullCalibratedLinearChannel_apply]
  congr 1

theorem cast_rationalEmpiricalForward {D T : ℕ}
    (sample : Fin T → Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (rationalEmpiricalForward sample) =
      (((D + 1 : ℕ) : ℝ) / (T : ℝ)) • ∑ t, castQMatrix (sample t) - 1 := by
  rw [rationalEmpiricalForward, castQMatrix_sub, castQMatrix_rat_smul,
    castQMatrix_sum, castQMatrix_one]
  simp only [Rat.cast_div, Rat.cast_natCast]

theorem rationalProjectiveChannel_contract {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (hP : ∀ e b, castQMatrix (P e b) = finiteUnitaryMeasurementProjector (U e) b)
    (A : Matrix (Fin D) (Fin D) QComplex) :
    ‖encode (castQMatrix (rationalProjectiveChannel P A))‖ ≤ ‖encode (castQMatrix A)‖ := by
  rw [cast_rationalProjectiveChannel U P hP]
  exact finite_channel_frobenius_contract U _

theorem rationalProjectiveChannel_selfAdjoint {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (P : E → Fin D → Matrix (Fin D) (Fin D) QComplex)
    (hP : ∀ e b, castQMatrix (P e b) = finiteUnitaryMeasurementProjector (U e) b)
    (A B : Matrix (Fin D) (Fin D) QComplex) :
    ⟪encode (castQMatrix (rationalProjectiveChannel P A)), encode (castQMatrix B)⟫_ℝ =
      ⟪encode (castQMatrix A), encode (castQMatrix (rationalProjectiveChannel P B))⟫_ℝ := by
  rw [cast_rationalProjectiveChannel U P hP, cast_rationalProjectiveChannel U P hP]
  exact finite_channel_frobenius_selfAdjoint U _ _

end TomographyOracleCore.Revision.MatrixSolver
