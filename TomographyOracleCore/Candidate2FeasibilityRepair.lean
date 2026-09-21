import TomographyOracleCore.Candidate2FullCalibratedChannel
import TomographyOracleCore.Candidate2ForwardFit

namespace TomographyOracleCore

open scoped ComplexOrder Matrix.Norms.L2Operator
open MatrixReduction
noncomputable section
set_option maxHeartbeats 800000

/-!
# Candidate 2: deterministic feasibility repair

The weak SDP solver may return a Hermitian matrix which is only approximately
positive and approximately trace one.  This file proves the concrete repair
used after that solve.  There are no solver or probability assumptions here.
-/

namespace Candidate2FeasibilityRepair

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Shift an approximately positive Hermitian matrix by `epsilon I`. -/
def shiftedMatrix (H : Matrix ι ι ℂ) (epsilon : ℝ) : Matrix ι ι ℂ :=
  H + epsilon • (1 : Matrix ι ι ℂ)

/-- Real trace of the shifted matrix. -/
def repairDenominator (H : Matrix ι ι ℂ) (epsilon : ℝ) : ℝ :=
  H.trace.re + (Fintype.card ι : ℝ) * epsilon

/-- Normalize the positive shift by its trace. -/
def repairedMatrix (H : Matrix ι ι ℂ) (epsilon : ℝ) : Matrix ι ι ℂ :=
  (repairDenominator H epsilon)⁻¹ • shiftedMatrix H epsilon

/-- A Hermitian matrix has real trace. -/
theorem trace_eq_ofReal_re (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    H.trace = (H.trace.re : ℂ) := by
  apply Eq.symm
  apply Complex.conj_eq_iff_re.mp
  have htrace := congrArg Matrix.trace hH.eq
  simpa only [Matrix.trace_conjTranspose, starRingEnd_apply] using htrace

/-- The shifted trace is exactly the real repair denominator. -/
theorem shiftedMatrix_trace (H : Matrix ι ι ℂ) (epsilon : ℝ)
    (hH : H.IsHermitian) :
    (shiftedMatrix H epsilon).trace =
      (repairDenominator H epsilon : ℂ) := by
  rw [shiftedMatrix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    trace_eq_ofReal_re H hH]
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul]
  simp [repairDenominator, mul_comm]

/-- Approximate Loewner positivity, expressed as
`H + epsilon I` positive semidefinite, survives positive normalization. -/
theorem repairedMatrix_posSemidef (H : Matrix ι ι ℂ) (epsilon : ℝ)
    (hshift : (shiftedMatrix H epsilon).PosSemidef)
    (hden : 0 < repairDenominator H epsilon) :
    (repairedMatrix H epsilon).PosSemidef := by
  unfold repairedMatrix
  exact hshift.smul (inv_nonneg.mpr hden.le)

/-- Positive normalization gives trace one. -/
theorem repairedMatrix_trace_eq_one (H : Matrix ι ι ℂ) (epsilon : ℝ)
    (hH : H.IsHermitian)
    (hden : 0 < repairDenominator H epsilon) :
    (repairedMatrix H epsilon).trace = 1 := by
  rw [repairedMatrix, Matrix.trace_smul, shiftedMatrix_trace H epsilon hH]
  simp [RCLike.real_smul_eq_coe_smul (K := ℂ), hden.ne']

/-- The actual repaired density operator. -/
def repairedDensity (H : Matrix ι ι ℂ) (epsilon : ℝ)
    (hH : H.IsHermitian)
    (hshift : (shiftedMatrix H epsilon).PosSemidef)
    (hden : 0 < repairDenominator H epsilon) : DensityOperator ι where
  matrix := repairedMatrix H epsilon
  posSemidef := repairedMatrix_posSemidef H epsilon hshift hden
  trace_eq_one := repairedMatrix_trace_eq_one H epsilon
    hH hden

@[simp] theorem repairedDensity_matrix (H : Matrix ι ι ℂ) (epsilon : ℝ)
    (hH : H.IsHermitian)
    (hshift : (shiftedMatrix H epsilon).PosSemidef)
    (hden : 0 < repairDenominator H epsilon) :
    (repairedDensity H epsilon hH hshift hden).matrix =
      repairedMatrix H epsilon := by
  rfl

/-! ## Quantitative trace-norm repair -/

/-- Real homogeneity of the Hermitian trace norm on a positive-semidefinite
matrix.  This auxiliary result also covers a negative real scalar by reducing
to `hermitianTraceNorm_neg`. -/
theorem hermitianTraceNorm_real_smul_psd
    (A : Matrix ι ι ℂ) (hA : A.PosSemidef) (c : ℝ) :
    hermitianTraceNorm (c • A)
        (hA.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))) =
      |c| * A.trace.re := by
  by_cases hc : 0 ≤ c
  · have hscaled : (c • A).PosSemidef := hA.smul hc
    calc
      hermitianTraceNorm (c • A)
          (hA.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))) =
          (c • A).trace.re := by
        exact hermitianTraceNorm_psd_eq_re_trace (c • A) hscaled
      _ = c * A.trace.re := by
        rw [Matrix.trace_smul, Complex.smul_re]
        rfl
      _ = |c| * A.trace.re := by rw [abs_of_nonneg hc]
  · have hcneg : c < 0 := lt_of_not_ge hc
    have hscaled : ((-c) • A).PosSemidef :=
      hA.smul (neg_nonneg.mpr hcneg.le)
    have hmatrix : c • A = -((-c) • A) := by
      ext i j
      simp
    calc
      hermitianTraceNorm (c • A)
          (hA.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))) =
        hermitianTraceNorm (-((-c) • A)) hscaled.isHermitian.neg := by
          congr 1
      _ =
          hermitianTraceNorm ((-c) • A) hscaled.isHermitian := by
        exact hermitianTraceNorm_neg ((-c) • A) hscaled.isHermitian
      _ = ((-c) • A).trace.re := by
        exact hermitianTraceNorm_psd_eq_re_trace ((-c) • A) hscaled
      _ = (-c) * A.trace.re := by
        rw [Matrix.trace_smul, Complex.smul_re]
        rfl
      _ = |c| * A.trace.re := by rw [abs_of_neg hcneg]

/-- Algebraic decomposition behind the repair estimate. -/
theorem repairedMatrix_sub_eq (H : Matrix ι ι ℂ) (epsilon : ℝ) :
    repairedMatrix H epsilon - H =
      ((repairDenominator H epsilon)⁻¹ - 1) •
          shiftedMatrix H epsilon +
        epsilon • (1 : Matrix ι ι ℂ) := by
  ext i j
  simp only [repairedMatrix, shiftedMatrix, Matrix.sub_apply,
    Matrix.add_apply, Matrix.smul_apply]
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply]
    ring
  · simp [Matrix.one_apply, hij]
    ring

/-- The scalar normalization error cancels its denominator exactly. -/
theorem abs_inv_sub_one_mul (a : ℝ) (ha : 0 < a) :
    |a⁻¹ - 1| * a = |1 - a| := by
  calc
    |a⁻¹ - 1| * a = |a⁻¹ - 1| * |a| := by rw [abs_of_pos ha]
    _ = |(a⁻¹ - 1) * a| := by rw [abs_mul]
    _ = |1 - a| := by
      congr 1
      field_simp [ha.ne']

/-- If `H` is Hermitian, `H + epsilon I` is PSD, and its trace is within
`epsilon` of one before shifting, normalization changes `H` by at most
`(2 D + 1) epsilon` in Hermitian trace norm. -/
theorem repairedMatrix_sub_traceNorm_le
    (H : Matrix ι ι ℂ) (epsilon : ℝ)
    (hH : H.IsHermitian)
    (hepsilon : 0 ≤ epsilon)
    (hshift : (shiftedMatrix H epsilon).PosSemidef)
    (htrace : |H.trace.re - 1| ≤ epsilon)
    (hden : 0 < repairDenominator H epsilon) :
    hermitianTraceNorm (repairedMatrix H epsilon - H)
        ((repairedMatrix_posSemidef H epsilon hshift hden).isHermitian.sub hH) ≤
      (2 * (Fintype.card ι : ℝ) + 1) * epsilon := by
  let d : ℝ := Fintype.card ι
  let a : ℝ := repairDenominator H epsilon
  let K : Matrix ι ι ℂ := shiftedMatrix H epsilon
  let c : ℝ := a⁻¹ - 1
  have hK : K.PosSemidef := hshift
  have ha : 0 < a := hden
  have hKtrace : K.trace.re = a := by
    have h := congrArg Complex.re (shiftedMatrix_trace H epsilon hH)
    simpa [K, a] using h
  have hI : (1 : Matrix ι ι ℂ).PosSemidef := Matrix.PosSemidef.one
  have heI : (epsilon • (1 : Matrix ι ι ℂ)).PosSemidef :=
    hI.smul hepsilon
  have hcNorm :
      hermitianTraceNorm (c • K)
          (hK.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))) =
        |1 - a| := by
    rw [hermitianTraceNorm_real_smul_psd K hK c, hKtrace]
    exact abs_inv_sub_one_mul a ha
  have heNorm :
      hermitianTraceNorm (epsilon • (1 : Matrix ι ι ℂ))
          heI.isHermitian = d * epsilon := by
    rw [hermitianTraceNorm_psd_eq_re_trace _ heI,
      Matrix.trace_smul, Complex.smul_re, Matrix.trace_one]
    simp [d, mul_comm]
  have habs : |1 - a| ≤ (d + 1) * epsilon := by
    calc
      |1 - a| = |(1 - H.trace.re) + (-(d * epsilon))| := by
        congr 1
        simp [a, repairDenominator, d]
        ring
      _ ≤ |1 - H.trace.re| + |-(d * epsilon)| := abs_add_le _ _
      _ = |H.trace.re - 1| + |d * epsilon| := by
        rw [abs_sub_comm, abs_neg]
      _ = |H.trace.re - 1| + d * epsilon := by
        rw [abs_of_nonneg (mul_nonneg (by positivity) hepsilon)]
      _ ≤ epsilon + d * epsilon := by
        linarith
      _ = (d + 1) * epsilon := by ring
  calc
    hermitianTraceNorm (repairedMatrix H epsilon - H)
        ((repairedMatrix_posSemidef H epsilon hshift hden).isHermitian.sub hH) =
      hermitianTraceNorm (c • K + epsilon • (1 : Matrix ι ι ℂ))
        ((hK.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))).add
          heI.isHermitian) := by
      congr 1
      simpa [c, K, a] using repairedMatrix_sub_eq H epsilon
    _ ≤ hermitianTraceNorm (c • K)
          (hK.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))) +
          hermitianTraceNorm (epsilon • (1 : Matrix ι ι ℂ))
            heI.isHermitian :=
      hermitianTraceNorm_triangle _ _ _ _
    _ = |1 - a| + d * epsilon := by rw [hcNorm, heNorm]
    _ ≤ (d + 1) * epsilon + d * epsilon := by linarith
    _ = (2 * (Fintype.card ι : ℝ) + 1) * epsilon := by
      simp [d]
      ring

/-! ## Forward-objective perturbation -/

/-- Pure linearity and the operator-norm triangle inequality show that the
full-channel objective changes by at most the forward image of the repair
error.  This theorem uses the corrected full channel
`L(A) = (D+1) M(A) - trace(A) I`. -/
theorem finiteUnitaryFullCalibrated_objective_repair_le
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q H : Matrix (Fin D) (Fin D) ℂ) (epsilon : ℝ) :
    matrixOperatorNorm
        (Q - finiteUnitaryFullCalibratedLinearChannel U
          (repairedMatrix H epsilon)) ≤
      matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        matrixOperatorNorm
          (finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H)) := by
  have hdecomp :
      Q - finiteUnitaryFullCalibratedLinearChannel U
          (repairedMatrix H epsilon) =
        (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
          -(finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H)) := by
    rw [map_sub]
    abel
  rw [hdecomp]
  calc
    matrixOperatorNorm
        ((Q - finiteUnitaryFullCalibratedLinearChannel U H) +
          -(finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H))) ≤
      matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        matrixOperatorNorm
          (-(finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H))) :=
      Candidate2ForwardFit.matrixOperatorNorm_add_le _ _
    _ = matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        matrixOperatorNorm
          (finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H)) := by
      rw [matrixOperatorNorm_neg]

/-- Scalar `delta_alg` form of the previous theorem.  The displayed
`hchannel` is a deterministic Lipschitz certificate for the concrete full
channel, not an external statistical or solver axiom. -/
theorem finiteUnitaryFullCalibrated_objective_repair_le_of_traceLipschitz
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q H : Matrix (Fin D) (Fin D) ℂ) (epsilon Lambda : ℝ)
    (hH : H.IsHermitian)
    (hepsilon : 0 ≤ epsilon)
    (hshift : (shiftedMatrix H epsilon).PosSemidef)
    (htrace : |H.trace.re - 1| ≤ epsilon)
    (hden : 0 < repairDenominator H epsilon)
    (hLambda : 0 ≤ Lambda)
    (hchannel :
      matrixOperatorNorm
          (finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H)) ≤
        Lambda * hermitianTraceNorm (repairedMatrix H epsilon - H)
          ((repairedMatrix_posSemidef H epsilon hshift hden).isHermitian.sub hH)) :
    matrixOperatorNorm
        (Q - finiteUnitaryFullCalibratedLinearChannel U
          (repairedMatrix H epsilon)) ≤
      matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        Lambda * (2 * (D : ℝ) + 1) * epsilon := by
  calc
    matrixOperatorNorm
        (Q - finiteUnitaryFullCalibratedLinearChannel U
          (repairedMatrix H epsilon)) ≤
      matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        matrixOperatorNorm
          (finiteUnitaryFullCalibratedLinearChannel U
            (repairedMatrix H epsilon - H)) :=
      finiteUnitaryFullCalibrated_objective_repair_le U Q H epsilon
    _ ≤ matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        Lambda * hermitianTraceNorm (repairedMatrix H epsilon - H)
          ((repairedMatrix_posSemidef H epsilon hshift hden).isHermitian.sub hH) :=
      add_le_add_right hchannel
        (matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H))
    _ ≤ matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        Lambda * ((2 * (D : ℝ) + 1) * epsilon) := by
      apply add_le_add_right
      have hrepair :
          hermitianTraceNorm (repairedMatrix H epsilon - H)
              ((repairedMatrix_posSemidef H epsilon hshift hden).isHermitian.sub hH) ≤
            (2 * (D : ℝ) + 1) * epsilon := by
        simpa using repairedMatrix_sub_traceNorm_le H epsilon hH hepsilon
          hshift htrace hden
      exact mul_le_mul_of_nonneg_left hrepair hLambda
    _ = matrixOperatorNorm
          (Q - finiteUnitaryFullCalibratedLinearChannel U H) +
        Lambda * (2 * (D : ℝ) + 1) * epsilon := by ring

end Candidate2FeasibilityRepair

end
end TomographyOracleCore
