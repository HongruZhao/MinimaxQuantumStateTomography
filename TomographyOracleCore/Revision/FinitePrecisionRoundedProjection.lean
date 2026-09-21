import TomographyOracleCore.Revision.FinitePrecisionOracles
import TomographyOracleCore.Revision.FinitePrecisionRounding
import TomographyOracleCore.Revision.FinitePrecisionInexactFrankWolfe

/-!
# Executable bounded-precision projection onto density matrices

Each round computes the certified rational Rayleigh atom, forms a rational
convex combination, then rounds and repairs it at fixed precision. All
states and intermediate atoms are eagerly materialized into dense arrays.
No eigenvector, PSD projection, feasibility-repair, or convergence oracle
is postulated.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open AlgorithmResources MatrixReduction MatrixSolver Matrix
open scoped ComplexOrder InnerProductSpace BigOperators

set_option maxHeartbeats 1000000

variable {D : ℕ}

/-- The actual unrounded update returns stored arrays, so compiler eta
expansion cannot turn materialization into a coordinate-by-coordinate thunk. -/
def qFWUnroundedDense (hD : 0 < D) (delta : ℚ)
    (X Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ) : DenseMatrix D QComplex :=
  let V := qMinimumDensityOracleDense hD delta (X - Y)
  denseOfMatrix ((1 - fwWeight j) • X + fwWeight j • denseToMatrix V)

/-- Matrix view of the actual stored unrounded update. -/
def qFWUnrounded (hD : 0 < D) (delta : ℚ)
    (X Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ) :
    Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (qFWUnroundedDense hD delta X Y j)

@[simp] theorem qFWUnrounded_eq (hD : 0 < D) (delta : ℚ)
    (X Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ) :
    qFWUnrounded hD delta X Y j =
      (1 - fwWeight j) • X + fwWeight j • qMinimumDensityOracle hD delta (X - Y) := by
  simp [qFWUnrounded, qFWUnroundedDense]

/-- Actual recursive state is an array value. Every preceding state and raw
update is computed once before the next rounding stage reads its entries. -/
def qRoundedProjectionDense (hD : 0 < D) (delta : ℚ) (s : ℕ)
    (X0 Y : Matrix (Fin D) (Fin D) QComplex) : ℕ → DenseMatrix D QComplex
  | 0 => denseOfMatrix X0
  | j + 1 =>
      let previous := qRoundedProjectionDense hD delta s X0 Y j
      let raw := qFWUnroundedDense hD delta (denseToMatrix previous) Y j
      denseOfMatrix (qRoundDensity s (denseToMatrix raw))

/-- External matrix view; correctness theorems use this view of the stored
array-valued algorithm. -/
def qRoundedProjection (hD : 0 < D) (delta : ℚ) (s : ℕ)
    (X0 Y : Matrix (Fin D) (Fin D) QComplex) (N : ℕ) : Matrix (Fin D) (Fin D) QComplex :=
  denseToMatrix (qRoundedProjectionDense hD delta s X0 Y N)

@[simp] theorem qRoundedProjection_zero (hD : 0 < D) (delta : ℚ) (s : ℕ)
    (X0 Y : Matrix (Fin D) (Fin D) QComplex) :
    qRoundedProjection hD delta s X0 Y 0 = X0 := by
  simp [qRoundedProjection, qRoundedProjectionDense]

@[simp] theorem qRoundedProjection_succ (hD : 0 < D) (delta : ℚ) (s : ℕ)
    (X0 Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ) :
    qRoundedProjection hD delta s X0 Y (j + 1) =
      qRoundDensity s (qFWUnrounded hD delta (qRoundedProjection hD delta s X0 Y j) Y j) := by
  simp only [qRoundedProjection, qRoundedProjectionDense, denseToMatrix_ofMatrix, qFWUnrounded]

theorem qFWUnrounded_feasible (hD : 0 < D) (delta : ℚ)
    (X Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ)
    (hX : (castQMatrix X).PosSemidef ∧ (castQMatrix X).trace = 1) :
    (castQMatrix (qFWUnrounded hD delta X Y j)).PosSemidef ∧
      (castQMatrix (qFWUnrounded hD delta X Y j)).trace = 1 := by
  rw [qFWUnrounded_eq, castQMatrix_add, castQMatrix_rat_smul, castQMatrix_rat_smul]
  have hv := qMinimumDensityOracle_feasible hD delta (X - Y)
  have ha : (0 : ℝ) ≤ (1 - fwWeight j : ℚ) := by
    push_cast
    exact sub_nonneg.mpr (fwWeight_le_one j)
  constructor
  · exact (hX.1.smul ha).add (hv.1.smul (fwWeight_nonneg j))
  · rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hX.2, hv.2,
      ← add_smul]
    norm_cast
    norm_num

/-- All computed iterates are exactly feasible, including all repairs.
No Hermitian-input or accuracy hypothesis is needed for this invariant. -/
theorem qRoundedProjection_feasible
    (hD : 0 < D) (delta : ℚ) (s : ℕ) (X0 Y : Matrix (Fin D) (Fin D) QComplex)
    (h0 : (castQMatrix X0).PosSemidef ∧ (castQMatrix X0).trace = 1) (N : ℕ) :
    (castQMatrix (qRoundedProjection hD delta s X0 Y N)).PosSemidef ∧
      (castQMatrix (qRoundedProjection hD delta s X0 Y N)).trace = 1 := by
  induction N with
  | zero => simpa using h0
  | succ N ih =>
      have hf := qFWUnrounded_feasible hD delta (qRoundedProjection hD delta s X0 Y N) Y N ih
      have hr := qRoundDensity_correct hD s _ hf.1 hf.2
      rw [qRoundedProjection_succ]
      exact ⟨hr.1, hr.2.1⟩

noncomputable section

def densityRoundingError (D s : ℕ) : ℝ := (2 * (D : ℝ) + 2) * (qRoundingEta D s : ℝ)

theorem densityRoundingError_nonneg (D s : ℕ) : 0 ≤ densityRoundingError D s := by
  exact mul_nonneg (by positivity) (qRoundingEta_nonneg D s)

theorem qRoundedProjection_local_rounding_error
    (hD : 0 < D) (delta : ℚ) (s : ℕ) (X0 Y : Matrix (Fin D) (Fin D) QComplex)
    (h0 : (castQMatrix X0).PosSemidef ∧ (castQMatrix X0).trace = 1) (j : ℕ) :
    ‖encode (castQMatrix (qRoundedProjection hD delta s X0 Y (j + 1))) -
      encode (castQMatrix (qFWUnrounded hD delta
        (qRoundedProjection hD delta s X0 Y j) Y j))‖ ≤ densityRoundingError D s := by
  have hf := qFWUnrounded_feasible hD delta (qRoundedProjection hD delta s X0 Y j) Y j
    (qRoundedProjection_feasible hD delta s X0 Y h0 j)
  have hr := qRoundDensity_correct hD s _ hf.1 hf.2
  rw [qRoundedProjection_succ, ← encode_sub]
  exact hr.2.2

theorem encode_qFWUnrounded (hD : 0 < D) (delta : ℚ)
    (X Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ) :
    encode (castQMatrix (qFWUnrounded hD delta X Y j)) =
      (1 - (fwWeight j : ℝ)) • encode (castQMatrix X) +
        (fwWeight j : ℝ) • encode (castQMatrix (qMinimumDensityOracle hD delta (X - Y))) := by
  rw [qFWUnrounded_eq, castQMatrix_add, castQMatrix_rat_smul, castQMatrix_rat_smul,
    encode_add, encode_smul, encode_smul]
  norm_cast

theorem qFWUnrounded_radius_le_three
    (hD : 0 < D) (delta : ℚ) (X Y : Matrix (Fin D) (Fin D) QComplex) (j : ℕ)
    (hX : (castQMatrix X).PosSemidef ∧ (castQMatrix X).trace = 1)
    (hYnorm : ‖encode (castQMatrix Y)‖ ≤ 2) :
    ‖encode (castQMatrix (qFWUnrounded hD delta X Y j)) - encode (castQMatrix Y)‖ ≤ 3 := by
  have hf := qFWUnrounded_feasible hD delta X Y j hX
  let rho : DensityOperator (Fin D) := ⟨castQMatrix (qFWUnrounded hD delta X Y j), hf.1, hf.2⟩
  have hs := density_frobenius_norm_sq_le_one rho
  have hn : ‖encode rho.matrix‖ ≤ 1 := by nlinarith [norm_nonneg (encode rho.matrix)]
  have htriangle := norm_sub_le (encode rho.matrix) (encode (castQMatrix Y))
  exact htriangle.trans (by linarith)

/-- Concrete integer choice of the dyadic precision implies the complete
per-run rounding budget and bounds every local error by one. -/
theorem rounded_projection_precision_budget (D s n : ℕ)
    (hprecision : 7 * (D + 1) * D ^ 2 * (n + 2) ^ 2 ≤ 2 ^ s) :
    ((2 * (3 : ℝ) + 1) * densityRoundingError D s) *
        (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 4 ∧
      densityRoundingError D s ≤ 1 := by
  have hp : 0 < (2 : ℝ) ^ s := by positivity
  have hcast : 7 * ((D : ℝ) + 1) * (D : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2 ≤ (2 : ℝ) ^ s := by
    exact_mod_cast hprecision
  have hdiv : (7 * ((D : ℝ) + 1) * (D : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2) /
      (2 : ℝ) ^ s ≤ 1 := (div_le_one₀ hp).2 hcast
  have hid : ((2 * (3 : ℝ) + 1) * densityRoundingError D s) *
      (((n + 1 : ℕ) : ℝ) + 1) ^ 2 =
      4 * ((7 * ((D : ℝ) + 1) * (D : ℝ) ^ 2 * ((n : ℝ) + 2) ^ 2) / (2 : ℝ) ^ s) := by
    unfold densityRoundingError qRoundingEta
    push_cast
    ring
  have hbudget : ((2 * (3 : ℝ) + 1) * densityRoundingError D s) *
      (((n + 1 : ℕ) : ℝ) + 1) ^ 2 ≤ 4 := by rw [hid]; linarith
  refine ⟨hbudget, ?_⟩
  have hsq : 1 ≤ (((n + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    have hn : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hmul := mul_nonneg
    (show 0 ≤ (2 * (3 : ℝ) + 1) * densityRoundingError D s by
      exact mul_nonneg (by norm_num) (densityRoundingError_nonneg D s))
    (sub_nonneg.mpr hsq)
  nlinarith

/-- The actually computed rounded matrix satisfies the conditional-gradient
potential recurrence. All local spectral and feasibility inputs are proved
by the concrete routines, not passed in as algorithm contracts. -/
theorem qRoundedProjection_quadratic_step
    (hD : 0 < D) (delta : ℚ) (hdelta : 0 < delta) (s : ℕ)
    (X0 Y : Matrix (Fin D) (Fin D) QComplex)
    (h0 : (castQMatrix X0).PosSemidef ∧ (castQMatrix X0).trace = 1)
    (hY : (castQMatrix Y).IsHermitian) (hYnorm : ‖encode (castQMatrix Y)‖ ≤ 2)
    (rho : DensityOperator (Fin D)) (j : ℕ)
    (hrle : densityRoundingError D s ≤ 1)
    (hcharge : 7 * densityRoundingError D s ≤ (fwWeight j : ℝ) ^ 2) :
    ‖encode (castQMatrix (qRoundedProjection hD delta s X0 Y (j + 1))) -
        encode (castQMatrix Y)‖ ^ 2 - ‖encode rho.matrix - encode (castQMatrix Y)‖ ^ 2 ≤
      (1 - (fwWeight j : ℝ)) *
        (‖encode (castQMatrix (qRoundedProjection hD delta s X0 Y j)) -
          encode (castQMatrix Y)‖ ^ 2 - ‖encode rho.matrix - encode (castQMatrix Y)‖ ^ 2) +
        2 * (fwWeight j : ℝ) * (delta : ℝ) + (fwWeight j : ℝ) ^ 2 * 3 := by
  let X := qRoundedProjection hD delta s X0 Y j
  let A := X - Y
  let V := qMinimumDensityOracle hD delta A
  have hX := qRoundedProjection_feasible hD delta s X0 Y h0 j
  have hV := qMinimumDensityOracle_feasible hD delta A
  have hA : (castQMatrix A).IsHermitian := by
    dsimp only [A]
    rw [castQMatrix_sub]
    exact hX.1.isHermitian.sub hY
  have hl := qMinimumDensityOracle_correct hD delta hdelta A hA rho
  have hlinear :
      ⟪encode (castQMatrix X) - encode (castQMatrix Y),
        encode (castQMatrix V) - encode rho.matrix⟫_ℝ ≤ (delta : ℝ) := by
    rw [← encode_sub, ← castQMatrix_sub, ← encode_sub,
      real_inner_encode_eq_trace_of_hermitian _ _ hA,
      Matrix.sub_mul, Matrix.trace_sub, Complex.sub_re]
    apply sub_le_iff_le_add.mpr
    simpa only [V, add_comm] using hl
  have hdiam : ‖encode (castQMatrix V) - encode (castQMatrix X)‖ ^ 2 ≤ 2 :=
    density_frobenius_diameter_sq ⟨castQMatrix V, hV.1, hV.2⟩
      ⟨castQMatrix X, hX.1, hX.2⟩
  have hradius := qFWUnrounded_radius_le_three hD delta X Y j hX hYnorm
  rw [encode_qFWUnrounded] at hradius
  have hround := qRoundedProjection_local_rounding_error hD delta s X0 Y h0 j
  rw [encode_qFWUnrounded] at hround
  have h := rounded_fw_quadratic_step
    (encode (castQMatrix X)) (encode (castQMatrix V)) (encode rho.matrix)
    (encode (castQMatrix Y))
    (encode (castQMatrix (qRoundedProjection hD delta s X0 Y (j + 1))))
    (fwWeight_nonneg j) (by norm_num : (0 : ℝ) ≤ 3)
    (densityRoundingError_nonneg D s) hrle hlinear hdiam hradius hround
    (by norm_num at hcharge ⊢; exact hcharge)
  simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using h

/-- Full correctness of the constructed bounded-precision inner projection.
Its hypotheses are input validity and explicit rational/integer accuracy
schedules. No computational or spectral theorem is assumed. -/
theorem qRoundedProjection_error
    (hD : 0 < D) (delta : ℚ) (hdelta : 0 < delta) (s : ℕ)
    (X0 Y : Matrix (Fin D) (Fin D) QComplex)
    (h0 : (castQMatrix X0).PosSemidef ∧ (castQMatrix X0).trace = 1)
    (hY : (castQMatrix Y).IsHermitian) (hYnorm : ‖encode (castQMatrix Y)‖ ≤ 2)
    (rho0 : DensityOperator (Fin D)) (n : ℕ) (epsilon : ℝ) (hepsilon : 0 ≤ epsilon)
    (hdeltaBudget : (delta : ℝ) ≤ epsilon ^ 2 / 4)
    (hiterationBudget : 24 ≤ ((n : ℝ) + 3) * epsilon ^ 2)
    (hprecision : 7 * (D + 1) * D ^ 2 * (n + 2) ^ 2 ≤ 2 ^ s) :
    ‖encode (castQMatrix (qRoundedProjection hD delta s X0 Y (n + 1))) -
      densityProjection rho0 (encode (castQMatrix Y))‖ ≤ epsilon := by
  let p := densityProjection rho0 (encode (castQMatrix Y))
  let rho : DensityOperator (Fin D) :=
    ⟨decode p, (densityProjection_mem rho0 _).1, (densityProjection_mem rho0 _).2⟩
  have hrho : encode rho.matrix = p := encode_decode _
  let gap (j : ℕ) : ℝ :=
    ‖encode (castQMatrix (qRoundedProjection hD delta s X0 Y j)) - encode (castQMatrix Y)‖ ^ 2 -
      ‖p - encode (castQMatrix Y)‖ ^ 2
  have hb := rounded_projection_precision_budget D s n hprecision
  have hstep (j : ℕ) (hj : j < n + 1) :
      gap (j + 1) ≤ (1 - (fwWeight j : ℝ)) * gap j +
        2 * (fwWeight j : ℝ) * (delta : ℝ) + (fwWeight j : ℝ) ^ 2 * 3 := by
    have hcharge := fw_rounding_charge_of_run_budget (by norm_num : (0 : ℝ) ≤ 3)
      (densityRoundingError_nonneg D s) (n + 1) j hj hb.1
    have hs := qRoundedProjection_quadratic_step hD delta hdelta s X0 Y h0 hY hYnorm rho j
      hb.2 (by norm_num at hcharge ⊢; exact hcharge)
    simpa only [hrho] using hs
  have hgap := fw_scalar_gap_le_until gap (delta : ℝ) 3 (by norm_num) n hstep
  have hf := qRoundedProjection_feasible hD delta s X0 Y h0 (n + 1)
  have hv := densityProjection_variational rho0 (encode (castQMatrix Y))
    (encode (castQMatrix (qRoundedProjection hD delta s X0 Y (n + 1)))) hf
  have hdist := projection_distance_sq_le_objective_gap
    (encode (castQMatrix (qRoundedProjection hD delta s X0 Y (n + 1)))) p
    (encode (castQMatrix Y)) hv
  have hden : 0 < (n : ℝ) + 3 := by positivity
  have hfrac : 12 / ((n : ℝ) + 3) ≤ epsilon ^ 2 / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hsq : ‖encode (castQMatrix (qRoundedProjection hD delta s X0 Y (n + 1))) - p‖ ^ 2 ≤
      epsilon ^ 2 := by
    dsimp only [gap] at hgap
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) hepsilon).1 hsq

end

end TomographyOracleCore.Revision.FinitePrecision
