import TomographyOracleCore.Revision.PaperTheorems

/-! The literal measurement-weighted quadratic objective and its compact
minimizer. No optimization contract is postulated. -/
namespace TomographyOracleCore.MWPLS
open MatrixReduction Revision.PhysicalMinimax
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
set_option maxHeartbeats 1200000
variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

def pairing (A B : Matrix (Fin D) (Fin D) ℂ) : ℝ := (A * B).trace.re

theorem pairing_add_left (A B C : Matrix (Fin D) (Fin D) ℂ) :
    pairing (A+B) C = pairing A C + pairing B C := by
  simp [pairing, add_mul, Matrix.trace_add]
theorem pairing_add_right (A B C : Matrix (Fin D) (Fin D) ℂ) :
    pairing A (B+C) = pairing A B + pairing A C := by
  simp [pairing, mul_add, Matrix.trace_add]
theorem pairing_sub_left (A B C : Matrix (Fin D) (Fin D) ℂ) :
    pairing (A-B) C = pairing A C - pairing B C := by
  simp [pairing, sub_mul, Matrix.trace_sub]
theorem pairing_sub_right (A B C : Matrix (Fin D) (Fin D) ℂ) :
    pairing A (B-C) = pairing A B - pairing A C := by
  simp [pairing, mul_sub, Matrix.trace_sub]
theorem pairing_smul_left (t : ℝ) (A B : Matrix (Fin D) (Fin D) ℂ) :
    pairing (t • A) B = t * pairing A B := by
  simp [pairing, Matrix.smul_mul, Matrix.trace_smul]
theorem pairing_smul_right (t : ℝ) (A B : Matrix (Fin D) (Fin D) ℂ) :
    pairing A (t • B) = t * pairing A B := by
  simp [pairing, Matrix.mul_smul, Matrix.trace_smul]
theorem pairing_comm (A B : Matrix (Fin D) (Fin D) ℂ) :
    pairing A B = pairing B A := by rw [pairing, pairing, Matrix.trace_mul_comm]

theorem projective_channel_trace_symm (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    (finiteUnitaryProjectiveLinearChannel U A * B).trace =
      (finiteUnitaryProjectiveLinearChannel U B * A).trace := by
  classical
  simp only [finiteUnitaryProjectiveLinearChannel_apply, Matrix.smul_mul,
    Finset.sum_mul, Matrix.trace_sum, Matrix.trace_smul, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  rw [Matrix.trace_mul_comm (finiteUnitaryMeasurementProjector (U e) b) B,
    Matrix.trace_mul_comm (finiteUnitaryMeasurementProjector (U e) b) A]
  ring

theorem calibrated_channel_pairing_symm (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    pairing (finiteUnitaryFullCalibratedLinearChannel U A) B =
      pairing (finiteUnitaryFullCalibratedLinearChannel U B) A := by
  unfold pairing
  apply congrArg Complex.re
  simp only [finiteUnitaryFullCalibratedLinearChannel_apply, sub_mul,
    Matrix.trace_sub, Matrix.smul_mul, Matrix.trace_smul, one_mul, smul_eq_mul]
  rw [projective_channel_trace_symm U A B]
  ring

def quadratic (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q A : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  (1/2 : ℝ) * pairing (finiteUnitaryFullCalibratedLinearChannel U A) A - pairing Q A

def objective (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D)) : ℝ :=
  quadratic U Q sigma.matrix

theorem continuous_objective (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) : Continuous (objective U Q) := by
  have hm : Continuous (DensityOperator.matrix :
      DensityOperator (Fin D) → Matrix (Fin D) (Fin D) ℂ) :=
    (show Isometry (DensityOperator.matrix :
      DensityOperator (Fin D) → Matrix (Fin D) (Fin D) ℂ) from fun _ _ => rfl).continuous
  have hL := (finiteUnitaryFullCalibratedLinearChannel U).continuous_of_finiteDimensional
  exact (continuous_const.mul (Complex.continuous_re.comp
    (((hL.comp hm).mul hm).matrix_trace))).sub
    (Complex.continuous_re.comp ((continuous_const.mul hm).matrix_trace))

theorem exists_minimizer (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) :
    ∃ sigma : DensityOperator (Fin D), ∀ rho : DensityOperator (Fin D),
      objective U Q sigma ≤ objective U Q rho := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  letI : Nonempty (DensityOperator (Fin D)) := DensityGrid.densityOperator_nonempty
  obtain ⟨sigma, _, hsigma⟩ := DensityCompact.isCompact_univ_densityOperator.exists_isMinOn
    Set.univ_nonempty (continuous_objective U Q).continuousOn
  exact ⟨sigma, fun rho => hsigma (Set.mem_univ rho)⟩

/-- Exact MW-PLS, selected independently of rank or spectral parameters. -/
def minimizer (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) : DensityOperator (Fin D) :=
  (exists_minimizer hD U Q).choose

theorem minimizer_le (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    objective U Q (minimizer hD U Q) ≤ objective U Q rho :=
  (exists_minimizer hD U Q).choose_spec rho

theorem quadratic_expand (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q A H : Matrix (Fin D) (Fin D) ℂ) (t : ℝ) :
    quadratic U Q (A + t • H) = quadratic U Q A +
      t * pairing (finiteUnitaryFullCalibratedLinearChannel U A - Q) H +
      t^2/2 * pairing (finiteUnitaryFullCalibratedLinearChannel U H) H := by
  have hsmul : finiteUnitaryFullCalibratedLinearChannel U (t • H) =
      t • finiteUnitaryFullCalibratedLinearChannel U H :=
    (finiteUnitaryFullCalibratedLinearChannel U).restrictScalars ℝ |>.map_smul t H
  simp only [quadratic, map_add, hsmul, pairing_add_left,
    pairing_add_right, pairing_smul_left, pairing_smul_right, pairing_sub_left]
  rw [calibrated_channel_pairing_symm U H A]
  ring

def mixture (sigma rho : DensityOperator (Fin D)) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) : DensityOperator (Fin D) where
  matrix := (1-t) • sigma.matrix + t • rho.matrix
  posSemidef := (sigma.posSemidef.smul (sub_nonneg.mpr ht1)).add (rho.posSemidef.smul ht)
  trace_eq_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      sigma.trace_eq_one, rho.trace_eq_one, ← add_smul]
    simp

theorem mixture_matrix (sigma rho : DensityOperator (Fin D)) (t : ℝ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (mixture sigma rho t ht ht1).matrix = sigma.matrix + t • (rho.matrix-sigma.matrix) := by
  dsimp [mixture]
  module

theorem first_order_scalar (g c : ℝ)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ -t*g + t^2/2*c) : g ≤ 0 := by
  by_contra hbad
  have hg : 0 < g := lt_of_not_ge hbad
  let t := min 1 (g/(|c|+1))
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hb : t*(|c|+1) ≤ g :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hc : t*c ≤ t*|c| := mul_le_mul_of_nonneg_left (le_abs_self _) ht.le
  have htc : t*c ≤ g := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left htc ht.le
  have hpoly := h t ht ht1
  nlinarith [mul_pos ht hg]

/-- The exact compact minimizer satisfies the actual first-order condition. -/
theorem minimizer_first_order (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    pairing (finiteUnitaryFullCalibratedLinearChannel U (minimizer hD U Q).matrix-Q)
      ((minimizer hD U Q).matrix-rho.matrix) ≤ 0 := by
  let sigma := minimizer hD U Q
  let H := rho.matrix-sigma.matrix
  apply first_order_scalar _ (pairing (finiteUnitaryFullCalibratedLinearChannel U H) H)
  intro t ht ht1
  have hh := minimizer_le hD U Q (mixture sigma rho t ht.le ht1)
  change quadratic U Q sigma.matrix ≤ quadratic U Q (mixture sigma rho t ht.le ht1).matrix at hh
  rw [mixture_matrix, quadratic_expand] at hh
  have hsign : pairing (finiteUnitaryFullCalibratedLinearChannel U sigma.matrix-Q) H =
      -pairing (finiteUnitaryFullCalibratedLinearChannel U sigma.matrix-Q)
        (sigma.matrix-rho.matrix) := by
    simp only [H, pairing_sub_right]
    ring
  change quadratic U Q sigma.matrix ≤ quadratic U Q sigma.matrix +
    t * pairing (finiteUnitaryFullCalibratedLinearChannel U sigma.matrix-Q) H +
    t^2/2 * pairing (finiteUnitaryFullCalibratedLinearChannel U H) H at hh
  rw [hsign] at hh
  nlinarith

theorem quadratic_centered_identity (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A X : Matrix (Fin D) (Fin D) ℂ) :
    quadratic U (finiteUnitaryFullCalibratedLinearChannel U A) X =
      quadratic U (finiteUnitaryFullCalibratedLinearChannel U A) A +
      (1/2 : ℝ)*pairing (finiteUnitaryFullCalibratedLinearChannel U (X-A)) (X-A) := by
  have he := quadratic_expand U (finiteUnitaryFullCalibratedLinearChannel U A) A (X-A) 1
  have hid : A+(1 : ℝ) • (X-A) = X := by simp
  rw [hid] at he
  simpa [pairing] using he

/-- The implemented quadratic minimizer is a minimizer of the screenshot's
measurement-weighted squared distance whenever L(A) is the input score. -/
theorem minimizer_weighted_projection (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A : Matrix (Fin D) (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    let sigma := minimizer hD U (finiteUnitaryFullCalibratedLinearChannel U A)
    pairing (finiteUnitaryFullCalibratedLinearChannel U (sigma.matrix-A)) (sigma.matrix-A) ≤
      pairing (finiteUnitaryFullCalibratedLinearChannel U (rho.matrix-A)) (rho.matrix-A) := by
  dsimp only
  have hm := minimizer_le hD U (finiteUnitaryFullCalibratedLinearChannel U A) rho
  dsimp only [objective] at hm
  rw [quadratic_centered_identity U A
    (minimizer hD U (finiteUnitaryFullCalibratedLinearChannel U A)).matrix,
    quadratic_centered_identity U A rho.matrix] at hm
  linarith

end
end TomographyOracleCore.MWPLS
