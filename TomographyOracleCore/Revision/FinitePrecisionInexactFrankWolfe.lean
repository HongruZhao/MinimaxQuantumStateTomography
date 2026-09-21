import TomographyOracleCore.Revision.FinitePrecisionFrankWolfe
import TomographyOracleCore.Revision.FinitePrecisionPotential

/-! Error accumulation for the inner conditional-gradient projection when
every iterate is rounded and repaired to bounded word length. -/

namespace TomographyOracleCore.Revision.FinitePrecision

open scoped InnerProductSpace

/-- Scalar convergence from the local quadratic conditional-gradient
recurrence. No initialization bound is needed because the first step has
weight one. -/
theorem fw_scalar_gap_le
    (gap : ℕ → ℝ) (delta D2 : ℝ) (hD2 : 0 ≤ D2)
    (hstep : ∀ j,
      gap (j + 1) ≤ (1 - (fwWeight j : ℝ)) * gap j +
        2 * (fwWeight j : ℝ) * delta + (fwWeight j : ℝ) ^ 2 * D2)
    (n : ℕ) :
    gap (n + 1) ≤ 4 * D2 / ((n : ℝ) + 3) + 2 * delta := by
  induction n with
  | zero =>
      have hs := hstep 0
      norm_num [fwWeight] at hs ⊢
      linarith
  | succ n ih =>
      have hs := hstep (n + 1)
      have hnonneg : 0 ≤ 1 - (fwWeight (n + 1) : ℝ) :=
        sub_nonneg.mpr (fwWeight_le_one (n + 1))
      have hscaled := mul_le_mul_of_nonneg_left ih hnonneg
      have hscalar :
          (1 - (fwWeight (n + 1) : ℝ)) *
              (4 * D2 / ((n : ℝ) + 3) + 2 * delta) +
            2 * (fwWeight (n + 1) : ℝ) * delta +
            (fwWeight (n + 1) : ℝ) ^ 2 * D2 ≤
          4 * D2 / (((n + 1 : ℕ) : ℝ) + 3) + 2 * delta := by
        rw [fwWeight_cast]
        push_cast
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        field_simp
        nlinarith
      linarith

/-- Bounded-length version of the scalar result, requiring local
certificates only on the iterations actually executed. -/
theorem fw_scalar_gap_le_until
    (gap : ℕ → ℝ) (delta D2 : ℝ) (hD2 : 0 ≤ D2) (n : ℕ)
    (hstep : ∀ j < n + 1,
      gap (j + 1) ≤ (1 - (fwWeight j : ℝ)) * gap j +
        2 * (fwWeight j : ℝ) * delta + (fwWeight j : ℝ) ^ 2 * D2) :
    gap (n + 1) ≤ 4 * D2 / ((n : ℝ) + 3) + 2 * delta := by
  induction n with
  | zero =>
      have hs := hstep 0 (by omega)
      norm_num [fwWeight] at hs ⊢
      linarith
  | succ n ih =>
      have hp := ih (fun j hj => hstep j (by omega))
      have hs := hstep (n + 1) (by omega)
      have hnonneg : 0 ≤ 1 - (fwWeight (n + 1) : ℝ) :=
        sub_nonneg.mpr (fwWeight_le_one (n + 1))
      have hscaled := mul_le_mul_of_nonneg_left hp hnonneg
      have hscalar :
          (1 - (fwWeight (n + 1) : ℝ)) *
              (4 * D2 / ((n : ℝ) + 3) + 2 * delta) +
            2 * (fwWeight (n + 1) : ℝ) * delta +
            (fwWeight (n + 1) : ℝ) ^ 2 * D2 ≤
          4 * D2 / (((n + 1 : ℕ) : ℝ) + 3) + 2 * delta := by
        rw [fwWeight_cast]
        push_cast
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        field_simp
        nlinarith
      linarith

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A locally rounded conditional-gradient step obeys the same recurrence
with curvature increased by one whenever the rounding error is charged
to the square of the step size. -/
theorem rounded_fw_quadratic_step
    (x v z y q : E) {a delta D2 S epsilon : ℝ}
    (ha : 0 ≤ a) (hS : 0 ≤ S) (hepsilon : 0 ≤ epsilon)
    (hepsilon_le : epsilon ≤ 1)
    (hlinear : ⟪x - y, v - z⟫_ℝ ≤ delta)
    (hdiam : ‖v - x‖ ^ 2 ≤ D2)
    (hradius : ‖(1 - a) • x + a • v - y‖ ≤ S)
    (hrounding : ‖q - ((1 - a) • x + a • v)‖ ≤ epsilon)
    (hcharge : (2 * S + 1) * epsilon ≤ a ^ 2) :
    ‖q - y‖ ^ 2 - ‖z - y‖ ^ 2 ≤
      (1 - a) * (‖x - y‖ ^ 2 - ‖z - y‖ ^ 2) +
        2 * a * delta + a ^ 2 * (D2 + 1) := by
  have hstep := fw_quadratic_step x v z y ha hlinear hdiam
  have hperturb := nearby_projection_potential
    ((1 - a) • x + a • v) q y hS hepsilon hradius hrounding
  have hsq : epsilon ^ 2 ≤ epsilon := by nlinarith
  nlinarith

end Hilbert

/-- A fixed precision works for all steps of a requested finite run.
Only the square of the run length enters the rounding budget. -/
theorem fw_rounding_charge_of_run_budget
    {S epsilon : ℝ} (hS : 0 ≤ S) (hepsilon : 0 ≤ epsilon)
    (N j : ℕ) (hj : j < N)
    (hbudget : ((2 * S + 1) * epsilon) * ((N : ℝ) + 1) ^ 2 ≤ 4) :
    (2 * S + 1) * epsilon ≤ (fwWeight j : ℝ) ^ 2 := by
  rw [fwWeight_cast]
  have hjreal : (j : ℝ) + 2 ≤ (N : ℝ) + 1 := by exact_mod_cast (show j + 2 ≤ N + 1 by omega)
  have hsmall : 0 < (j : ℝ) + 2 := by positivity
  have hlarge : 0 ≤ (N : ℝ) + 1 := by positivity
  have hsq := pow_le_pow_left₀ hsmall.le hjreal 2
  have hmul := mul_le_mul_of_nonneg_left hsq
    (mul_nonneg (by positivity : 0 ≤ 2 * S + 1) hepsilon)
  rw [div_pow]
  apply (le_div_iff₀ (pow_pos hsmall 2)).2
  nlinarith

end TomographyOracleCore.Revision.FinitePrecision
