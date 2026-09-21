import TomographyOracleCore.SemanticUpper

namespace TomographyOracleCore

open MeasureTheory
open MatrixReduction

/-!
# Hermitian semantic upper bound

This file replaces the provisional singular-value loss in `SemanticUpper`
by the Hermitian trace norm appropriate for differences of density operators.
It also consumes the proved PSD projection-cone theorem, so the remaining
matrix inputs are only curvature and the energy/forward-error dual bound.
-/

/-- Projection-tail functional appearing in the PSD cone inequality. -/
def densityProjectionTail
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (rho : DensityOperator ι) (P : Matrix ι ι ℂ) : ℝ :=
  ((1 - P) * rho.matrix * (1 - P)).trace.re

/-- Hermitian matrix reduction plus a forward-error bound imply the
simultaneous oracle. -/
theorem densityHermitianOracle_of_matrix_bounds_and_forward_error
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma rho : DensityOperator ι)
    (D : ℕ) (a eta h energy : ℝ) (tail : ℕ → ℝ)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hforward : h ≤ 4 * eta)
    (hcone : ∀ s, 1 ≤ s → s ≤ D →
      hermitianTraceNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) ≤
        2 * tail s + 4 * Real.sqrt s *
          hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
            (sigma.sub_isHermitian rho))
    (hlower :
      a * hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) ^ 2 ≤ energy)
    (hupper :
      energy ≤ hermitianTraceNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) * h) :
    OracleBound
      (hermitianTraceNorm (sigma.matrix - rho.matrix)
        (sigma.sub_isHermitian rho))
      tail (64 * eta / a) D := by
  intro s hs1 hsD
  have hred := density_hermitianTrace_reduction_of_matrix_bounds sigma rho s
    a (tail s) h energy ha hh (hcone s hs1 hsD) hlower hupper
  have hz : 0 ≤ (s : ℝ) * h / a :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg s) hh) ha.le
  have habsorb :
      hermitianTraceNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) ≤
        4 * tail s + 16 * ((s : ℝ) * h / a) :=
    scalar_quadratic_absorption
      (hermitianTraceNorm (sigma.matrix - rho.matrix)
        (sigma.sub_isHermitian rho))
      (tail s) ((s : ℝ) * h / a)
      (hermitianTraceNorm_nonneg _ _) hz hred
  have hnoise := noise_control_of_forward_bound a h eta ha hforward s
  linarith

/-- Hermitian trace loss between density operators is deterministically at
most two. -/
theorem densityHermitianTraceError_le_two
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma rho : DensityOperator ι) :
    hermitianTraceNorm (sigma.matrix - rho.matrix)
      (sigma.sub_isHermitian rho) ≤ 2 := by
  exact density_hermitianTraceNorm_sub_le_two sigma rho

end TomographyOracleCore
