import TomographyOracleCore.PeriodicForwardCovarianceBaiYinReduction

namespace TomographyOracleCore

open scoped BigOperators ComplexConjugate
open InnerProductSpace

noncomputable section

/-!
# Quarter-phase realification for Candidate 2

The covariance theorem used by Candidate 2 is real.  A complex measurement
vector can be made mean zero without changing its rank-one projector by an
independent uniform phase in `{1, i, -1, -i}`.  This file proves the finite
algebra behind that reduction.  It contains no probabilistic concentration
claim.
-/

namespace Candidate2PhaseRandomization

/-- The four complex fourth roots of unity, in cyclic order. -/
def quarterPhase : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

@[simp] theorem quarterPhase_norm (j : Fin 4) : ‖quarterPhase j‖ = 1 := by
  fin_cases j <;> simp [quarterPhase]

theorem sum_quarterPhase : ∑ j : Fin 4, quarterPhase j = 0 := by
  norm_num [quarterPhase, Fin.sum_univ_succ]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

local instance : InnerProductSpace ℝ E :=
  InnerProductSpace.complexToReal

/-- A complex vector rotated by one of the four quarter phases. -/
def phaseVector (j : Fin 4) (x : E) : E := quarterPhase j • x

@[simp] theorem norm_phaseVector (j : Fin 4) (x : E) :
    ‖phaseVector j x‖ = ‖x‖ := by
  rw [phaseVector, norm_smul, quarterPhase_norm, one_mul]

/-- Uniform quarter-phase randomization is exactly centered. -/
theorem sum_phaseVector (x : E) :
    ∑ j : Fin 4, phaseVector j x = 0 := by
  simp [phaseVector, quarterPhase, Fin.sum_univ_succ]

/-- Multiplication of the first argument by `i` exposes the imaginary part
as a real inner product. -/
@[simp] theorem re_inner_I_smul_left (x u : E) :
    (⟪Complex.I • x, u⟫_ℂ).re = (⟪x, u⟫_ℂ).im := by
  rw [inner_smul_left]
  simp [Complex.mul_re]

@[simp] theorem real_inner_I_smul_left (x u : E) :
    ⟪Complex.I • x, u⟫_ℝ = (⟪x, u⟫_ℂ).im := by
  simp [real_inner_eq_re_inner]

/-- The exact second real marginal moment over the four phases. -/
theorem sum_real_inner_phaseVector_sq (x u : E) :
    ∑ j : Fin 4, ⟪phaseVector j x, u⟫_ℝ ^ 2 =
      2 * ‖⟪x, u⟫_ℂ‖ ^ 2 := by
  simp [phaseVector, quarterPhase, Fin.sum_univ_succ,
    real_inner_eq_re_inner, re_inner_I_smul_left,
    Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The exact fourth real marginal moment over the four phases. -/
theorem sum_real_inner_phaseVector_fourth (x u : E) :
    ∑ j : Fin 4, ⟪phaseVector j x, u⟫_ℝ ^ 4 =
      2 * ((⟪x, u⟫_ℂ).re ^ 4 + (⟪x, u⟫_ℂ).im ^ 4) := by
  simp [phaseVector, quarterPhase, Fin.sum_univ_succ,
    real_inner_eq_re_inner, re_inner_I_smul_left]
  ring

/-- The exact sixth real marginal moment over the four phases. -/
theorem sum_real_inner_phaseVector_sixth (x u : E) :
    ∑ j : Fin 4, ⟪phaseVector j x, u⟫_ℝ ^ 6 =
      2 * ((⟪x, u⟫_ℂ).re ^ 6 + (⟪x, u⟫_ℂ).im ^ 6) := by
  simp [phaseVector, quarterPhase, Fin.sum_univ_succ,
    real_inner_eq_re_inner, re_inner_I_smul_left]
  ring

/-- The sixth real marginal moment is bounded by the sixth power of the
complex marginal, with the exact factor produced by the four-point sum. -/
theorem sum_real_inner_phaseVector_sixth_le (x u : E) :
    ∑ j : Fin 4, |⟪phaseVector j x, u⟫_ℝ| ^ 6 ≤
      2 * ‖⟪x, u⟫_ℂ‖ ^ 6 := by
  rw [show (∑ j : Fin 4, |⟪phaseVector j x, u⟫_ℝ| ^ 6) =
      ∑ j : Fin 4, ⟪phaseVector j x, u⟫_ℝ ^ 6 by
    apply Finset.sum_congr rfl
    intro j _
    rw [← abs_pow, abs_of_nonneg (by positivity)]]
  rw [sum_real_inner_phaseVector_sixth]
  have hcross :
      (⟪x, u⟫_ℂ).re ^ 6 + (⟪x, u⟫_ℂ).im ^ 6 ≤
        ((⟪x, u⟫_ℂ).re ^ 2 + (⟪x, u⟫_ℂ).im ^ 2) ^ 3 := by
    nlinarith [sq_nonneg ((⟪x, u⟫_ℂ).re ^ 2 * (⟪x, u⟫_ℂ).im),
      sq_nonneg ((⟪x, u⟫_ℂ).im ^ 2 * (⟪x, u⟫_ℂ).re)]
  calc
    2 * ((⟪x, u⟫_ℂ).re ^ 6 + (⟪x, u⟫_ℂ).im ^ 6) ≤
        2 * (((⟪x, u⟫_ℂ).re ^ 2 + (⟪x, u⟫_ℂ).im ^ 2) ^ 3) :=
      mul_le_mul_of_nonneg_left hcross (by norm_num)
    _ = 2 * ‖⟪x, u⟫_ℂ‖ ^ 6 := by
      have hnorm6 :
          ‖⟪x, u⟫_ℂ‖ ^ 6 =
            ((⟪x, u⟫_ℂ).re ^ 2 + (⟪x, u⟫_ℂ).im ^ 2) ^ 3 := by
        calc
          ‖⟪x, u⟫_ℂ‖ ^ 6 = (‖⟪x, u⟫_ℂ‖ ^ 2) ^ 3 := by ring
          _ = ((⟪x, u⟫_ℂ).re ^ 2 +
              (⟪x, u⟫_ℂ).im ^ 2) ^ 3 := by
            rw [Complex.sq_norm, Complex.normSq_apply]
            ring
      rw [hnorm6]

/-- Quarter-phase averaging of real rank-one maps is one half of the
complex rank-one map, viewed on the underlying real space. -/
theorem average_rankOneCovariance_phaseVector_apply (x u : E) :
    ((4 : ℝ)⁻¹) •
        (∑ j : Fin 4,
          PeriodicForwardCovariance.rankOneCovariance (phaseVector j x)) u =
      ((2 : ℝ)⁻¹) • (⟪x, u⟫_ℂ • x) := by
  simp [PeriodicForwardCovariance.rankOneCovariance_apply,
    phaseVector, quarterPhase, Fin.sum_univ_succ,
    real_inner_eq_re_inner, re_inner_I_smul_left]
  conv_rhs => rw [← Complex.re_add_im ⟪x, u⟫_ℂ]
  module

end Candidate2PhaseRandomization

end

end TomographyOracleCore
