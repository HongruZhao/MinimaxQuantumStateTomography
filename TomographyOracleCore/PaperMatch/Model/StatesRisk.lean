import TomographyOracleCore.PhysicalRisk
import TomographyOracleCore.ChoKimCondition

/-! Exact model definitions for the frozen September 12 manuscript.

The paper numbers eigenvalues from one; Lean's finite eigenvalue index starts
at zero. Thus `j > s` in the paper becomes `s ≤ j.val` below. Risk uses the
actual physical experiment and randomized-estimator kernels, not a supplied
risk bound or an abstract oracle conclusion.
-/
namespace TomographyOracleCore.PaperMatch.Model
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalRisk
open scoped ENNReal ComplexOrder
noncomputable section

/-- Equation (1): positive semidefinite complex matrices of trace one. -/
def stateSpace (d : ℕ) : Set (Matrix (Fin d) (Fin d) ℂ) :=
  {A | A.PosSemidef ∧ A.trace = 1}

theorem eq_state_space (d : ℕ) :
    Set.range (DensityOperator.matrix (ι := Fin d)) = stateSpace d := by
  ext A
  constructor
  · rintro ⟨rho, rfl⟩
    exact ⟨rho.posSemidef, rho.trace_eq_one⟩
  · rintro ⟨hp, ht⟩
    exact ⟨⟨A, hp, ht⟩, rfl⟩

/-- Equation (2), with the one-based/zero-based index translation explicit. -/
theorem eq_spectral_tail {d : ℕ} (rho : DensityOperator (Fin d)) (s : ℕ) :
    orderedSpectralTail rho s =
      ∑ j : Fin (Fintype.card (Fin d)),
        if s < j.val + 1 then rho.isHermitian.eigenvalues₀ j else 0 := by
  simp only [orderedSpectralTail, Nat.lt_add_one_iff]

/-- Equation (3), with exactly the physical truncation range. -/
theorem eq_decay_class (d : ℕ) (alpha L : ℝ) (rho : DensityOperator (Fin d)) :
    rho ∈ spectralDecayClass d alpha L ↔
      ∀ s : ℕ, 1 ≤ s → s ≤ d →
        orderedSpectralTail rho s ≤ L * (s : ℝ) ^ (1 - alpha) := Iff.rfl

/-- Worst-case full trace loss on an arbitrary state class. -/
def worstCaseRiskOn {d T : ℕ} (C : Set (DensityOperator (Fin d)))
    (design : Design d T) (estimator : Estimator d T) : ℝ≥0∞ :=
  ⨆ rho : C, statewiseExpectedTraceRisk design estimator rho.1

/-- Equation (7): optimize the reconstruction kernel for a fixed design. -/
def fixedRiskOn {d T : ℕ} (C : Set (DensityOperator (Fin d)))
    (design : Design d T) : ℝ≥0∞ :=
  ⨅ estimator : Estimator d T, worstCaseRiskOn C design estimator

/-- Equation (8): optimize both the design and the reconstruction kernel. -/
def minimaxRiskOn {d T : ℕ} (C : Set (DensityOperator (Fin d))) : ℝ≥0∞ :=
  ⨅ design : Design d T, fixedRiskOn C design

theorem eq_fixed_ensemble_risk {d T : ℕ}
    (C : Set (DensityOperator (Fin d))) (design : Design d T) :
    fixedRiskOn C design =
      ⨅ estimator : Estimator d T, ⨆ rho : C,
        ∫⁻ estimate, hermitianTraceLoss rho.1 estimate
          ∂(estimateKernel design estimator) rho.1 := rfl

theorem eq_minimax_risk {d T : ℕ} (C : Set (DensityOperator (Fin d))) :
    minimaxRiskOn (T := T) C =
      ⨅ design : Design d T, ⨅ estimator : Estimator d T, ⨆ rho : C,
        statewiseExpectedTraceRisk design estimator rho.1 := rfl

theorem minimaxRiskOn_le_fixedRiskOn {d T : ℕ}
    (C : Set (DensityOperator (Fin d))) (design : Design d T) :
    minimaxRiskOn (T := T) C ≤ fixedRiskOn C design := iInf_le _ design

/-- The arbitrary-class definition specializes to the existing formal risk. -/
theorem fixedRiskOn_spectral_class {d T : ℕ} (alpha L : ℝ) (design : Design d T) :
    fixedRiskOn (spectralDecayClass d alpha L) design =
      PhysicalRisk.fixedDesignRisk d T alpha L design := rfl

theorem minimaxRiskOn_spectral_class {d T : ℕ} (alpha L : ℝ) :
    minimaxRiskOn (T := T) (spectralDecayClass d alpha L) =
      PhysicalRisk.unrestrictedRisk d T alpha L := rfl

end
end TomographyOracleCore.PaperMatch.Model
