import TomographyOracleCore.PhysicalRisk
import TomographyOracleCore.LowerConstants

namespace TomographyOracleCore

open scoped ENNReal
open MatrixReduction

namespace PhysicalRisk

/-!
# Exact physical upper and minimax targets

These propositions use the actual Markov-kernel experiment and the genuine
state-supremum/estimator-infimum/design-infimum risks from `PhysicalRisk`.
They contain no physical theorem input and do not assert that a Haar or
Cho--Kim design exists.
-/

/-- The real three-regime rate embedded in `ENNReal`. -/
noncomputable def spectralDecayRateENNReal
    (D T : ℕ) (alpha L : ℝ) : ENNReal :=
  ENNReal.ofReal (spectralDecayMinimaxRate D (T : ℝ) L alpha)

/-- Exact high-probability rank-free oracle target for one fixed physical
design.  The estimator may depend on `(D,T,design,delta)` but not on a rank or
decay parameter. -/
noncomputable def RankFreeOracleTarget
    (D T : ℕ) (design : Design D T) : Prop :=
  ∃ C0 C : ℝ, 0 < C0 ∧ 0 < C ∧
    ∀ delta : ℝ, 0 < delta → delta < 1 / 2 →
      C0 * ((D : ℝ) + Real.log delta⁻¹) ≤ (T : ℝ) →
      ∃ estimator : Estimator D T, ∀ rho : DensityOperator (Fin D),
        ENNReal.ofReal (1 - delta) ≤
          (estimateKernel design estimator rho)
            {estimate | ∀ s : ℕ, 1 ≤ s → s ≤ D →
              hermitianTraceLoss rho estimate ≤
                ENNReal.ofReal
                  (4 * orderedSpectralTail rho s +
                    C * (s : ℝ) *
                      Real.sqrt
                        (((D : ℝ) + Real.log delta⁻¹) / (T : ℝ)))}

/-- A single physical estimator, chosen from `(D,T,design)` before `alpha,L`,
attains the class-specific upper rate simultaneously over all admissible
spectral-decay classes. -/
noncomputable def SimultaneousPhysicalUpper
    (D T : ℕ) (design : Design D T)
    (upperConstant : ℝ → ℝ) : Prop :=
  ∃ estimator : Estimator D T, ∀ alpha L : ℝ,
    1 < alpha → 1 ≤ L →
      classWorstCaseRisk D T alpha L design estimator ≤
        ENNReal.ofReal
          (upperConstant alpha *
            spectralDecayMinimaxRate D (T : ℝ) L alpha)

/-- The exact physical minimax sandwich for one fixed design. -/
noncomputable def PhysicalMinimaxSandwich
    (D T : ℕ) (design : Design D T)
    (lowerConstant upperConstant : ℝ → ℝ) : Prop :=
  ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
    ENNReal.ofReal
        (lowerConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
        unrestrictedRisk D T alpha L ∧
    unrestrictedRisk D T alpha L ≤ fixedDesignRisk D T alpha L design ∧
    fixedDesignRisk D T alpha L design ≤
      ENNReal.ofReal
        (upperConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha)

/-- Assemble the physical minimax target from a genuine unrestricted lower
bound and a single simultaneous physical estimator.  Both risk orderings are
deduced from the actual infima. -/
theorem physicalMinimaxSandwich_of_lower_and_simultaneousUpper
    (D T : ℕ) (design : Design D T)
    (lowerConstant upperConstant : ℝ → ℝ)
    (hlower : ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      ENNReal.ofReal
          (lowerConstant alpha *
            spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
        unrestrictedRisk D T alpha L)
    (hupper : SimultaneousPhysicalUpper D T design upperConstant) :
    PhysicalMinimaxSandwich D T design lowerConstant upperConstant := by
  rcases hupper with ⟨estimator, hestimator⟩
  intro alpha L halpha hL
  have hfixed : fixedDesignRisk D T alpha L design ≤
      ENNReal.ofReal
        (upperConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha) :=
    (fixedDesignRisk_le_estimator design estimator).trans
      (hestimator alpha L halpha hL)
  exact ⟨hlower alpha L halpha hL,
    unrestrictedRisk_le_fixedDesignRisk design, hfixed⟩

/-- The explicit lower constant from the manuscript is a valid choice in the
target statement once the physical lower chain has been proved. -/
noncomputable def ExplicitPhysicalMinimaxTarget
    (D T : ℕ) (design : Design D T)
    (upperConstant : ℝ → ℝ) : Prop :=
  PhysicalMinimaxSandwich D T design explicitDecayLowerConstant upperConstant

end PhysicalRisk

end TomographyOracleCore
