import TomographyOracleCore.MathlibImports
import TomographyOracleCore.Algebra

namespace TomographyOracleCore

/-!
Named theorem parameters for the non-formalized scientific inputs.

There are deliberately no project-specific `axiom` declarations here.
Universal axioms over arbitrary real scalars would be false and could make the
environment inconsistent.  Instead, the public theorems take values of these
structures as explicit hypotheses.  The structures say exactly what remains to
be supplied by matrix analysis, probability, channel calculations, and the
packing/Fano lower bound.
-/

/-- Inputs needed to convert the matrix/probability argument into the scalar
simultaneous oracle.  `reduction` is the curvature-plus-positivity reduction;
`noise_control` contains the robust scalar concentration and shallow-channel
constant calculation. -/
structure ShallowOracleInputs
    (err noise : ℝ) (tail : ℕ → ℝ) (z : ℕ → ℝ) (D : ℕ) : Prop where
  error_nonnegative : 0 ≤ err
  tail_nonnegative : ∀ s, 1 ≤ s → s ≤ D → 0 ≤ tail s
  z_nonnegative : ∀ s, 1 ≤ s → s ≤ D → 0 ≤ z s
  reduction : ∀ s, 1 ≤ s → s ≤ D →
    err ≤ 2 * tail s + 4 * Real.sqrt (z s) * Real.sqrt err
  noise_control : ∀ s, 1 ≤ s → s ≤ D → 16 * z s ≤ noise * s

/-- Scalar name for the target class-specific lower inequality.  This
predicate does not itself prove the packing/Fano theorem. -/
def DecayClassLowerBound (risk rate lowerConstant : ℝ) : Prop :=
  lowerConstant * rate ≤ risk

/-- Scalar name for the target fixed-design upper inequality.  Establishing
it requires the expected universal oracle plus polynomial-tail optimization,
including integer rounding and endpoint regimes. -/
def ShallowFixedDesignUpper (risk rate upperConstant : ℝ) : Prop :=
  risk ≤ upperConstant * rate

/-- Legacy scalar form of experiment inclusion.  The semantic version is
proved from actual infimum definitions in `Structural.lean`. -/
def DesignRiskInclusion (unrestricted fixedDesign : ℝ) : Prop :=
  unrestricted ≤ fixedDesign

end TomographyOracleCore
