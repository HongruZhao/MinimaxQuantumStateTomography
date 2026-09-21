import TomographyOracleCore.Revision.PeriodicForwardConcentration

/-!
# Periodic physical concentration, derived on 2026-09-05

The declaration retained below has exactly the former axiom's statement:
the paper's Proposition E.1 for its literal independently repeated periodic
Born experiment. It is now a theorem.

The actual Clifford fourth moment, overlapping-layer contraction, Born
sixth moment, relative three-design conditioning, realification, and
physical matrix-law transport are proved in Lean. The general covariance
theorem `PublishedInputs.abdallaZhivotovskiy_fixedNorm_p6` is also proved.
This entire declaration now depends only on Lean's standard foundations.

No optimizer, subgradient, projection, finite-precision routine, complexity
claim, fitting guarantee, or minimax conclusion is axiomatized here.
-/

namespace TomographyOracleCore.Revision.NoncomputationalInputs

open MeasureTheory MatrixReduction
open PhysicalMinimax
open scoped Matrix.Norms.L2Operator

/-- Paper Proposition E.1. Constants are uniform in dimension, block size,
sample size, true state, and spectral-decay parameters. The threshold is
essential: the sharp `sqrt(D/T)` bound is not assumed for tiny samples. -/
theorem periodicBorn_expected_forward_covariance :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T → c * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ) →
        ∀ rho : DensityOperator (Fin (2 ^ n)),
          (∫ sample, periodicForwardError h rho sample
            ∂periodicSampleLaw h T rho) ≤
          A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) :=
  PeriodicForwardConcentration.periodic_expected_forward_covariance

end TomographyOracleCore.Revision.NoncomputationalInputs
