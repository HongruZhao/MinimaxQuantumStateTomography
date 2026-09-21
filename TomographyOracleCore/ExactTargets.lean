import TomographyOracleCore.DecayUpper
import TomographyOracleCore.OrderedSpectral

namespace TomographyOracleCore

open MatrixReduction

/-!
# Exact spectral-decay and minimax targets

This file records the semantic targets of the manuscript without asserting
any physical measurement, packing, information-theoretic, or circuit input.
In particular, the state class is a set of actual density operators, and the
two minimax risks below are the infima defined in `Structural`.
-/

/-- The manuscript's polynomial spectral-tail class on `D`-dimensional
density operators.  Only truncation indices in the physical range
`1 ≤ s ≤ D` are constrained. -/
noncomputable def spectralDecayClass
    (D : ℕ) (alpha L : ℝ) : Set (DensityOperator (Fin D)) :=
  {rho | ∀ s : ℕ, 1 ≤ s → s ≤ D →
    orderedSpectralTail rho s ≤ L * (s : ℝ) ^ (1 - alpha)}

theorem mem_spectralDecayClass_iff
    (D : ℕ) (alpha L : ℝ) (rho : DensityOperator (Fin D)) :
    rho ∈ spectralDecayClass D alpha L ↔
      ∀ s : ℕ, 1 ≤ s → s ≤ D →
        orderedSpectralTail rho s ≤ L * (s : ℝ) ^ (1 - alpha) := by
  rfl

/-- Exact three-regime rate appearing in the expected-risk minimax theorem. -/
noncomputable def spectralDecayMinimaxRate
    (D : ℕ) (T L alpha : ℝ) : ℝ :=
  samplingDecayRate D T L alpha

theorem spectralDecayMinimaxRate_eq
    (D : ℕ) (T L alpha : ℝ) :
    spectralDecayMinimaxRate D T L alpha =
      min 1 (min
        (L ^ alpha⁻¹ *
          ((D : ℝ) / T) ^ ((alpha - 1) / (2 * alpha)))
        (Real.sqrt ((D : ℝ) ^ 3 / T))) := by
  rfl

/-- One fixed design and one estimator adapt simultaneously to every
admissible pair `(alpha, L)`.  The quantifier order is intentional: the
estimator is selected before `alpha` and `L`. -/
noncomputable def FixedDesignSimultaneousAdaptation
    {Design Estimator : Type*}
    (D : ℕ)
    (pointRisk : Design → Estimator → DensityOperator (Fin D) → ℝ)
    (design : Design) (T : ℝ)
    (upperConstant : ℝ → ℝ) : Prop :=
  ∃ estimator : Estimator, ∀ alpha L : ℝ,
    1 < alpha → 1 ≤ L →
      classRisk (spectralDecayClass D alpha L) pointRisk design estimator ≤
        upperConstant alpha * spectralDecayMinimaxRate D T L alpha

/-- Pointwise control on a nonempty state class controls the actual class
supremum for the selected design and estimator. -/
theorem classRisk_le_of_pointwise_target
    {Design Estimator State : Type*}
    (states : Set State) (hstates : states.Nonempty)
    (pointRisk : Design → Estimator → State → ℝ)
    (design : Design) (estimator : Estimator) (bound : ℝ)
    (hpointwise : ∀ state ∈ states,
      pointRisk design estimator state ≤ bound) :
    classRisk states pointRisk design estimator ≤ bound := by
  unfold classRisk
  apply csSup_le (hstates.image (pointRisk design estimator))
  rintro _ ⟨state, hstate, rfl⟩
  exact hpointwise state hstate

/-- Assemble simultaneous adaptation for a selected estimator from
pointwise bounds on every spectral-decay class. -/
theorem fixedDesignSimultaneousAdaptation_of_pointwise
    {Design Estimator : Type*}
    (D : ℕ)
    (pointRisk : Design → Estimator → DensityOperator (Fin D) → ℝ)
    (design : Design) (estimator : Estimator) (T : ℝ)
    (upperConstant : ℝ → ℝ)
    (hstates : ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      (spectralDecayClass D alpha L).Nonempty)
    (hpointwise : ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      ∀ rho ∈ spectralDecayClass D alpha L,
        pointRisk design estimator rho ≤
          upperConstant alpha * spectralDecayMinimaxRate D T L alpha) :
    FixedDesignSimultaneousAdaptation D pointRisk design T upperConstant := by
  refine ⟨estimator, ?_⟩
  intro alpha L halpha hL
  apply classRisk_le_of_pointwise_target
    (spectralDecayClass D alpha L) (hstates alpha L halpha hL)
    pointRisk design estimator
  exact hpointwise alpha L halpha hL

/-- A minimax sandwich stated with the actual unrestricted and fixed-design
infima, rather than proposition-valued target wrappers. -/
noncomputable def ActualMinimaxSandwich
    {Design Estimator : Type*}
    (risk : Design → Estimator → ℝ) (design : Design)
    (rate lowerConstant upperConstant : ℝ) : Prop :=
  (lowerConstant * rate ≤ unrestrictedRisk risk ∧
    unrestrictedRisk risk ≤ upperConstant * rate) ∧
  (lowerConstant * rate ≤ fixedDesignRisk risk design ∧
    fixedDesignRisk risk design ≤ upperConstant * rate)

theorem actualMinimaxSandwich_of_bounds
    {Design Estimator : Type*} [Nonempty Estimator]
    (risk : Design → Estimator → ℝ)
    (hrisk : ∀ design estimator, 0 ≤ risk design estimator)
    (design : Design) (rate lowerConstant upperConstant : ℝ)
    (hlower : lowerConstant * rate ≤ unrestrictedRisk risk)
    (hupper : fixedDesignRisk risk design ≤ upperConstant * rate) :
    ActualMinimaxSandwich risk design rate lowerConstant upperConstant := by
  exact two_experiment_minimax_of_infima risk hrisk design rate
    lowerConstant upperConstant hlower hupper

/-- The complete spectral-decay minimax target, uniformly over admissible
`alpha` and `L`, using the actual density class and semantic risks. -/
noncomputable def SpectralDecayMinimaxSandwich
    {Design Estimator : Type*}
    (D : ℕ)
    (pointRisk : Design → Estimator → DensityOperator (Fin D) → ℝ)
    (design : Design) (T : ℝ)
    (lowerConstant upperConstant : ℝ → ℝ) : Prop :=
  ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
    ActualMinimaxSandwich
      (classRisk (spectralDecayClass D alpha L) pointRisk) design
      (spectralDecayMinimaxRate D T L alpha)
      (lowerConstant alpha) (upperConstant alpha)

/-- Combine a genuine unrestricted lower bound with one simultaneous
selected-estimator upper bound.  Experiment inclusion and the passage from
the selected estimator to the fixed-design infimum are proved internally. -/
theorem spectralDecayMinimaxSandwich_of_simultaneousAdaptation
    {Design Estimator : Type*}
    (D : ℕ)
    (pointRisk : Design → Estimator → DensityOperator (Fin D) → ℝ)
    (design : Design) (T : ℝ)
    (lowerConstant upperConstant : ℝ → ℝ)
    (hstates : ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      (spectralDecayClass D alpha L).Nonempty)
    (hpoint_nonnegative : ∀ design estimator rho,
      0 ≤ pointRisk design estimator rho)
    (hbdd : ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      ∀ design estimator,
        BddAbove
          (pointRisk design estimator '' spectralDecayClass D alpha L))
    (hadapt : FixedDesignSimultaneousAdaptation
      D pointRisk design T upperConstant)
    (hlower : ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
      lowerConstant alpha * spectralDecayMinimaxRate D T L alpha ≤
        unrestrictedRisk
          (classRisk (spectralDecayClass D alpha L) pointRisk)) :
    SpectralDecayMinimaxSandwich D pointRisk design T
      lowerConstant upperConstant := by
  rcases hadapt with ⟨estimator, hadapt⟩
  letI : Nonempty Estimator := ⟨estimator⟩
  intro alpha L halpha hL
  let states := spectralDecayClass D alpha L
  let risk := classRisk states pointRisk
  have hrisk : ∀ otherDesign otherEstimator,
      0 ≤ risk otherDesign otherEstimator := by
    intro otherDesign otherEstimator
    exact classRisk_nonnegative states (hstates alpha L halpha hL)
      pointRisk
      (fun d e rho _ ↦ hpoint_nonnegative d e rho)
      (hbdd alpha L halpha hL) otherDesign otherEstimator
  have hupper : fixedDesignRisk risk design ≤
      upperConstant alpha * spectralDecayMinimaxRate D T L alpha := by
    apply (fixedDesignRisk_le_selectedEstimator
      risk hrisk design estimator).trans
    exact hadapt alpha L halpha hL
  exact actualMinimaxSandwich_of_bounds risk hrisk design
    (spectralDecayMinimaxRate D T L alpha)
    (lowerConstant alpha) (upperConstant alpha)
    (by simpa [risk, states] using hlower alpha L halpha hL) hupper

end TomographyOracleCore
