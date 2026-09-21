import TomographyOracleCore.PaperMatch.Model.OperatorDesign

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM Revision.NonadaptiveFano
open scoped ENNReal
noncomputable section

/-- Worst-case expected full trace loss for an arbitrary observation space. -/
def worstCaseRisk {D T : ℕ} {Seed Outcome : Type*}
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (C : Set (DensityOperator (Fin D))) (design : OperatorDesign D T Seed Outcome)
    (estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin D)))
    [IsMarkovKernel estimator] : ENNReal :=
  ⨆ rho : C, expectedTraceLoss design.experimentKernel estimator rho.1

/-- A procedure bundles the arbitrary standard Borel public-seed and outcome
spaces. Thus the minimax infimum does not fix these spaces to real codes. -/
structure Procedure (D T : ℕ) where
  Seed : Type
  Outcome : Type
  [seedMeasurable : MeasurableSpace Seed]
  [seedBorel : StandardBorelSpace Seed]
  [outcomeMeasurable : MeasurableSpace Outcome]
  [outcomeBorel : StandardBorelSpace Outcome]
  design : OperatorDesign D T Seed Outcome
  estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin D))
  [estimator_markov : IsMarkovKernel estimator]

attribute [instance] Procedure.seedMeasurable Procedure.seedBorel
  Procedure.outcomeMeasurable Procedure.outcomeBorel Procedure.estimator_markov

/-- The paper's minimax expected risk over arbitrary nonadaptive one-copy
operator-valued POVMs and randomized reconstruction kernels. -/
def minimaxRisk {D T : ℕ} (C : Set (DensityOperator (Fin D))) : ENNReal :=
  ⨅ p : Procedure D T, worstCaseRisk C p.design p.estimator

end
end TomographyOracleCore.PaperMatch.ExactMain
