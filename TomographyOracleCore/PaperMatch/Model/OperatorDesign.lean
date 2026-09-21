import TomographyOracleCore.PaperMatch.Model.OperatorPOVM
import TomographyOracleCore.Revision.RiskFromFano

set_option autoImplicit false

namespace TomographyOracleCore.PhysicalPOVM
open MeasureTheory ProbabilityTheory MatrixReduction
noncomputable section

namespace OperatorPOVM
variable {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

def bornMeasure (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D)) : Measure Outcome :=
  M.toDominated.bornMeasure rho

@[simp] theorem bornMeasure_apply (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D))
    (s : Set Outcome) (hs : MeasurableSet s) :
    M.bornMeasure rho s = ENNReal.ofReal (rho.matrix * M.apply s).trace.re :=
  M.toDominated_bornMeasure_apply rho s hs

instance bornMeasure_probability (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D)) :
    IsProbabilityMeasure (M.bornMeasure rho) := M.toDominated.born_probability rho
end OperatorPOVM

/-- A randomized nonadaptive one-copy experiment with genuinely
operator-valued POVMs on arbitrary standard Borel spaces. The last fields
express measurability and conditional independence of the experiment. -/
structure OperatorDesign (D T : ℕ) (Seed Outcome : Type*)
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome] where
  dimension_pos : 0 < D
  seed : Measure Seed
  seed_probability : IsProbabilityMeasure seed
  measurement : Fin T → Seed → OperatorPOVM D Outcome
  shot_measurable : ∀ t : Fin T, Measurable fun p : DensityOperator (Fin D) × Seed =>
    (measurement t p.2).bornMeasure p.1
  outcomes : Kernel (DensityOperator (Fin D) × Seed) (Fin T → Outcome)
  outcomes_markov : IsMarkovKernel outcomes
  outcomes_eq_pi : ∀ p : DensityOperator (Fin D) × Seed,
    outcomes p = Measure.pi fun t : Fin T => (measurement t p.2).bornMeasure p.1

namespace OperatorDesign
variable {D T : ℕ} {Seed Outcome : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

def toDominated (design : OperatorDesign D T Seed Outcome) :
    RandomizedNonadaptiveDesign D T Seed Outcome where
  dimension_pos := design.dimension_pos
  seed := design.seed
  seed_probability := design.seed_probability
  measurement := fun t s => (design.measurement t s).toDominated
  shot_measurable := design.shot_measurable
  outcomes := design.outcomes
  outcomes_markov := design.outcomes_markov
  outcomes_eq_pi := design.outcomes_eq_pi

/-- The original public seed and conditional outcome law, unchanged by the
proved density representation. -/
def experimentKernel (design : OperatorDesign D T Seed Outcome) :
    Kernel (DensityOperator (Fin D)) (Seed × (Fin T → Outcome)) :=
  design.toDominated.experimentKernel

instance experimentKernel_markov (design : OperatorDesign D T Seed Outcome) :
    IsMarkovKernel design.experimentKernel := by unfold experimentKernel; infer_instance

@[simp] theorem toDominated_experimentKernel (design : OperatorDesign D T Seed Outcome) :
    design.toDominated.experimentKernel = design.experimentKernel := rfl
end OperatorDesign
end
end TomographyOracleCore.PhysicalPOVM
