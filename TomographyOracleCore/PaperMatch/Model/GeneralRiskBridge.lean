import TomographyOracleCore.PaperMatch.Model.DominatedPOVMBridge
import TomographyOracleCore.PaperMatch.Model.GeneralRisk
import TomographyOracleCore.PaperMatch.Model.StatesRisk

set_option autoImplicit false

namespace TomographyOracleCore.PhysicalPOVM.RandomizedNonadaptiveDesign
open MeasureTheory ProbabilityTheory MatrixReduction
noncomputable section
variable {D T : ℕ} {Seed Outcome : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

def toOperator (design : RandomizedNonadaptiveDesign D T Seed Outcome) :
    OperatorDesign D T Seed Outcome where
  dimension_pos := design.dimension_pos
  seed := design.seed
  seed_probability := design.seed_probability
  measurement := fun t s => (design.measurement t s).toOperator
  shot_measurable := by
    intro t
    simpa only [DominatedPOVM.toOperator_bornMeasure] using design.shot_measurable t
  outcomes := design.outcomes
  outcomes_markov := design.outcomes_markov
  outcomes_eq_pi := by
    intro p
    simpa only [DominatedPOVM.toOperator_bornMeasure] using design.outcomes_eq_pi p

@[simp] theorem toOperator_experimentKernel (design : RandomizedNonadaptiveDesign D T Seed Outcome) :
    design.toOperator.experimentKernel = design.experimentKernel := rfl
end
end TomographyOracleCore.PhysicalPOVM.RandomizedNonadaptiveDesign

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM Revision.NonadaptiveFano
open scoped ENNReal
noncomputable section

/-- Fixed-experiment risk still optimizes every randomized reconstruction. -/
def fixedRisk {D T : ℕ} {Seed Outcome : Type*}
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (C : Set (DensityOperator (Fin D))) (design : OperatorDesign D T Seed Outcome) : ENNReal :=
  ⨅ estimator : Kernel (Seed × (Fin T → Outcome)) (DensityOperator (Fin D)),
    ⨅ _h : IsMarkovKernel estimator, worstCaseRisk C design estimator

def Procedure.ofDominated {D T : ℕ} (design : PhysicalRisk.Design D T)
    (estimator : PhysicalRisk.Estimator D T) : Procedure D T where
  Seed := ℝ
  Outcome := ℝ
  design := design.toOperator
  estimator := estimator.kernel

theorem worstCaseRisk_ofDominated {D T : ℕ} (C : Set (DensityOperator (Fin D)))
    (design : PhysicalRisk.Design D T) (estimator : PhysicalRisk.Estimator D T) :
    worstCaseRisk C design.toOperator estimator.kernel = Model.worstCaseRiskOn C design estimator := rfl

theorem fixedRisk_ofDominated {D T : ℕ} (C : Set (DensityOperator (Fin D)))
    (design : PhysicalRisk.Design D T) :
    fixedRisk C design.toOperator = Model.fixedRiskOn C design := by
  apply le_antisymm
  · apply le_iInf
    intro estimator
    exact (iInf_le _ estimator.kernel).trans (iInf_le _ estimator.markov)
  · apply le_iInf
    intro estimator
    apply le_iInf
    intro hm
    let est : PhysicalRisk.Estimator D T := ⟨estimator, hm⟩
    exact iInf_le _ est

theorem minimaxRisk_le_fixedRisk {D T : ℕ} (C : Set (DensityOperator (Fin D)))
    (design : PhysicalRisk.Design D T) : minimaxRisk (T := T) C ≤ fixedRisk C design.toOperator := by
  rw [fixedRisk_ofDominated]
  apply le_iInf
  intro estimator
  exact iInf_le _ (Procedure.ofDominated design estimator)

end
end TomographyOracleCore.PaperMatch.ExactMain
