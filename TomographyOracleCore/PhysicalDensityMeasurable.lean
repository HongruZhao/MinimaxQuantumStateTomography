import TomographyOracleCore.PhysicalLossBounds
import TomographyOracleCore.DensityCompact

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped ENNReal

namespace PhysicalPOVM

/-- The coordinate map used to define the measurable structure on density
operators is injective. -/
theorem densityCoordinates_injective (D : ℕ) :
    Function.Injective (densityCoordinates D) := by
  intro ρ σ h
  apply DensityCompact.densityOperator_matrix_injective
  ext i j
  exact congrFun h (i, j)

/-- Single density operators are measurable for the coordinate-generated
measurable structure.  This is useful for finite-valued deterministic
estimators and does not invoke a measurable-selection theorem. -/
noncomputable instance densityOperatorMeasurableSingletonClass (D : ℕ) :
    MeasurableSingletonClass (DensityOperator (Fin D)) where
  measurableSet_singleton ρ := by
    have heq : ({ρ} : Set (DensityOperator (Fin D))) =
        densityCoordinates D ⁻¹' {densityCoordinates D ρ} := by
      ext σ
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact (densityCoordinates_injective D).eq_iff.symm
    rw [heq]
    exact (measurableSet_singleton (densityCoordinates D ρ)).preimage
      (measurable_densityCoordinates D)

end PhysicalPOVM

end TomographyOracleCore
