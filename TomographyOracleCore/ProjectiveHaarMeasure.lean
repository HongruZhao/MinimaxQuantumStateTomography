import TomographyOracleCore.ProjectiveHaar

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped ComplexOrder

/-!
# Normalized complex projective Haar measure: compact public facade

This module exposes the unconditional measure construction from
`ProjectiveHaar` under short names.  It contains no moment assumption.
-/

section UnitVectors

variable (ι : Type*) [Fintype ι] [Nonempty ι]

/-- Normalized probability law on complex unit vectors. -/
noncomputable abbrev normalizedComplexUnitVectorLaw :
    Measure (sphere (0 : EuclideanSpace ℂ ι) 1) :=
  complexUnitSphereHaarLaw ι

noncomputable instance normalizedComplexUnitVectorLaw_isProbabilityMeasure :
    IsProbabilityMeasure (normalizedComplexUnitVectorLaw ι) := by
  infer_instance

@[simp] theorem normalizedComplexUnitVectorLaw_apply_univ :
    normalizedComplexUnitVectorLaw ι univ = 1 := by
  exact IsProbabilityMeasure.measure_univ

end UnitVectors

section Projectors

variable (ι : Type*) [Fintype ι] [Nonempty ι]

/-- Measurable map from a unit vector to its rank-one projector. -/
noncomputable abbrev complexRankOneProjectorMap :
    sphere (0 : EuclideanSpace ℂ ι) 1 → Matrix ι ι ℂ :=
  complexSphereProjector

theorem measurable_complexRankOneProjectorMap :
    Measurable (complexRankOneProjectorMap ι) :=
  measurable_complexSphereProjector

/-- Normalized probability law on complex rank-one projectors. -/
noncomputable abbrev normalizedComplexProjectorLaw :
    Measure (Matrix ι ι ℂ) :=
  complexProjectiveHaarLaw ι

noncomputable instance normalizedComplexProjectorLaw_isProbabilityMeasure :
    IsProbabilityMeasure (normalizedComplexProjectorLaw ι) := by
  infer_instance

@[simp] theorem normalizedComplexProjectorLaw_apply_univ :
    normalizedComplexProjectorLaw ι univ = 1 := by
  exact IsProbabilityMeasure.measure_univ

theorem complexRankOneProjectorMap_posSemidef
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexRankOneProjectorMap ι x).PosSemidef :=
  complexSphereProjector_posSemidef x

theorem complexRankOneProjectorMap_trace_eq_one
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexRankOneProjectorMap ι x).trace = 1 :=
  complexSphereProjector_trace_eq_one x

theorem complexRankOneProjectorMap_rank_le_one
    (x : sphere (0 : EuclideanSpace ℂ ι) 1) :
    (complexRankOneProjectorMap ι x).rank ≤ 1 :=
  complexSphereProjector_rank_le_one x

end Projectors

end TomographyOracleCore
