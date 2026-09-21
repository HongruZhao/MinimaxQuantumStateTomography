import TomographyOracleCore.ProjectiveHaarMomentValues
import TomographyOracleCore.DensityCompact

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

noncomputable section

/-!
# Support and first moment of the concrete projective Haar law

These are the measure-validity facts needed to bundle the exact projective
Haar measurement as a physical dominated POVM.  They are derived from the
literal pushforward construction and the already-proved projective
two-moment theorem; no support or normalization premise is introduced.
-/

section Support

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The concrete projective Haar law is supported on positive semidefinite
rank-one projectors. -/
theorem complexProjectiveHaar_ae_posSemidef :
    ∀ᵐ B ∂complexProjectiveHaarLaw ι, B.PosSemidef := by
  unfold complexProjectiveHaarLaw
  rw [ae_map_iff
    (measurable_complexSphereProjector (ι := ι)).aemeasurable
    (DensityCompact.isClosed_posSemidefSet (ι := ι)).measurableSet]
  exact Filter.Eventually.of_forall complexSphereProjector_posSemidef

/-- Every projector in the pushforward support has trace one. -/
theorem complexProjectiveHaar_ae_trace_eq_one :
    ∀ᵐ B ∂complexProjectiveHaarLaw ι, B.trace = 1 := by
  have hmeas : MeasurableSet
      {B : Matrix ι ι ℂ | B.trace = 1} :=
    (isClosed_eq continuous_id.matrix_trace continuous_const).measurableSet
  unfold complexProjectiveHaarLaw
  rw [ae_map_iff
    (measurable_complexSphereProjector (ι := ι)).aemeasurable hmeas]
  exact Filter.Eventually.of_forall complexSphereProjector_trace_eq_one

/-- A single matrix coordinate is integrable under projective Haar. -/
theorem integrable_complexProjectiveHaar_coordinate (i j : ι) :
    Integrable (fun B : Matrix ι ι ℂ ↦ B i j)
      (complexProjectiveHaarLaw ι) := by
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure
    (measurable_complexMatrix_apply ι i j).aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  have hc := continuous_complexSphereProjector_apply ι i j
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

end Support

section FirstMoment

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- The exact first coordinate moment of a normalized complex rank-one
projector. -/
theorem integral_complexProjectiveHaar_coordinate
    (i j : ι) :
    (∫ B, B i j ∂complexProjectiveHaarLaw ι) =
      if i = j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
  have hformula :=
    (complexProjectiveCoordinateTwoMomentFormula_iff_integral ι).mp
      (complexProjectiveCoordinateTwoMomentFormula_proved (ι := ι))
  calc
    (∫ B, B i j ∂complexProjectiveHaarLaw ι) =
        ∫ B, B i j * B.trace ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [complexProjectiveHaar_ae_trace_eq_one ι] with B hB
      rw [hB]
      ring
    _ = ∫ B, ∑ k : ι, B i j * B k k
          ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [] with B
      simp only [Matrix.trace, Matrix.diag_apply, Finset.mul_sum]
    _ = ∑ k : ι, ∫ B, B i j * B k k
          ∂complexProjectiveHaarLaw ι := by
      rw [integral_finsetSum]
      intro k hk
      exact integrable_complexProjectiveHaar_coordinateSecondMoment
        ι i j k k
    _ = ∑ k : ι,
          ((((if i = j then 1 else 0) * (if k = k then 1 else 0) +
              (if i = k then 1 else 0) * (if k = j then 1 else 0)) *
            (complexProjectiveTwoMomentDenominator ι)⁻¹)) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hformula i j k k
    _ = if i = j then (Fintype.card ι : ℂ)⁻¹ else 0 := by
      by_cases hij : i = j
      · subst j
        simp only [if_pos, mul_one]
        rw [← Finset.sum_mul]
        simp [eq_comm, complexProjectiveTwoMomentDenominator,
          Finset.sum_add_distrib]
        field_simp
      · simp [hij, complexProjectiveTwoMomentDenominator]

/-- After multiplying by the dimension, the first projective Haar moment is
the identity matrix coordinatewise. -/
theorem card_mul_integral_complexProjectiveHaar_coordinate
    (i j : ι) :
    (Fintype.card ι : ℂ) *
        (∫ B, B i j ∂complexProjectiveHaarLaw ι) =
      if i = j then 1 else 0 := by
  rw [integral_complexProjectiveHaar_coordinate ι i j]
  by_cases hij : i = j
  · simp [hij]
  · simp [hij]

end FirstMoment

end

end TomographyOracleCore
