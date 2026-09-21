import TomographyOracleCore.WithDensityPearson
import TomographyOracleCore.PhysicalReferenceDensity
import TomographyOracleCore.HardReferenceLikelihood

namespace TomographyOracleCore

open MeasureTheory
open MatrixReduction
open scoped ENNReal

noncomputable section

namespace PhysicalPOVM.DominatedPOVM

variable {k m : ℕ} {Outcome : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-!
# Exact Pearson formula for a hard state and its common reference

This module specializes the common-base-measure Pearson identity to the
physical Born laws, then uses the exact centered-projector likelihood
identity to expose the scalar integrand used by the lower-information proof.
-/

/-- Direct specialization of `pearsonChiSquare_withDensity_eq_integral` to a
projector hard state and the common hard reference state. -/
theorem pearsonChiSquare_hardProjector_hardReference_eq_bornDensity_integral
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    pearsonChiSquare
        (M.bornMeasure (hardProjectorDensityOperator P b hm hb.le hbquarter))
        (M.bornMeasure
          (hardReferenceDensityOperator k b hk hb.le hbquarter)) =
      ∫ z,
        ((bornDensityFrom M.effect
              (hardProjectorDensityOperator P b hm hb.le hbquarter) z).toReal -
            (bornDensityFrom M.effect
              (hardReferenceDensityOperator k b hk hb.le hbquarter) z).toReal) ^ 2 /
          (bornDensityFrom M.effect
            (hardReferenceDensityOperator k b hk hb.le hbquarter) z).toReal
        ∂M.base := by
  letI : IsFiniteMeasure M.base := M.base_finite
  change pearsonChiSquare
      (M.base.withDensity
        (bornDensityFrom M.effect
          (hardProjectorDensityOperator P b hm hb.le hbquarter)))
      (M.base.withDensity
        (bornDensityFrom M.effect
          (hardReferenceDensityOperator k b hk hb.le hbquarter))) = _
  exact pearsonChiSquare_withDensity_eq_integral M.base _ _
    (measurable_bornDensityFrom M _).aemeasurable
    (measurable_bornDensityFrom M _).aemeasurable
    (bornDensityFrom_ae_ne_top M _)
    (hardReferenceBornDensity_ae_ne_zero M hk hb hbquarter)
    (bornDensityFrom_ae_ne_top M _)

/-- Exact physical Pearson integral for one hard projector state relative to
the common full-rank reference. -/
theorem pearsonChiSquare_hardProjector_hardReference_eq_integral
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    pearsonChiSquare
        (M.bornMeasure (hardProjectorDensityOperator P b hm hb.le hbquarter))
        (M.bornMeasure
          (hardReferenceDensityOperator k b hk hb.le hbquarter)) =
      ∫ z,
        (b * (embeddedCenteredProjectorTail P * M.effect z).trace.re) ^ 2 /
          (hardReferenceMatrix k b * M.effect z).trace.re
        ∂M.base := by
  rw [pearsonChiSquare_hardProjector_hardReference_eq_bornDensity_integral
    M P b hm hk hb hbquarter]
  apply integral_congr_ae
  filter_upwards [
      M.born_density_ae_nonnegative
        (hardProjectorDensityOperator P b hm hb.le hbquarter),
      M.born_density_ae_nonnegative
        (hardReferenceDensityOperator k b hk hb.le hbquarter)] with z hp hq
  unfold bornDensityFrom
  rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
  change
    ((hardProjectorMatrix P b * M.effect z).trace.re -
        (hardReferenceMatrix k b * M.effect z).trace.re) ^ 2 /
      (hardReferenceMatrix k b * M.effect z).trace.re = _
  rw [bornTrace_hardProjector_sub_hardReference P b (M.effect z)]

end PhysicalPOVM.DominatedPOVM

end

end TomographyOracleCore
