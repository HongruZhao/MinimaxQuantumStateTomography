import TomographyOracleCore.PhysicalPOVM
import TomographyOracleCore.HardReferenceBornLower

namespace TomographyOracleCore

open MeasureTheory
open MatrixReduction
open scoped ENNReal

noncomputable section

namespace PhysicalPOVM.DominatedPOVM

variable {k : ℕ} {b : ℝ} {Outcome : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-!
# Physical reference Born density

This module supplies the measurable, strictly positive, finite reference
density facts required to apply the common-base-measure Pearson formulas to
the hard tomography family.
-/

/-- The Born density of every state is measurable with respect to the
dominating outcome sigma-algebra. -/
theorem measurable_bornDensityFrom
    (M : DominatedPOVM (k + 2) Outcome)
    (ρ : DensityOperator (Fin (k + 2))) :
    Measurable (bornDensityFrom M.effect ρ) := by
  unfold bornDensityFrom
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ (fun i _ ↦
    Finset.measurable_sum Finset.univ (fun j _ ↦
      (M.effect_measurable j i).const_mul (ρ.matrix i j)))

/-- The Born density of every state is finite, pointwise and hence almost
everywhere. -/
theorem bornDensityFrom_ne_top
    (M : DominatedPOVM (k + 2) Outcome)
    (ρ : DensityOperator (Fin (k + 2))) (z : Outcome) :
    bornDensityFrom M.effect ρ z ≠ ∞ := by
  unfold bornDensityFrom
  exact ENNReal.ofReal_ne_top

theorem bornDensityFrom_ae_ne_top
    (M : DominatedPOVM (k + 2) Outcome)
    (ρ : DensityOperator (Fin (k + 2))) :
    ∀ᵐ z ∂M.base, bornDensityFrom M.effect ρ z ≠ ∞ := by
  exact Filter.Eventually.of_forall (bornDensityFrom_ne_top M ρ)

/-- Against a physical dominated POVM, the common hard reference state has
Born density at least its uniform tail eigenvalue almost everywhere. -/
theorem hardReferenceBornDensity_ae_tail_lower
    (M : DominatedPOVM (k + 2) Outcome)
    (hk : 1 ≤ k) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    ∀ᵐ z ∂M.base,
      ENNReal.ofReal (b / (k : ℝ)) ≤
        bornDensityFrom M.effect
          (hardReferenceDensityOperator k b hk hb0 hbquarter) z := by
  filter_upwards [M.effect_ae_posSemidef, M.effect_ae_trace_one] with z hpos htrace
  unfold bornDensityFrom
  apply ENNReal.ofReal_le_ofReal
  exact hardReferenceMatrix_born_re_tail_lower
    k b hk hb0 hbquarter (M.effect z) hpos htrace

/-- If the tail weight is strictly positive, the hard reference Born density
is nonzero almost everywhere. -/
theorem hardReferenceBornDensity_ae_ne_zero
    (M : DominatedPOVM (k + 2) Outcome)
    (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    ∀ᵐ z ∂M.base,
      bornDensityFrom M.effect
        (hardReferenceDensityOperator k b hk hb.le hbquarter) z ≠ 0 := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hbdiv : 0 < b / (k : ℝ) := div_pos hb hkR
  filter_upwards [hardReferenceBornDensity_ae_tail_lower M hk hb.le hbquarter]
      with z hz
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hbdiv) hz)

/-- The hard reference density meets the measurability, nonvanishing, and
finiteness hypotheses used by `WithDensityPearson`. -/
theorem hardReferenceBornDensity_withDensityPearson_conditions
    (M : DominatedPOVM (k + 2) Outcome)
    (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    AEMeasurable
        (bornDensityFrom M.effect
          (hardReferenceDensityOperator k b hk hb.le hbquarter)) M.base ∧
      (∀ᵐ z ∂M.base,
        bornDensityFrom M.effect
          (hardReferenceDensityOperator k b hk hb.le hbquarter) z ≠ 0) ∧
      (∀ᵐ z ∂M.base,
        bornDensityFrom M.effect
          (hardReferenceDensityOperator k b hk hb.le hbquarter) z ≠ ∞) := by
  refine ⟨(measurable_bornDensityFrom M _).aemeasurable,
    hardReferenceBornDensity_ae_ne_zero M hk hb hbquarter, ?_⟩
  exact bornDensityFrom_ae_ne_top M _

end PhysicalPOVM.DominatedPOVM

end


end TomographyOracleCore
