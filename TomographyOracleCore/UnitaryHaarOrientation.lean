import TomographyOracleCore.HaarRankMProjector
import TomographyOracleCore.HardReferenceState
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace TomographyOracleCore

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

/-!
# Normalized Haar probability on the finite unitary group

The unitary matrix group is compact.  Mathlib's Haar measure is therefore
finite, and its normalization is a genuine probability measure.  This file
also records the exact left-invariance used by the hidden-orientation lower
bound.  No moment or tomography claim is assumed here.
-/

/-- The finite-dimensional unitary group is compact, including in dimension
zero.  For positive dimension it is the closed, norm-bounded unitary subset
of the finite-dimensional matrix algebra. -/
noncomputable instance unitaryMatrixCompactSpace (D : ℕ) :
    CompactSpace (unitary (Matrix (Fin D) (Fin D) ℂ)) := by
  by_cases hD : D = 0
  · subst D
    infer_instance
  · letI : Nonempty (Fin D) :=
      Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hD)
    apply isCompact_iff_compactSpace.mp
    apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
    rw [Metric.isBounded_iff]
    refine ⟨2, ?_⟩
    intro U hU V hV
    calc
      dist U V = ‖U - V‖ := dist_eq_norm U V
      _ ≤ ‖U‖ + ‖V‖ := norm_sub_le U V
      _ = 2 := by
        rw [CStarRing.norm_of_mem_unitary hU,
          CStarRing.norm_of_mem_unitary hV]
        norm_num

/-- Haar measure on the compact unitary matrix group, normalized to mass one. -/
noncomputable def unitaryHaarProbability (D : ℕ) :
    Measure (unitary (Matrix (Fin D) (Fin D) ℂ)) :=
  let μ : Measure (unitary (Matrix (Fin D) (Fin D) ℂ)) := Measure.haar
  (μ univ)⁻¹ • μ

private theorem unitaryHaar_univ_ne_zero (D : ℕ) :
    (Measure.haar : Measure (unitary (Matrix (Fin D) (Fin D) ℂ))) univ ≠ 0 := by
  exact isOpen_univ.measure_ne_zero _ univ_nonempty

private theorem unitaryHaar_univ_ne_top (D : ℕ) :
    (Measure.haar : Measure (unitary (Matrix (Fin D) (Fin D) ℂ))) univ ≠ ∞ := by
  exact ne_of_lt isCompact_univ.measure_lt_top

instance unitaryHaarProbability_isProbabilityMeasure (D : ℕ) :
    IsProbabilityMeasure (unitaryHaarProbability D) where
  measure_univ := by
    rw [unitaryHaarProbability, Measure.smul_apply]
    change
      ((Measure.haar : Measure (unitary (Matrix (Fin D) (Fin D) ℂ))) univ)⁻¹ *
          (Measure.haar : Measure (unitary (Matrix (Fin D) (Fin D) ℂ))) univ = 1
    exact ENNReal.inv_mul_cancel
      (unitaryHaar_univ_ne_zero D) (unitaryHaar_univ_ne_top D)

instance unitaryHaarProbability_isMulLeftInvariant (D : ℕ) :
    (unitaryHaarProbability D).IsMulLeftInvariant := by
  unfold unitaryHaarProbability
  infer_instance

/-- On the compact unitary group, normalized left Haar probability is also
right invariant.  This follows from uniqueness of Haar probability: every
right translate remains a left-Haar probability. -/
theorem unitaryHaarProbability_map_mul_right (D : ℕ)
    (V : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    Measure.map (fun U ↦ U * V) (unitaryHaarProbability D) =
      unitaryHaarProbability D := by
  letI : Measure.IsHaarMeasure (unitaryHaarProbability D) := by
    unfold unitaryHaarProbability
    exact Measure.IsHaarMeasure.smul _
      (ENNReal.inv_ne_zero.mpr (unitaryHaar_univ_ne_top D))
      (ENNReal.inv_ne_top.mpr (unitaryHaar_univ_ne_zero D))
  let ν := Measure.map (fun U ↦ U * V) (unitaryHaarProbability D)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop :
      AEMeasurable (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) ↦ U * V)
        (unitaryHaarProbability D))
  letI : Measure.IsHaarMeasure ν := by
    dsimp only [ν]
    exact Measure.isHaarMeasure_map_mul_right (unitaryHaarProbability D) V
  have h : ν = unitaryHaarProbability D := by
    apply Measure.isHaarMeasure_eq_of_isProbabilityMeasure
  exact h

instance unitaryHaarProbability_isMulRightInvariant (D : ℕ) :
    (unitaryHaarProbability D).IsMulRightInvariant where
  map_mul_right_eq_self := unitaryHaarProbability_map_mul_right D

/-- Normalized unitary Haar probability is invariant under left
multiplication by every fixed unitary. -/
theorem unitaryHaarProbability_map_mul_left (D : ℕ)
    (V : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    Measure.map (fun U ↦ V * U) (unitaryHaarProbability D) =
      unitaryHaarProbability D := by
  exact MeasureTheory.map_mul_left_eq_self (unitaryHaarProbability D) V

/-- Integral form of normalized unitary-Haar left invariance. -/
theorem integral_comp_unitaryHaarProbability_mul_left
    (D : ℕ) (V : unitary (Matrix (Fin D) (Fin D) ℂ))
    (f : unitary (Matrix (Fin D) (Fin D) ℂ) → ℝ)
    (hf : AEStronglyMeasurable f (unitaryHaarProbability D)) :
    (∫ U, f (V * U) ∂unitaryHaarProbability D) =
      ∫ U, f U ∂unitaryHaarProbability D := by
  have hmul : Measurable
      (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) ↦ V * U) := by
    fun_prop
  have hfmap : AEStronglyMeasurable f
      (Measure.map (fun U ↦ V * U) (unitaryHaarProbability D)) := by
    rw [unitaryHaarProbability_map_mul_left]
    exact hf
  calc
    (∫ U, f (V * U) ∂unitaryHaarProbability D) =
        ∫ U, f U ∂Measure.map (fun U ↦ V * U)
          (unitaryHaarProbability D) := by
      symm
      exact integral_map hmul.aemeasurable hfmap
    _ = ∫ U, f U ∂unitaryHaarProbability D := by
      rw [unitaryHaarProbability_map_mul_left]

/-- Integral form of normalized unitary-Haar right invariance.  Keeping both
forms available avoids an orientation convention in later orbit maps. -/
theorem integral_comp_unitaryHaarProbability_mul_right
    (D : ℕ) (V : unitary (Matrix (Fin D) (Fin D) ℂ))
    (f : unitary (Matrix (Fin D) (Fin D) ℂ) → ℝ)
    (hf : AEStronglyMeasurable f (unitaryHaarProbability D)) :
    (∫ U, f (U * V) ∂unitaryHaarProbability D) =
      ∫ U, f U ∂unitaryHaarProbability D := by
  have hmul : Measurable
      (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) ↦ U * V) := by
    fun_prop
  have hfmap : AEStronglyMeasurable f
      (Measure.map (fun U ↦ U * V) (unitaryHaarProbability D)) := by
    rw [unitaryHaarProbability_map_mul_right]
    exact hf
  calc
    (∫ U, f (U * V) ∂unitaryHaarProbability D) =
        ∫ U, f U ∂Measure.map (fun U ↦ U * V)
          (unitaryHaarProbability D) := by
      symm
      exact integral_map hmul.aemeasurable hfmap
    _ = ∫ U, f U ∂unitaryHaarProbability D := by
      rw [unitaryHaarProbability_map_mul_right]

/-! ## Measurable oriented density operators -/

/-- Unitary conjugation of a fixed density operator is measurable for the
coordinate sigma algebra used by the physical POVM model. -/
theorem measurable_unitaryConjugateDensityOperator {D : ℕ}
    (ρ : MatrixReduction.DensityOperator (Fin D)) :
    Measurable (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) ↦
      unitaryConjugateDensityOperator U ρ) := by
  apply measurable_comap_iff.mpr
  change Measurable (fun U ↦ fun p : Fin D × Fin D ↦
    unitaryConjugateMatrix U ρ.matrix p.1 p.2)
  rw [measurable_pi_iff]
  intro p
  exact (measurable_complexMatrix_apply (Fin D) p.1 p.2).comp
    (continuous_unitaryConjugateMatrix_fixed ρ.matrix).measurable

/-- The commonly oriented hard-projector state is a measurable function of
the hidden unitary orientation. -/
theorem measurable_orientedHardProjectorDensityOperator {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    Measurable (fun U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
      orientedHardProjectorDensityOperator U P b hm hb0 hbquarter) := by
  exact measurable_unitaryConjugateDensityOperator _

/-- Apply the same hidden unitary orientation to the hard reference state. -/
noncomputable def orientedHardReferenceDensityOperator
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    MatrixReduction.DensityOperator (Fin (k + 2)) :=
  unitaryConjugateDensityOperator U
    (hardReferenceDensityOperator k b hk hb0 hbquarter)

@[simp] theorem orientedHardReferenceDensityOperator_matrix
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    (orientedHardReferenceDensityOperator k b hk hb0 hbquarter U).matrix =
      unitaryConjugateMatrix U (hardReferenceMatrix k b) := rfl

/-- The oriented hard reference is measurable in its hidden unitary. -/
theorem measurable_orientedHardReferenceDensityOperator
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    Measurable (orientedHardReferenceDensityOperator
      k b hk hb0 hbquarter) := by
  exact measurable_unitaryConjugateDensityOperator _

end

end TomographyOracleCore
