import TomographyOracleCore.PhysicalHaarDesign

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM

noncomputable section

/-!
# Repeated physical designs from an arbitrary matrix-valued POVM

The physical risk layer fixes both public seeds and one-copy outcomes to the
universal standard-Borel code `ℝ`.  This file factors the real coding and
finite-product construction out of the projective-Haar specialization.  It
will be used by the concrete finite Cho--Kim POVM; no statistical property is
assumed or asserted here.
-/

namespace PhysicalRisk

variable {D T : ℕ}

/-- Transport any matrix-valued dominated POVM through the canonical Borel
isomorphism between finite complex matrices and `ℝ`. -/
noncomputable def realCodedMatrixPOVM
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) :
    DominatedPOVM D ℝ :=
  M.mapMeasurableEquiv (haarOutcomeRealMeasurableEquiv D M.dimension_pos)

@[simp]
theorem realCodedMatrixPOVM_effect
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (z : ℝ) :
    (realCodedMatrixPOVM M).effect z =
      M.effect (decodeHaarOutcome D M.dimension_pos z) :=
  rfl

theorem realCodedMatrixPOVM_bornMeasure
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (rho : DensityOperator (Fin D)) :
    (realCodedMatrixPOVM M).bornMeasure rho =
      Measure.map (encodeHaarOutcome D M.dimension_pos) (M.bornMeasure rho) :=
  DominatedPOVM.mapMeasurableEquiv_bornMeasure M
    (haarOutcomeRealMeasurableEquiv D M.dimension_pos) rho

/-- Decoding the universal real code recovers the original matrix-valued
Born law of an arbitrary matrix POVM. -/
theorem map_decodeHaarOutcome_realCodedMatrixPOVM_bornMeasure
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ))
    (rho : DensityOperator (Fin D)) :
    Measure.map (decodeHaarOutcome D M.dimension_pos)
        ((realCodedMatrixPOVM M).bornMeasure rho) =
      M.bornMeasure rho := by
  rw [realCodedMatrixPOVM_bornMeasure]
  rw [Measure.map_map
    (measurable_decodeHaarOutcome D M.dimension_pos)
    (measurable_encodeHaarOutcome D M.dimension_pos)]
  have hcomp :
      decodeHaarOutcome D M.dimension_pos ∘
          encodeHaarOutcome D M.dimension_pos = id := by
    funext B
    exact decodeHaarOutcome_encodeHaarOutcome D M.dimension_pos B
  rw [hcomp, Measure.map_id]

/-- Conditional product kernel for repeated independent uses of one fixed
matrix-valued POVM, after real coding. -/
noncomputable def repeatedMatrixPOVMOutcomesKernel
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    Kernel (DensityOperator (Fin D) × ℝ) (Fin T → ℝ) where
  toFun := fun p => Measure.pi fun _ : Fin T =>
    (realCodedMatrixPOVM M).bornMeasure p.1
  measurable' := by
    apply measurable_measure_pi_probability
    · intro t
      exact (realCodedMatrixPOVM M).born_measurable.comp measurable_fst
    · intro p t
      exact (realCodedMatrixPOVM M).born_probability p.1

instance repeatedMatrixPOVMOutcomesKernel_isMarkov
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    IsMarkovKernel (repeatedMatrixPOVMOutcomesKernel M T) where
  isProbabilityMeasure p := by
    change IsProbabilityMeasure
      (Measure.pi fun _ : Fin T =>
        (realCodedMatrixPOVM M).bornMeasure p.1)
    letI : IsProbabilityMeasure
        ((realCodedMatrixPOVM M).bornMeasure p.1) :=
      (realCodedMatrixPOVM M).born_probability p.1
    infer_instance

@[simp]
theorem repeatedMatrixPOVMOutcomesKernel_apply
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (p : DensityOperator (Fin D) × ℝ) :
    repeatedMatrixPOVMOutcomesKernel M T p =
      Measure.pi fun _ : Fin T =>
        (realCodedMatrixPOVM M).bornMeasure p.1 :=
  rfl

/-- Exact randomized-nonadaptive physical design obtained by repeating one
matrix-valued POVM independently.  The public seed is deterministic. -/
noncomputable def constantMatrixPOVMPhysicalDesign
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    Design D T :=
  { dimension_pos := M.dimension_pos
    seed := Measure.dirac (0 : ℝ)
    seed_probability := by infer_instance
    measurement := fun _ _ => realCodedMatrixPOVM M
    shot_measurable := fun _ =>
      (realCodedMatrixPOVM M).born_measurable.comp measurable_fst
    outcomes := repeatedMatrixPOVMOutcomesKernel M T
    outcomes_markov := by infer_instance
    outcomes_eq_pi := fun _ => rfl }

@[simp]
theorem constantMatrixPOVMPhysicalDesign_seed
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ) :
    (constantMatrixPOVMPhysicalDesign M T).seed = Measure.dirac (0 : ℝ) :=
  rfl

@[simp]
theorem constantMatrixPOVMPhysicalDesign_measurement
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (t : Fin T) (seed : ℝ) :
    (constantMatrixPOVMPhysicalDesign M T).measurement t seed =
      realCodedMatrixPOVM M :=
  rfl

@[simp]
theorem constantMatrixPOVMPhysicalDesign_outcomes
    (M : DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ)) (T : ℕ)
    (p : DensityOperator (Fin D) × ℝ) :
    (constantMatrixPOVMPhysicalDesign M T).outcomes p =
      Measure.pi fun _ : Fin T =>
        (realCodedMatrixPOVM M).bornMeasure p.1 :=
  rfl

end PhysicalRisk

end

end TomographyOracleCore
