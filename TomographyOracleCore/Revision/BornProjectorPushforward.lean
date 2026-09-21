import TomographyOracleCore.Revision.FourthVectorBoundary
import TomographyOracleCore.Candidate2FiniteBornVectorLaw
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

namespace TomographyOracleCore.Revision.BornProjectorPushforward

open MeasureTheory MatrixReduction Candidate2FiniteBornVectorLaw Candidate2PhaseRandomizedLaw
open Candidate2PhaseRandomization FourthVectorBoundary
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
noncomputable section

variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]

theorem vectorProjector_complex_smul (c : ℂ) (x : EuclideanSpace ℂ (Fin D)) :
    vectorProjector (c • x) = (‖c‖ ^ 2 : ℝ) • vectorProjector x := by
  ext i j
  simp only [vectorProjector, Matrix.vecMulVec_apply, Pi.star_apply,
    PiLp.smul_apply, Matrix.smul_apply, smul_eq_mul, star_mul]
  have hc : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    simp only [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  calc
    _ = (c * star c) * (x i * star (x j)) := by ring
    _ = _ := by rw [hc]; rfl

theorem vectorProjector_real_smul (c : ℝ) (x : EuclideanSpace ℂ (Fin D)) :
    vectorProjector (c • x) = c ^ 2 • vectorProjector x := by
  ext i j
  change ((c : ℂ) * x i) * star ((c : ℂ) * x j) =
    ((c ^ 2 : ℝ) : ℂ) * (x i * star (x j))
  simp only [star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

theorem vectorProjector_phaseVector (j : Fin 4) (x : EuclideanSpace ℂ (Fin D)) :
    vectorProjector (phaseVector j x) = vectorProjector x := by
  rw [phaseVector, vectorProjector_complex_smul, quarterPhase_norm, one_pow, one_smul]

def normalizedProjector (D : ℕ) (x : EuclideanSpace ℂ (Fin D)) :
    Matrix (Fin D) (Fin D) ℂ := ((D : ℝ) + 1)⁻¹ • vectorProjector x

theorem continuous_normalizedProjector (D : ℕ) : Continuous (normalizedProjector D) := by
  unfold normalizedProjector vectorProjector Matrix.vecMulVec
  fun_prop

theorem normalizedProjector_scaledMeasurement
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    normalizedProjector D (candidate2ScaledMeasurementVector U b) =
      finiteUnitaryMeasurementProjector U b := by
  rw [normalizedProjector, candidate2ScaledMeasurementVector, vectorProjector_real_smul,
    Real.sq_sqrt (by positivity), smul_smul, inv_mul_cancel₀ (by positivity), one_smul,
    finiteUnitaryMeasurementProjector_eq_complexSphereProjector]
  rfl

theorem normalizedProjector_phaseVector (j : Fin 4) (x : EuclideanSpace ℂ (Fin D)) :
    normalizedProjector D (phaseVector j x) = normalizedProjector D x := by
  rw [normalizedProjector, vectorProjector_phaseVector]
  rfl

/-- Removing the phase leaves precisely the physical projector law. -/
theorem normalizedProjector_map_phaseRandomized (mu : Measure (EuclideanSpace ℂ (Fin D)))
    [IsProbabilityMeasure mu] :
    (phaseRandomizedLaw mu).map (normalizedProjector D) = mu.map (normalizedProjector D) := by
  rw [phaseRandomizedLaw, Measure.map_map (continuous_normalizedProjector D).measurable
    measurable_phaseProductMap]
  have hf : normalizedProjector D ∘ phaseProductMap = normalizedProjector D ∘ Prod.snd := by
    funext z
    exact normalizedProjector_phaseVector z.1 z.2
  rw [hf, ← Measure.map_map (continuous_normalizedProjector D).measurable measurable_snd,
    phaseProductMeasure, Measure.map_snd_prod, measure_univ, one_smul]

/-- The scaled Born vectors push forward to the literal finite-POVM Born
measure, including all repeated projectors and their combined weights. -/
theorem normalizedProjector_map_bornVectorLaw (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    (finiteUnitaryBornVectorLaw U rho).map (normalizedProjector D) =
      (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  letI : IsProbabilityMeasure ((finiteUnitaryBornVectorLaw U rho).map (normalizedProjector D)) :=
    Measure.isProbabilityMeasure_map (continuous_normalizedProjector D).measurable.aemeasurable
  letI : IsProbabilityMeasure ((finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) :=
    (finiteUnitaryProjectivePOVM D hD U).born_probability rho
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map (continuous_normalizedProjector D).measurable.aemeasurable
    g.continuous.aestronglyMeasurable, integral_finiteUnitaryBornVectorLaw_real_eq_sum hD,
    integral_finiteUnitaryProjectivePOVM_bornMeasure_real_eq_sum hD]
  simp only [normalizedProjector_scaledMeasurement, finiteUnitaryBornWeight, mul_comm]

theorem normalizedProjector_map_phaseBornVectorLaw (hD : 0 < D)
    (U : A → Matrix.unitaryGroup (Fin D) ℂ) (rho : DensityOperator (Fin D)) :
    (finiteUnitaryPhaseRandomizedBornVectorLaw U rho).map (normalizedProjector D) =
      (finiteUnitaryProjectivePOVM D hD U).bornMeasure rho := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  rw [finiteUnitaryPhaseRandomizedBornVectorLaw, normalizedProjector_map_phaseRandomized,
    normalizedProjector_map_bornVectorLaw hD]

end
end TomographyOracleCore.Revision.BornProjectorPushforward
