import TomographyOracleCore.PaperMatch.PureTensorTesting
import TomographyOracleCore.PhysicalReferenceDensity

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM
open Revision.MatrixTensorPi
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

section General
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

theorem integrable_matrix_inner (μ : Measure Ω) (F : Ω → Matrix ι ι ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ) (u v : EuclideanSpace ℂ ι) :
    Integrable (fun x => ⟪u, (F x).toEuclideanLin v⟫_ℂ) μ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, dotProduct, Matrix.mulVec, dotProduct, Finset.sum_mul]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact ((hF i j).mul_const (v j)).mul_const (star (u i))

theorem inner_real_smul_matrix (c : ℝ) (F : Matrix ι ι ℂ) (u v : EuclideanSpace ℂ ι) :
    ⟪u, (c • F).toEuclideanLin v⟫_ℂ = (c : ℂ) * ⟪u, F.toEuclideanLin v⟫_ℂ := by
  change ⟪u, ((c : ℂ) • F).toEuclideanLin v⟫_ℂ = _
  rw [map_smul, LinearMap.smul_apply, inner_smul_right]

end General

section ProductPOVM
variable {D T : ℕ} {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]

def productEffect (M : Fin T → DominatedPOVM D Ω) (y : Fin T → Ω) :
    Matrix (Fin T → Fin D) (Fin T → Fin D) ℂ :=
  tensorPi (fun t => (M t).effect (y t))

def productBase (M : Fin T → DominatedPOVM D Ω) : Measure (Fin T → Ω) :=
  Measure.pi (fun t => (M t).base)

theorem productEffect_integrable (M : Fin T → DominatedPOVM D Ω)
    (i j : Fin T → Fin D) :
    Integrable (fun y => productEffect M y i j) (productBase M) := by
  letI (t : Fin T) : IsFiniteMeasure (M t).base := (M t).base_finite
  exact Integrable.fintype_prod (fun t => (M t).effect_integrable (i t) (j t))

theorem productEffect_ae_pos (M : Fin T → DominatedPOVM D Ω) :
    ∀ᵐ y ∂productBase M, (productEffect M y).PosSemidef := by
  letI (t : Fin T) : IsFiniteMeasure (M t).base := (M t).base_finite
  have hall : ∀ᵐ y ∂productBase M, ∀ t, ((M t).effect (y t)).PosSemidef :=
    Filter.eventually_all.mpr fun t =>
      (Measure.tendsto_eval_ae_ae (μ := fun t => (M t).base) (i := t)).eventually ((M t).effect_ae_posSemidef)
  filter_upwards [hall] with y hy
  exact tensorPi_posSemidef _ hy

theorem productEffect_normalized (M : Fin T → DominatedPOVM D Ω) :
    entryIntegral (productBase M) (productEffect M) = 1 := by
  letI (t : Fin T) : IsFiniteMeasure (M t).base := (M t).base_finite
  ext i j
  change (∫ y : Fin T → Ω, ∏ t, (M t).effect (y t) (i t) (j t)
    ∂Measure.pi (fun t => (M t).base)) = (1 : Matrix _ _ ℂ) i j
  rw [integral_fintype_prod_eq_prod (fun t z => (M t).effect z (i t) (j t))]
  simp_rw [(M _).integral_effect_eq_one]
  exact congrFun (congrFun (tensorPi_one (J := Fin T) (α := Fin D)) i) j

def nonnegativeBornTrace (M : DominatedPOVM D Ω) (ρ : DensityOperator (Fin D)) (z : Ω) : ℝ :=
  max ((ρ.matrix * M.effect z).trace.re) 0

theorem nonnegativeBornTrace_measurable (M : DominatedPOVM D Ω)
    (ρ : DensityOperator (Fin D)) : Measurable (nonnegativeBornTrace M ρ) := by
  unfold nonnegativeBornTrace
  apply Measurable.max _ measurable_const
  apply Complex.measurable_re.comp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  exact measurable_const.mul (M.effect_measurable j i)

theorem nonnegativeBornTrace_integrable (M : DominatedPOVM D Ω)
    (ρ : DensityOperator (Fin D)) : Integrable (nonnegativeBornTrace M ρ) M.base := by
  apply Integrable.pos_part
  change Integrable (fun a => RCLike.re ((ρ.matrix * M.effect a).trace)) M.base
  apply Integrable.re
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply integrable_finsetSum
  intro i hi
  apply integrable_finsetSum
  intro j hj
  exact (M.effect_integrable j i).const_mul (ρ.matrix i j)

theorem productBorn_density (M : Fin T → DominatedPOVM D Ω) (ρ : DensityOperator (Fin D)) :
    Measure.pi (fun t => (M t).bornMeasure ρ) =
      (productBase M).withDensity (fun y => ENNReal.ofReal (∏ t, nonnegativeBornTrace (M t) ρ (y t))) := by
  letI (t : Fin T) : IsFiniteMeasure (M t).base := (M t).base_finite
  letI (t : Fin T) : IsProbabilityMeasure ((M t).bornMeasure ρ) := (M t).born_probability ρ
  apply Revision.GaussianChangeOfMeasure.pi_eq_withDensity_of_coordinates
  · exact fun t => nonnegativeBornTrace_integrable (M t) ρ
  · exact fun t z => le_max_right _ _
  · intro t
    change (M t).base.withDensity (fun x => ENNReal.ofReal ((ρ.matrix * (M t).effect x).trace.re)) = _
    simp [nonnegativeBornTrace]

theorem pureBorn_inner (M : DominatedPOVM D Ω)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) (z : Ω) :
    ((complexSpherePureState v).matrix * M.effect z).trace =
      ⟪v.1, (M.effect z).toEuclideanLin v.1⟫_ℂ := by
  rw [Matrix.trace_mul_comm]
  simp only [complexSpherePureState, complexSphereProjector, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin]
  rfl

theorem pureBorn_inner_eq_nonnegative (M : DominatedPOVM D Ω)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) {z : Ω}
    (hF : (M.effect z).PosSemidef) :
    ⟪v.1, (M.effect z).toEuclideanLin v.1⟫_ℂ =
      (nonnegativeBornTrace M (complexSpherePureState v) z : ℂ) := by
  have hp : 0 ≤ ⟪v.1, (M.effect z).toEuclideanLin v.1⟫_ℂ := by
    simpa [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
      Matrix.toLin'_apply, dotProduct_comm] using hF.dotProduct_mulVec_nonneg v.1.ofLp
  have hr := Complex.nonneg_iff.mp hp
  unfold nonnegativeBornTrace
  rw [pureBorn_inner, max_eq_left hr.1]
  apply Complex.ext
  · rfl
  · simpa using hr.2.symm

/-- The product Born density is exactly the tensor-state quadratic form. -/
theorem productBorn_inner_ae (M : Fin T → DominatedPOVM D Ω)
    (v : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    ∀ᵐ y ∂productBase M,
      ⟪tensorVector (fun _ : Fin T => v.1),
        (productEffect M y).toEuclideanLin (tensorVector (fun _ : Fin T => v.1))⟫_ℂ =
        ((∏ t, nonnegativeBornTrace (M t) (complexSpherePureState v) (y t) : ℝ) : ℂ) := by
  letI (t : Fin T) : IsFiniteMeasure (M t).base := (M t).base_finite
  have hall : ∀ᵐ y ∂productBase M, ∀ t, ((M t).effect (y t)).PosSemidef :=
    Filter.eventually_all.mpr fun t =>
      (Measure.tendsto_eval_ae_ae (μ := fun t => (M t).base) (i := t)).eventually ((M t).effect_ae_posSemidef)
  filter_upwards [hall] with y hy
  rw [productEffect, tensorPi_inner, Complex.ofReal_prod]
  exact Finset.prod_congr rfl (fun t _ => pureBorn_inner_eq_nonnegative (M t) v (hy t))

end ProductPOVM
end
end TomographyOracleCore.PaperMatch.RankMinimax
