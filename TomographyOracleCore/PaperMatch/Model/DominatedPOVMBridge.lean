import TomographyOracleCore.PaperMatch.Model.OperatorDesign

set_option autoImplicit false

namespace TomographyOracleCore.PhysicalPOVM.DominatedPOVM
open MeasureTheory ProbabilityTheory Matrix MatrixReduction
open scoped BigOperators ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

def integratedEffect (M : DominatedPOVM D Outcome) (s : Set Outcome) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => ∫ z in s, M.effect z i j ∂M.base

theorem integratedEffect_isHermitian (M : DominatedPOVM D Outcome) (s : Set Outcome) :
    (M.integratedEffect s).IsHermitian := by
  apply Matrix.IsHermitian.ext_iff.mpr
  intro i j
  change star (∫ z in s, M.effect z j i ∂M.base) = ∫ z in s, M.effect z i j ∂M.base
  change (starRingEnd ℂ) (∫ z in s, M.effect z j i ∂M.base) = _
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae M.effect_ae_posSemidef] with z hz
  exact hz.isHermitian.apply i j

theorem integrable_quadratic_effect (M : DominatedPOVM D Outcome) (v : Fin D → ℂ) :
    Integrable (fun z => OperatorPOVM.quadratic (M.effect z) v) M.base :=
  integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((M.effect_integrable i j).const_mul (star (v i))).mul_const (v j)

theorem quadratic_integratedEffect (M : DominatedPOVM D Outcome) (v : Fin D → ℂ)
    (s : Set Outcome) :
    OperatorPOVM.quadratic (M.integratedEffect s) v =
      ∫ z in s, OperatorPOVM.quadratic (M.effect z) v ∂M.base := by
  unfold OperatorPOVM.quadratic
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (((M.effect_integrable i j).const_mul (star (v i))).mul_const (v j)).integrableOn]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ =>
    (((M.effect_integrable i j).const_mul (star (v i))).mul_const (v j)).integrableOn]
  simp only [integral_mul_const, integral_const_mul]
  rfl

theorem integratedEffect_posSemidef (M : DominatedPOVM D Outcome) (s : Set Outcome) :
    (M.integratedEffect s).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (M.integratedEffect_isHermitian s)
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · rw [← OperatorPOVM.quadratic_eq, M.quadratic_integratedEffect v s]
    change 0 ≤ Complex.reCLM (∫ z in s, OperatorPOVM.quadratic (M.effect z) v ∂M.base)
    rw [← Complex.reCLM.integral_comp_comm (M.integrable_quadratic_effect v).integrableOn]
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_of_ae M.effect_ae_posSemidef] with z hz
    change 0 ≤ (OperatorPOVM.quadratic (M.effect z) v).re
    rw [OperatorPOVM.quadratic_eq]
    exact (hz.dotProduct_mulVec_nonneg v).1
  · exact ((M.integratedEffect_isHermitian s).im_star_dotProduct_mulVec_self v).symm

/-- Integrating an effect density gives a countably additive operator-valued
measure. This is the reverse direction of the representation theorem. -/
def toOperator (M : DominatedPOVM D Outcome) : OperatorPOVM D Outcome where
  dimension_pos := M.dimension_pos
  entry := fun i j => M.base.withDensityᵥ (fun z => M.effect z i j)
  positive := by
    intro s hs
    have heq : (fun i j => (M.base.withDensityᵥ (fun z => M.effect z i j)) s) =
        M.integratedEffect s := by
      funext i j
      exact withDensityᵥ_apply (M.effect_integrable i j) hs
    rw [heq]
    exact M.integratedEffect_posSemidef s
  normalized := by
    ext i j
    rw [withDensityᵥ_apply (M.effect_integrable i j) MeasurableSet.univ, Measure.restrict_univ]
    exact M.integral_effect_eq_one i j

theorem toOperator_apply (M : DominatedPOVM D Outcome) (s : Set Outcome) (hs : MeasurableSet s) :
    M.toOperator.apply s = M.integratedEffect s := by
  ext i j
  exact withDensityᵥ_apply (M.effect_integrable i j) hs

theorem integrable_bornTrace (M : DominatedPOVM D Outcome) (rho : DensityOperator (Fin D)) :
    Integrable (fun z => (rho.matrix * M.effect z).trace) M.base := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (M.effect_integrable j i).const_mul (rho.matrix i j)

theorem bornTrace_integratedEffect (M : DominatedPOVM D Outcome) (rho : DensityOperator (Fin D))
    (s : Set Outcome) :
    (rho.matrix * M.integratedEffect s).trace =
      ∫ z in s, (rho.matrix * M.effect z).trace ∂M.base := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((M.effect_integrable j i).const_mul (rho.matrix i j)).integrableOn]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ =>
    ((M.effect_integrable j i).const_mul (rho.matrix i j)).integrableOn]
  simp only [integral_const_mul]
  rfl

/-- The reverse construction preserves every statewise Born law exactly. -/
theorem toOperator_bornMeasure (M : DominatedPOVM D Outcome) (rho : DensityOperator (Fin D)) :
    M.toOperator.bornMeasure rho = M.bornMeasure rho := by
  apply Measure.ext
  intro s hs
  rw [OperatorPOVM.bornMeasure_apply _ _ s hs, M.toOperator_apply s hs,
    M.bornTrace_integratedEffect rho s]
  change ENNReal.ofReal (Complex.reCLM (∫ z in s, (rho.matrix * M.effect z).trace ∂M.base)) = _
  rw [← Complex.reCLM.integral_comp_comm (M.integrable_bornTrace rho).integrableOn]
  change ENNReal.ofReal (∫ z in s, (rho.matrix * M.effect z).trace.re ∂M.base) = _
  exact (ofReal_integral_eq_lintegral_ofReal (M.integrable_bornTrace rho).re.integrableOn
    (ae_restrict_of_ae (M.born_density_ae_nonnegative rho))).trans (withDensity_apply _ hs).symm

end
end TomographyOracleCore.PhysicalPOVM.DominatedPOVM
