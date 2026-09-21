import TomographyOracleCore.ProjectiveHaarPOVM
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Countably additive operator-valued POVMs

This definition starts with complex measures for the matrix entries. Positivity
and normalization are imposed on the operator-valued measure itself; an effect
density or a Radon--Nikodym representation is not part of the input.
-/
set_option autoImplicit false

namespace TomographyOracleCore.PhysicalPOVM
open MeasureTheory Matrix
open scoped BigOperators ComplexOrder
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

structure OperatorPOVM (D : ℕ) (Outcome : Type*) [MeasurableSpace Outcome] where
  dimension_pos : 0 < D
  entry : Fin D → Fin D → ComplexMeasure Outcome
  positive : ∀ s, MeasurableSet s → Matrix.PosSemidef ((fun i j => entry i j s) : Matrix (Fin D) (Fin D) ℂ)
  normalized : ((fun i j => entry i j Set.univ) : Matrix (Fin D) (Fin D) ℂ) = (1 : Matrix (Fin D) (Fin D) ℂ)

namespace OperatorPOVM
variable {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome]

def apply (M : OperatorPOVM D Outcome) (s : Set Outcome) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => M.entry i j s

def traceSigned (M : OperatorPOVM D Outcome) : SignedMeasure Outcome :=
  ∑ i : Fin D, (M.entry i i).re

theorem traceSigned_apply (M : OperatorPOVM D Outcome) (s : Set Outcome) :
    M.traceSigned s = (M.apply s).trace.re := by
  simp only [traceSigned, FunLike.coe_sum, Finset.sum_apply, apply, Matrix.trace, Matrix.diag, Complex.re_sum]
  rfl

theorem traceSigned_nonnegative (M : OperatorPOVM D Outcome) :
    0 ≤[Set.univ] M.traceSigned := by
  apply (VectorMeasure.restrict_le_restrict_iff _ _ MeasurableSet.univ).2
  intro s hs _
  rw [_root_.zero_apply, traceSigned_apply]
  exact (M.positive s hs).trace_nonneg.1

/-- The canonical finite dominating measure: the trace of the POVM. -/
def traceMeasure (M : OperatorPOVM D Outcome) : Measure Outcome :=
  M.traceSigned.toMeasureOfZeroLE Set.univ MeasurableSet.univ M.traceSigned_nonnegative

instance traceMeasure_finite (M : OperatorPOVM D Outcome) : IsFiniteMeasure M.traceMeasure := by
  unfold traceMeasure
  infer_instance

theorem traceMeasure_real (M : OperatorPOVM D Outcome) (s : Set Outcome) (hs : MeasurableSet s) :
    M.traceMeasure.real s = (M.apply s).trace.re := by
  rw [traceMeasure, SignedMeasure.toMeasureOfZeroLE_real_apply _ _ _ hs, Set.univ_inter,
    traceSigned_apply]

theorem traceMeasure_univ (M : OperatorPOVM D Outcome) : M.traceMeasure Set.univ = D := by
  have h := M.traceMeasure_real Set.univ MeasurableSet.univ
  have hn : M.apply Set.univ = 1 := M.normalized
  rw [hn, Matrix.trace_one] at h
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (by simp)).mp
  simpa [measureReal_def] using h

/-- A zero trace-measure set has zero effect operator. -/
theorem apply_eq_zero_of_traceMeasure_eq_zero (M : OperatorPOVM D Outcome)
    (s : Set Outcome) (hs : MeasurableSet s) (hz : M.traceMeasure s = 0) :
    M.apply s = 0 := by
  have hp := M.positive s hs
  apply hp.trace_eq_zero_iff.mp
  apply Complex.ext
  · have h := M.traceMeasure_real s hs
    rw [measureReal_def, hz, ENNReal.toReal_zero] at h
    exact h.symm
  · exact hp.trace_nonneg.2.symm

/-- Absolute continuity is a consequence of positivity, not an assumption. -/
theorem entry_absolutelyContinuous (M : OperatorPOVM D Outcome) (i j : Fin D) :
    M.entry i j ≪ᵥ M.traceMeasure.toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hz
  have hz' : M.traceMeasure s = 0 := by
    simpa only [Measure.toENNRealVectorMeasure_apply, if_pos hs] using hz
  exact congrFun (congrFun (M.apply_eq_zero_of_traceMeasure_eq_zero s hs hz') i) j

/-- The entrywise Radon--Nikodym derivative with respect to the trace measure. -/
def density (M : OperatorPOVM D Outcome) (z : Outcome) : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => (M.entry i j).rnDeriv M.traceMeasure z

theorem density_integrable (M : OperatorPOVM D Outcome) (i j : Fin D) :
    Integrable (fun z => M.density z i j) M.traceMeasure :=
  ComplexMeasure.integrable_rnDeriv _ _

theorem density_measurable (M : OperatorPOVM D Outcome) (i j : Fin D) :
    Measurable (fun z => M.density z i j) := by
  change Measurable (fun z => ⟨_, _⟩ : Outcome → ℂ)
  have hr := SignedMeasure.measurable_rnDeriv (M.entry i j).re M.traceMeasure
  have hi := SignedMeasure.measurable_rnDeriv (M.entry i j).im M.traceMeasure
  have heq : (fun z => M.density z i j) = fun z =>
      ((M.entry i j).re.rnDeriv M.traceMeasure z : ℂ) +
        ((M.entry i j).im.rnDeriv M.traceMeasure z : ℂ) * Complex.I := by
    funext z
    exact (Complex.re_add_im (M.density z i j)).symm
  change Measurable (fun z => M.density z i j)
  rw [heq]
  exact (Complex.measurable_ofReal.comp hr).add
    ((Complex.measurable_ofReal.comp hi).mul_const _)

/-- The full operator-valued measure is recovered on every measurable set. -/
theorem setIntegral_density (M : OperatorPOVM D Outcome) (s : Set Outcome)
    (hs : MeasurableSet s) (i j : Fin D) :
    (∫ z in s, M.density z i j ∂M.traceMeasure) = M.entry i j s := by
  have hac := (ComplexMeasure.absolutelyContinuous_ennreal_iff _ _).mp
    (M.entry_absolutelyContinuous i j)
  have hr := congrArg (fun v : SignedMeasure Outcome => v s)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac.1)
  have hi := congrArg (fun v : SignedMeasure Outcome => v s)
    (SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hac.2)
  rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at hr hi
  apply Complex.ext
  · exact (Complex.reCLM.integral_comp_comm (M.density_integrable i j).integrableOn).symm.trans hr
  · exact (Complex.imCLM.integral_comp_comm (M.density_integrable i j).integrableOn).symm.trans hi


/-- Almost-everywhere Hermitian symmetry follows from equality of the
operator-valued measures, using uniqueness of integrable densities. -/
theorem density_ae_isHermitian (M : OperatorPOVM D Outcome) :
    ∀ᵐ z ∂M.traceMeasure, (M.density z).IsHermitian := by
  have hij (i j : Fin D) :
      (fun z => star (M.density z j i)) =ᵐ[M.traceMeasure] (fun z => M.density z i j) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _
      (Complex.conjCLE.toContinuousLinearMap.integrable_comp (M.density_integrable j i)) (M.density_integrable i j)
    intro s hs _
    change (∫ z in s, (starRingEnd ℂ) (M.density z j i) ∂M.traceMeasure) = _
    rw [integral_conj, M.setIntegral_density s hs, M.setIntegral_density s hs]
    exact (M.positive s hs).isHermitian.apply i j
  have ha : ∀ᵐ z ∂M.traceMeasure, ∀ i j, star (M.density z j i) = M.density z i j :=
    ae_all_iff.mpr fun i => ae_all_iff.mpr fun j => hij i j
  filter_upwards [ha] with z hz
  exact Matrix.IsHermitian.ext_iff.mpr hz

def quadratic (A : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ) : ℂ :=
  ∑ i : Fin D, ∑ j : Fin D, star (v i) * A i j * v j

theorem quadratic_eq (A : Matrix (Fin D) (Fin D) ℂ) (v : Fin D → ℂ) :
    quadratic A v = star v ⬝ᵥ A.mulVec v := by
  simp [quadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem integrable_quadratic (M : OperatorPOVM D Outcome) (v : Fin D → ℂ) :
    Integrable (fun z => quadratic (M.density z) v) M.traceMeasure := by
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((M.density_integrable i j).const_mul (star (v i))).mul_const (v j)

theorem setIntegral_quadratic (M : OperatorPOVM D Outcome) (v : Fin D → ℂ)
    (s : Set Outcome) (hs : MeasurableSet s) :
    (∫ z in s, quadratic (M.density z) v ∂M.traceMeasure) = quadratic (M.apply s) v := by
  unfold quadratic
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (((M.density_integrable i j).const_mul (star (v i))).mul_const (v j)).integrableOn]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ =>
    (((M.density_integrable i j).const_mul (star (v i))).mul_const (v j)).integrableOn]
  simp only [integral_mul_const, integral_const_mul, M.setIntegral_density s hs]
  rfl

theorem quadratic_density_ae_nonnegative (M : OperatorPOVM D Outcome) (v : Fin D → ℂ) :
    ∀ᵐ z ∂M.traceMeasure, 0 ≤ (quadratic (M.density z) v).re := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (M.integrable_quadratic v).re
  intro s hs _
  rw [integral_re (M.integrable_quadratic v).integrableOn, M.setIntegral_quadratic v s hs]
  change 0 ≤ (quadratic (M.apply s) v).re
  rw [quadratic_eq]
  exact ((M.positive s hs).dotProduct_mulVec_nonneg v).1

/-- Positivity holds simultaneously for every vector: a countable dense set
is used before intersecting the almost-everywhere events. -/
theorem density_ae_posSemidef (M : OperatorPOVM D Outcome) :
    ∀ᵐ z ∂M.traceMeasure, (M.density z).PosSemidef := by
  obtain ⟨S, hScount, hSdense⟩ := TopologicalSpace.exists_countable_dense (Fin D → ℂ)
  let : Countable S := hScount.to_subtype
  have hS : ∀ᵐ z ∂M.traceMeasure, ∀ v : S, 0 ≤ (quadratic (M.density z) v).re :=
    ae_all_iff.mpr fun v => M.quadratic_density_ae_nonnegative v
  filter_upwards [M.density_ae_isHermitian, hS] with z hH hz
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH
  intro v
  apply Complex.nonneg_iff.mpr
  constructor
  · have hc : Continuous (fun v : Fin D → ℂ => (quadratic (M.density z) v).re) := by
      unfold quadratic
      fun_prop
    have h := le_on_closure (fun w hw => hz ⟨w, hw⟩) continuous_const.continuousOn
      hc.continuousOn (hSdense v)
    simpa only [quadratic_eq] using h
  · exact (hH.im_star_dotProduct_mulVec_self v).symm

theorem integrable_trace_density (M : OperatorPOVM D Outcome) :
    Integrable (fun z => (M.density z).trace) M.traceMeasure :=
  integrable_finsetSum _ fun i _ => M.density_integrable i i

/-- The trace-measure choice makes the derivative have trace one a.e. -/
theorem density_ae_trace_one (M : OperatorPOVM D Outcome) :
    ∀ᵐ z ∂M.traceMeasure, (M.density z).trace = 1 := by
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ M.integrable_trace_density (integrable_const 1)
  intro s hs _
  have htrace : (∫ z in s, (M.density z).trace ∂M.traceMeasure) = (M.apply s).trace := by
    change (∫ z in s, ∑ i : Fin D, M.density z i i ∂M.traceMeasure) =
      ∑ i : Fin D, M.entry i i s
    rw [integral_finsetSum _ fun i _ => (M.density_integrable i i).integrableOn]
    simp only [M.setIntegral_density s hs]
  rw [htrace, setIntegral_const]
  have hr := M.traceMeasure_real s hs
  apply Complex.ext
  · simpa [smul_eq_mul, measureReal_def] using hr.symm
  · have hi : (M.apply s).trace.im = 0 := (M.positive s hs).trace_nonneg.2.symm
    simp [hi]

/-- Normalization of the derivative is derived from the original POVM. -/
theorem integral_density (M : OperatorPOVM D Outcome) (i j : Fin D) :
    (∫ z, M.density z i j ∂M.traceMeasure) = if i = j then 1 else 0 := by
  have h := M.setIntegral_density Set.univ MeasurableSet.univ i j
  rw [Measure.restrict_univ] at h
  exact h.trans (congrFun (congrFun M.normalized i) j)


open MatrixReduction in
theorem integrable_bornTrace (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D)) :
    Integrable (fun z => (rho.matrix * M.density z).trace) M.traceMeasure := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (M.density_integrable j i).const_mul (rho.matrix i j)

open MatrixReduction in
theorem setIntegral_bornTrace (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D))
    (s : Set Outcome) (hs : MeasurableSet s) :
    (∫ z in s, (rho.matrix * M.density z).trace ∂M.traceMeasure) =
      (rho.matrix * M.apply s).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    ((M.density_integrable j i).const_mul (rho.matrix i j)).integrableOn]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ fun j _ =>
    ((M.density_integrable j i).const_mul (rho.matrix i j)).integrableOn]
  simp only [integral_const_mul, M.setIntegral_density s hs]
  rfl

open MatrixReduction in
theorem bornTrace_ae_nonnegative (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D)) :
    ∀ᵐ z ∂M.traceMeasure, 0 ≤ (rho.matrix * M.density z).trace.re := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp M.dimension_pos
  filter_upwards [M.density_ae_posSemidef] with z hz
  exact trace_mul_re_nonnegative_of_posSemidef _ _ rho.posSemidef hz

open MatrixReduction in
theorem bornMeasureFrom_apply (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D))
    (s : Set Outcome) (hs : MeasurableSet s) :
    bornMeasureFrom M.traceMeasure M.density rho s =
      ENNReal.ofReal (rho.matrix * M.apply s).trace.re := by
  rw [bornMeasureFrom, withDensity_apply _ hs]
  unfold bornDensityFrom
  have hreal : (∫ z in s, (rho.matrix * M.density z).trace.re ∂M.traceMeasure) =
      (rho.matrix * M.apply s).trace.re := by
    exact (Complex.reCLM.integral_comp_comm (M.integrable_bornTrace rho).integrableOn).trans
      (congrArg Complex.re (M.setIntegral_bornTrace rho s hs))
  calc
    _ = ENNReal.ofReal (∫ z in s, (rho.matrix * M.density z).trace.re ∂M.traceMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal (M.integrable_bornTrace rho).re.integrableOn
        (ae_restrict_of_ae (M.bornTrace_ae_nonnegative rho))).symm
    _ = _ := congrArg ENNReal.ofReal hreal

open MatrixReduction in
theorem bornMeasureFrom_probability (M : OperatorPOVM D Outcome) (rho : DensityOperator (Fin D)) :
    IsProbabilityMeasure (bornMeasureFrom M.traceMeasure M.density rho) := by
  constructor
  rw [M.bornMeasureFrom_apply rho Set.univ MeasurableSet.univ]
  have hn : M.apply Set.univ = 1 := M.normalized
  rw [hn, Matrix.mul_one, rho.trace_eq_one]
  norm_num

open MatrixReduction in
theorem bornMeasureFrom_measurable (M : OperatorPOVM D Outcome) :
    Measurable (bornMeasureFrom M.traceMeasure M.density) := by
  apply measurable_withDensity
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ fun i _ =>
    Finset.measurable_sum Finset.univ fun j _ =>
      ((measurable_densityOperator_apply D i j).comp measurable_fst).mul
        ((M.density_measurable j i).comp measurable_snd)

/-- Every countably additive finite-dimensional POVM has the normalized
effect-density representation used by the original information proofs. -/
def toDominated [StandardBorelSpace Outcome] (M : OperatorPOVM D Outcome) :
    DominatedPOVM D Outcome where
  dimension_pos := M.dimension_pos
  base := M.traceMeasure
  base_finite := M.traceMeasure_finite
  effect := M.density
  effect_measurable := M.density_measurable
  effect_integrable := M.density_integrable
  effect_ae_posSemidef := M.density_ae_posSemidef
  effect_ae_trace_one := M.density_ae_trace_one
  integral_effect_eq_one := M.integral_density
  born_density_ae_nonnegative := M.bornTrace_ae_nonnegative
  born_measurable := M.bornMeasureFrom_measurable
  born_probability := M.bornMeasureFrom_probability

/-- Born probabilities of the representation are exactly the operator-valued
Born rule on every measurable set. -/
theorem toDominated_bornMeasure_apply [StandardBorelSpace Outcome]
    (M : OperatorPOVM D Outcome) (rho : MatrixReduction.DensityOperator (Fin D))
    (s : Set Outcome) (hs : MeasurableSet s) :
    M.toDominated.bornMeasure rho s = ENNReal.ofReal (rho.matrix * M.apply s).trace.re :=
  M.bornMeasureFrom_apply rho s hs

end OperatorPOVM
end
end TomographyOracleCore.PhysicalPOVM
