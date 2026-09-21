import TomographyOracleCore.PhysicalConstantMatrixPOVMDesign

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ComplexOrder MatrixOrder ENNReal

noncomputable section

/-!
# Finite unitary projective POVMs

For a finite nonempty ensemble of unitary matrices, this module constructs
the literal law obtained by choosing an ensemble element and a computational
basis vector uniformly and returning the corresponding conjugated rank-one
projector.  Multiplying that probability law by the Hilbert-space dimension
gives the trace-dominating measure of a genuine matrix-valued POVM.
-/

section Projectors

variable {D : ℕ}

/-- The rank-one projector onto the `b`th computational basis vector. -/
def finiteComputationalBasisProjector (b : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  Matrix.single b b 1

/-- The measurement effect obtained by measuring in the basis selected by
`U`: `U† |b><b| U`. -/
def finiteUnitaryMeasurementProjector
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    Matrix (Fin D) (Fin D) ℂ :=
  U.1.conjTranspose * finiteComputationalBasisProjector b * U.1

theorem finiteComputationalBasisProjector_posSemidef (b : Fin D) :
    (finiteComputationalBasisProjector b).PosSemidef := by
  rw [show finiteComputationalBasisProjector b =
      Matrix.diagonal (Pi.single b (1 : ℂ)) by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hib : i = b
      · subst i
        simp [finiteComputationalBasisProjector, Matrix.single_apply,
          Matrix.diagonal_apply, Pi.single_apply]
      · simp [finiteComputationalBasisProjector, Matrix.single_apply,
          Matrix.diagonal_apply, Pi.single_apply, hib, Ne.symm hib]
    · by_cases hbi : b = i
      · subst b
        simp [finiteComputationalBasisProjector, Matrix.single_apply,
          Matrix.diagonal_apply, Pi.single_apply, hij]
      · simp [finiteComputationalBasisProjector, Matrix.single_apply,
          Matrix.diagonal_apply, Pi.single_apply, hij, hbi]]
  apply Matrix.PosSemidef.diagonal
  intro i
  by_cases hib : i = b
  · subst i
    simp
  · simp [Pi.single_apply, hib]

@[simp]
theorem finiteComputationalBasisProjector_trace (b : Fin D) :
    (finiteComputationalBasisProjector b).trace = 1 := by
  simp [finiteComputationalBasisProjector, Matrix.trace,
    Matrix.single_apply]

theorem sum_finiteComputationalBasisProjector :
    (∑ b : Fin D, finiteComputationalBasisProjector b) = 1 := by
  classical
  ext i j
  rw [Matrix.sum_apply (β := Fin D) i j Finset.univ
    (fun b : Fin D ↦ finiteComputationalBasisProjector b)]
  by_cases hij : i = j
  · subst j
    simp [finiteComputationalBasisProjector, Matrix.single_apply,
      Matrix.one_apply]
  · simp [finiteComputationalBasisProjector, Matrix.single_apply,
      Matrix.one_apply, hij]

theorem finiteUnitaryMeasurementProjector_posSemidef
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    (finiteUnitaryMeasurementProjector U b).PosSemidef := by
  unfold finiteUnitaryMeasurementProjector
  have h := (finiteComputationalBasisProjector_posSemidef b).mul_mul_conjTranspose_same
    U.1.conjTranspose
  simpa using h

@[simp]
theorem finiteUnitaryMeasurementProjector_trace
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    (finiteUnitaryMeasurementProjector U b).trace = 1 := by
  unfold finiteUnitaryMeasurementProjector
  rw [Matrix.trace_mul_cycle]
  have hU : U.1 * U.1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.2)
  rw [hU, one_mul, finiteComputationalBasisProjector_trace]

theorem sum_finiteUnitaryMeasurementProjector
    (U : Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ b : Fin D, finiteUnitaryMeasurementProjector U b) = 1 := by
  classical
  unfold finiteUnitaryMeasurementProjector
  rw [← Finset.sum_mul, ← Matrix.mul_sum,
    sum_finiteComputationalBasisProjector]
  simpa [Matrix.star_eq_conjTranspose] using
    (Matrix.mem_unitaryGroup_iff'.mp U.2)

end Projectors

section FiniteLaw

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- Uniform probability law of the projector obtained by independently
choosing `e : E` and `b : Fin D` uniformly. -/
noncomputable def finiteUnitaryProjectorLaw
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    Measure (Matrix (Fin D) (Fin D) ℂ) :=
  ((Fintype.card E * D : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ e : E, ∑ b : Fin D,
      Measure.dirac (finiteUnitaryMeasurementProjector (U e) b)

/-- Dimension-scaled projector law used as the POVM's dominating measure.
Equivalently, every pair `(e,b)` has base mass `1 / |E|`. -/
noncomputable def finiteUnitaryProjectivePOVMBase
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    Measure (Matrix (Fin D) (Fin D) ℂ) :=
  ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ e : E, ∑ b : Fin D,
      Measure.dirac (finiteUnitaryMeasurementProjector (U e) b)

/-- The effect density is the sampled matrix itself. -/
def finiteUnitaryProjectivePOVMEffect
    (B : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ :=
  B

theorem finiteUnitaryProjectorLaw_apply_univ
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (hD : 0 < D) :
    finiteUnitaryProjectorLaw U Set.univ = 1 := by
  have hE : Fintype.card E ≠ 0 := Fintype.card_ne_zero
  have hED : Fintype.card E * D ≠ 0 := Nat.mul_ne_zero hE hD.ne'
  simp [finiteUnitaryProjectorLaw, Measure.smul_apply]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast hED
  · exact ENNReal.mul_ne_top (by simp) (by simp)

theorem finiteUnitaryProjectorLaw_isProbability
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (hD : 0 < D) :
    IsProbabilityMeasure (finiteUnitaryProjectorLaw U) := by
  constructor
  exact finiteUnitaryProjectorLaw_apply_univ U hD

theorem finiteUnitaryProjectivePOVMBase_apply_univ
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryProjectivePOVMBase U Set.univ = D := by
  have hE : Fintype.card E ≠ 0 := Fintype.card_ne_zero
  simp [finiteUnitaryProjectivePOVMBase, Measure.smul_apply]
  apply ENNReal.inv_mul_cancel_left
  · exact_mod_cast hE
  · simp

theorem finiteUnitaryProjectivePOVMBase_finite
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    IsFiniteMeasure (finiteUnitaryProjectivePOVMBase U) := by
  constructor
  rw [finiteUnitaryProjectivePOVMBase_apply_univ U]
  exact ENNReal.coe_lt_top

theorem finiteUnitaryProjectivePOVMEffect_measurable
    (i j : Fin D) :
    Measurable fun B : Matrix (Fin D) (Fin D) ℂ ↦
      finiteUnitaryProjectivePOVMEffect B i j := by
  exact measurable_complexMatrix_apply (Fin D) i j

theorem finiteUnitaryProjectivePOVMEffect_integrable
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (i j : Fin D) :
    Integrable
      (fun B : Matrix (Fin D) (Fin D) ℂ ↦
        finiteUnitaryProjectivePOVMEffect B i j)
      (finiteUnitaryProjectivePOVMBase U) := by
  unfold finiteUnitaryProjectivePOVMBase
  apply Integrable.smul_measure
  · refine (integrable_finsetSum_measure).2 ?_
    intro e he
    refine (integrable_finsetSum_measure).2 ?_
    intro b hb
    exact integrable_dirac (f := fun B : Matrix (Fin D) (Fin D) ℂ ↦
      finiteUnitaryProjectivePOVMEffect B i j) (by simp)
  · simp

/-- Integration against the finite POVM base is the literal finite average
over the ensemble element and computational-basis outcome. -/
theorem integral_finiteUnitaryProjectivePOVMBase_eq_sum
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (f : Matrix (Fin D) (Fin D) ℂ → ℂ) :
    (∫ B, f B ∂finiteUnitaryProjectivePOVMBase U) =
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
        ∑ e : E, ∑ b : Fin D,
          f (finiteUnitaryMeasurementProjector (U e) b) := by
  have hb (e : E) : ∀ b ∈ (Finset.univ : Finset (Fin D)),
      Integrable f
        (Measure.dirac (finiteUnitaryMeasurementProjector (U e) b)) := by
    intro b hb
    exact integrable_dirac (f := f) (by simp)
  have he : ∀ e ∈ (Finset.univ : Finset E),
      Integrable f
        (∑ b : Fin D,
          Measure.dirac (finiteUnitaryMeasurementProjector (U e) b)) := by
    intro e he
    exact (integrable_finsetSum_measure).2 (hb e)
  unfold finiteUnitaryProjectivePOVMBase
  rw [integral_smul_measure]
  congr 1
  rw [integral_finsetSum_measure he]
  apply Finset.sum_congr rfl
  intro e he'
  rw [integral_finsetSum_measure (hb e)]
  simp

/-- Real-valued integration against the finite POVM base is the same literal
finite average. -/
theorem integral_finiteUnitaryProjectivePOVMBase_real_eq_sum
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (f : Matrix (Fin D) (Fin D) ℂ → ℝ) :
    (∫ B, f B ∂finiteUnitaryProjectivePOVMBase U) =
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
        ∑ e : E, ∑ b : Fin D,
          f (finiteUnitaryMeasurementProjector (U e) b) := by
  have hb (e : E) : ∀ b ∈ (Finset.univ : Finset (Fin D)),
      Integrable f
        (Measure.dirac (finiteUnitaryMeasurementProjector (U e) b)) := by
    intro b hb
    exact integrable_dirac (f := f) (by simp)
  have he : ∀ e ∈ (Finset.univ : Finset E),
      Integrable f
        (∑ b : Fin D,
          Measure.dirac (finiteUnitaryMeasurementProjector (U e) b)) := by
    intro e he
    exact (integrable_finsetSum_measure).2 (hb e)
  unfold finiteUnitaryProjectivePOVMBase
  rw [integral_smul_measure]
  congr 1
  rw [integral_finsetSum_measure he]
  apply Finset.sum_congr rfl
  intro e he'
  rw [integral_finsetSum_measure (hb e)]
  simp

/-- The sum of all projectors in all measurement bases is `|E| I`. -/
theorem sum_finiteUnitaryMeasurementProjector_ensemble
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ e : E, ∑ b : Fin D,
      finiteUnitaryMeasurementProjector (U e) b) =
        (Fintype.card E : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  simp_rw [sum_finiteUnitaryMeasurementProjector]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply]
  · simp [Matrix.one_apply, hij]

/-- The base integral of the effect matrix resolves the identity entrywise. -/
theorem integral_finiteUnitaryProjectivePOVMEffect_coordinate
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (i j : Fin D) :
    (∫ B, finiteUnitaryProjectivePOVMEffect B i j
        ∂finiteUnitaryProjectivePOVMBase U) =
      if i = j then 1 else 0 := by
  rw [integral_finiteUnitaryProjectivePOVMBase_eq_sum]
  simp only [finiteUnitaryProjectivePOVMEffect]
  have htotal := congrFun (congrFun
    (sum_finiteUnitaryMeasurementProjector_ensemble U) i) j
  simp only [Matrix.sum_apply] at htotal
  rw [htotal]
  by_cases hij : i = j
  · subst j
    simp [Matrix.one_apply, Fintype.card_ne_zero]
  · simp [Matrix.one_apply, hij]

theorem integrable_finiteUnitaryProjectivePOVM_bornTrace
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    Integrable
      (fun B : Matrix (Fin D) (Fin D) ℂ ↦ (ρ.matrix * B).trace)
      (finiteUnitaryProjectivePOVMBase U) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  apply integrable_finsetSum Finset.univ
  intro i hi
  apply integrable_finsetSum Finset.univ
  intro j hj
  exact (finiteUnitaryProjectivePOVMEffect_integrable U j i).const_mul
    (ρ.matrix i j)

theorem integral_finiteUnitaryProjectivePOVM_bornTrace_eq_one
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    (∫ B, (ρ.matrix * B).trace
        ∂finiteUnitaryProjectivePOVMBase U) = 1 := by
  have hcoordinate (i j : Fin D) :
      (∫ B, B i j ∂finiteUnitaryProjectivePOVMBase U) =
        if i = j then 1 else 0 := by
    simpa only [finiteUnitaryProjectivePOVMEffect] using
      integral_finiteUnitaryProjectivePOVMEffect_coordinate U i j
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  calc
    (∫ B, ∑ i, ∑ j, ρ.matrix i j * B j i
        ∂finiteUnitaryProjectivePOVMBase U) =
        ∑ i, ∫ B, ∑ j, ρ.matrix i j * B j i
          ∂finiteUnitaryProjectivePOVMBase U := by
      rw [integral_finsetSum]
      intro i hi
      apply integrable_finsetSum Finset.univ
      intro j hj
      exact (finiteUnitaryProjectivePOVMEffect_integrable U j i).const_mul
        (ρ.matrix i j)
    _ = ∑ i, ∑ j, ∫ B, ρ.matrix i j * B j i
          ∂finiteUnitaryProjectivePOVMBase U := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      intro j hj
      exact (finiteUnitaryProjectivePOVMEffect_integrable U j i).const_mul
        (ρ.matrix i j)
    _ = 1 := by
      simp_rw [integral_const_mul, hcoordinate]
      simpa [Matrix.trace, eq_comm] using ρ.trace_eq_one

theorem integrable_finiteUnitaryProjectivePOVM_bornTrace_re
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    Integrable
      (fun B : Matrix (Fin D) (Fin D) ℂ ↦ (ρ.matrix * B).trace.re)
      (finiteUnitaryProjectivePOVMBase U) :=
  (integrable_finiteUnitaryProjectivePOVM_bornTrace U ρ).re

theorem integral_finiteUnitaryProjectivePOVM_bornTrace_re_eq_one
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    (∫ B, (ρ.matrix * B).trace.re
        ∂finiteUnitaryProjectivePOVMBase U) = 1 := by
  have h := integral_re
    (integrable_finiteUnitaryProjectivePOVM_bornTrace U ρ)
  rw [integral_finiteUnitaryProjectivePOVM_bornTrace_eq_one U ρ] at h
  simpa only [RCLike.re_eq_complex_re, Complex.one_re] using h

theorem finiteUnitaryProjectivePOVM_ae_posSemidef
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ᵐ B ∂finiteUnitaryProjectivePOVMBase U,
      (finiteUnitaryProjectivePOVMEffect B).PosSemidef := by
  have hc : ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 := by
    simp [Fintype.card_ne_zero]
  unfold finiteUnitaryProjectivePOVMBase
  apply (Measure.ae_ennreal_smul_measure_iff (c :=
    ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹) hc).2
  simp only [ae_finsetSum_measure_iff, Finset.mem_univ,
    forall_const]
  intro e b
  simpa [finiteUnitaryProjectivePOVMEffect] using
    finiteUnitaryMeasurementProjector_posSemidef (U e) b

theorem finiteUnitaryProjectivePOVM_ae_trace_one
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    ∀ᵐ B ∂finiteUnitaryProjectivePOVMBase U,
      Matrix.trace (finiteUnitaryProjectivePOVMEffect B) = 1 := by
  have hc : ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹ ≠ 0 := by
    simp [Fintype.card_ne_zero]
  unfold finiteUnitaryProjectivePOVMBase
  apply (Measure.ae_ennreal_smul_measure_iff (c :=
    ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹) hc).2
  simp only [ae_finsetSum_measure_iff, Finset.mem_univ,
    forall_const]
  intro e b
  simpa [finiteUnitaryProjectivePOVMEffect] using
    finiteUnitaryMeasurementProjector_trace (U e) b

/-- The joint Born density is measurable in the density operator and the
matrix outcome. -/
theorem measurable_finiteUnitaryProjectivePOVM_bornDensity_uncurry :
    Measurable
      (Function.uncurry
        (bornDensityFrom
          (finiteUnitaryProjectivePOVMEffect (D := D)))) := by
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Function.uncurry_apply_pair, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, finiteUnitaryProjectivePOVMEffect]
  exact Finset.measurable_sum Finset.univ (fun i _ ↦
    Finset.measurable_sum Finset.univ (fun j _ ↦
      ((measurable_densityOperator_apply D i j).comp measurable_fst).mul
        ((measurable_complexMatrix_apply (Fin D) j i).comp measurable_snd)))

theorem measurable_finiteUnitaryProjectivePOVM_bornMeasure
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    Measurable
      (bornMeasureFrom
        (finiteUnitaryProjectivePOVMBase U)
        (finiteUnitaryProjectivePOVMEffect (D := D))) := by
  unfold bornMeasureFrom
  letI : IsFiniteMeasure (finiteUnitaryProjectivePOVMBase U) :=
    finiteUnitaryProjectivePOVMBase_finite U
  exact measurable_withDensity
    (measurable_finiteUnitaryProjectivePOVM_bornDensity_uncurry (D := D))

theorem finiteUnitaryProjectivePOVM_bornDensity_ae_nonnegative
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    ∀ᵐ B ∂finiteUnitaryProjectivePOVMBase U,
      0 ≤ (ρ.matrix * finiteUnitaryProjectivePOVMEffect B).trace.re := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  filter_upwards [finiteUnitaryProjectivePOVM_ae_posSemidef U] with B hB
  exact trace_mul_re_nonnegative_of_posSemidef ρ.matrix B ρ.posSemidef hB

theorem finiteUnitaryProjectivePOVM_born_probability
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    IsProbabilityMeasure
      (bornMeasureFrom
        (finiteUnitaryProjectivePOVMBase U)
        (finiteUnitaryProjectivePOVMEffect (D := D)) ρ) := by
  constructor
  rw [bornMeasureFrom, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  unfold bornDensityFrom finiteUnitaryProjectivePOVMEffect
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_finiteUnitaryProjectivePOVM_bornTrace_re U ρ)
    (finiteUnitaryProjectivePOVM_bornDensity_ae_nonnegative hD U ρ)]
  rw [integral_finiteUnitaryProjectivePOVM_bornTrace_re_eq_one U ρ]
  norm_num

/-- The unconditional physical POVM obtained by uniformly choosing a finite
unitary and a computational-basis outcome. -/
noncomputable def finiteUnitaryProjectivePOVM
    (D : ℕ) (hD : 0 < D)
    {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    DominatedPOVM D (Matrix (Fin D) (Fin D) ℂ) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  refine
    { dimension_pos := hD
      base := finiteUnitaryProjectivePOVMBase U
      base_finite := finiteUnitaryProjectivePOVMBase_finite U
      effect := finiteUnitaryProjectivePOVMEffect (D := D)
      effect_measurable := finiteUnitaryProjectivePOVMEffect_measurable
      effect_integrable := finiteUnitaryProjectivePOVMEffect_integrable U
      effect_ae_posSemidef := finiteUnitaryProjectivePOVM_ae_posSemidef U
      effect_ae_trace_one := finiteUnitaryProjectivePOVM_ae_trace_one U
      integral_effect_eq_one :=
        integral_finiteUnitaryProjectivePOVMEffect_coordinate U
      born_density_ae_nonnegative :=
        finiteUnitaryProjectivePOVM_bornDensity_ae_nonnegative hD U
      born_measurable := measurable_finiteUnitaryProjectivePOVM_bornMeasure U
      born_probability := finiteUnitaryProjectivePOVM_born_probability hD U }

theorem measurable_finiteUnitaryProjectivePOVM_bornDensity
    (ρ : DensityOperator (Fin D)) :
    Measurable
      (bornDensityFrom
        (finiteUnitaryProjectivePOVMEffect (D := D)) ρ) := by
  unfold bornDensityFrom finiteUnitaryProjectivePOVMEffect
  fun_prop

theorem finiteUnitaryProjectivePOVM_bornDensity_toReal_ae
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) :
    ∀ᵐ B ∂finiteUnitaryProjectivePOVMBase U,
      (bornDensityFrom
        (finiteUnitaryProjectivePOVMEffect (D := D)) ρ B).toReal =
          (ρ.matrix * B).trace.re := by
  filter_upwards
    [finiteUnitaryProjectivePOVM_bornDensity_ae_nonnegative hD U ρ]
      with B hB
  have hB' : 0 ≤ (ρ.matrix * B).trace.re := by
    simpa [finiteUnitaryProjectivePOVMEffect] using hB
  simp [bornDensityFrom, finiteUnitaryProjectivePOVMEffect,
    ENNReal.toReal_ofReal hB']

/-- Exact expectation formula for an arbitrary real-valued statistic under
the physical Born law. -/
theorem integral_finiteUnitaryProjectivePOVM_bornMeasure_real_eq_sum
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (g : Matrix (Fin D) (Fin D) ℂ → ℝ) :
    (∫ B, g B ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
        ∑ e : E, ∑ b : Fin D,
          g (finiteUnitaryMeasurementProjector (U e) b) *
            (ρ.matrix *
              finiteUnitaryMeasurementProjector (U e) b).trace.re := by
  change
    (∫ B, g B ∂bornMeasureFrom
      (finiteUnitaryProjectivePOVMBase U)
      (finiteUnitaryProjectivePOVMEffect (D := D)) ρ) = _
  unfold bornMeasureFrom
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_finiteUnitaryProjectivePOVM_bornDensity ρ)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [integral_congr_ae]
  · exact integral_finiteUnitaryProjectivePOVMBase_real_eq_sum U
      (fun B ↦ g B * (ρ.matrix * B).trace.re)
  · filter_upwards
      [finiteUnitaryProjectivePOVM_bornDensity_toReal_ae hD U ρ]
        with B hB
    simp only [hB, smul_eq_mul]
    ring

/-- Exact expectation formula for an arbitrary complex-valued statistic
under the physical Born law. -/
theorem integral_finiteUnitaryProjectivePOVM_bornMeasure_complex_eq_sum
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (ρ : DensityOperator (Fin D))
    (g : Matrix (Fin D) (Fin D) ℂ → ℂ) :
    (∫ B, g B ∂(finiteUnitaryProjectivePOVM D hD U).bornMeasure ρ) =
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal •
        ∑ e : E, ∑ b : Fin D,
          (ρ.matrix *
            finiteUnitaryMeasurementProjector (U e) b).trace.re •
              g (finiteUnitaryMeasurementProjector (U e) b) := by
  change
    (∫ B, g B ∂bornMeasureFrom
      (finiteUnitaryProjectivePOVMBase U)
      (finiteUnitaryProjectivePOVMEffect (D := D)) ρ) = _
  unfold bornMeasureFrom
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_finiteUnitaryProjectivePOVM_bornDensity ρ)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [integral_congr_ae]
  · exact integral_finiteUnitaryProjectivePOVMBase_eq_sum U
      (fun B ↦ (ρ.matrix * B).trace.re • g B)
  · filter_upwards
      [finiteUnitaryProjectivePOVM_bornDensity_toReal_ae hD U ρ]
        with B hB
    simp only [hB]

end FiniteLaw

end

end TomographyOracleCore
