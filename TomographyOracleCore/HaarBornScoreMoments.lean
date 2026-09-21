import TomographyOracleCore.ProjectiveHaarPOVM
import TomographyOracleCore.ProjectiveHaarThirdTrace
import TomographyOracleCore.HaarChannel

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator ENNReal

noncomputable section

section TraceReality

variable {ι : Type*} [Fintype ι]

/-- The trace pairing of two Hermitian matrices is real. -/
theorem trace_mul_im_eq_zero_of_isHermitian
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    star ((A * B).trace) = (Matrix.conjTranspose (A * B)).trace :=
      (Matrix.trace_conjTranspose (A * B)).symm
    _ = (Matrix.conjTranspose B * Matrix.conjTranspose A).trace := by
      rw [Matrix.conjTranspose_mul]
    _ = (B * A).trace := by rw [hA.eq, hB.eq]
    _ = (A * B).trace := Matrix.trace_mul_comm B A

theorem trace_mul_eq_re_of_isHermitian
    (A B : Matrix ι ι ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace = ((A * B).trace.re : ℂ) := by
  apply Complex.ext
  · simp
  · simp [trace_mul_im_eq_zero_of_isHermitian A B hA hB]

end TraceReality

section TraceIntegrability

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem integrable_complexProjectiveHaar_trace_mul_one
    (A : Matrix ι ι ℂ) :
    Integrable (fun P : Matrix ι ι ℂ ↦ (A * P).trace)
      (complexProjectiveHaarLaw ι) := by
  have hg : Continuous (fun P : Matrix ι ι ℂ ↦ (A * P).trace) := by
    fun_prop
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  have hc := hg.comp (continuous_complexSphereProjector ι)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

theorem integrable_complexProjectiveHaar_trace_mul_two
    (A C : Matrix ι ι ℂ) :
    Integrable
      (fun P : Matrix ι ι ℂ ↦ (A * P).trace * (C * P).trace)
      (complexProjectiveHaarLaw ι) := by
  have hg : Continuous
      (fun P : Matrix ι ι ℂ ↦ (A * P).trace * (C * P).trace) := by
    fun_prop
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  have hc := hg.comp (continuous_complexSphereProjector ι)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

theorem integrable_complexProjectiveHaar_trace_mul_three
    (A C E : Matrix ι ι ℂ) :
    Integrable
      (fun P : Matrix ι ι ℂ ↦
        (A * P).trace * (C * P).trace * (E * P).trace)
      (complexProjectiveHaarLaw ι) := by
  have hg : Continuous
      (fun P : Matrix ι ι ℂ ↦
        (A * P).trace * (C * P).trace * (E * P).trace) := by
    fun_prop
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  have hc := hg.comp (continuous_complexSphereProjector ι)
  apply hc.integrable_of_hasCompactSupport
  exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)

end TraceIntegrability

section TwoTraceMoment

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem integral_complexProjectiveHaar_trace_mul_two_eq_trace_integral
    (A C : Matrix ι ι ℂ) :
    (∫ P, (A * P).trace * (C * P).trace
        ∂complexProjectiveHaarLaw ι) =
      (C * (∫ P, (A * P).trace • P
        ∂complexProjectiveHaarLaw ι)).trace := by
  have hmatrix := integrable_complexProjectiveHaar_trace_smul_matrix ι A
  have hterm (i j : ι) : Integrable
      (fun P : Matrix ι ι ℂ ↦ C i j * ((A * P).trace * P j i))
      (complexProjectiveHaarLaw ι) := by
    have hentry : Continuous
        (fun P : Matrix ι ι ℂ ↦ C i j * ((A * P).trace * P j i)) := by
      fun_prop
    unfold complexProjectiveHaarLaw
    apply (integrable_map_measure hentry.aestronglyMeasurable
      (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
    have hc := hentry.comp (continuous_complexSphereProjector ι)
    apply hc.integrable_of_hasCompactSupport
    exact isCompact_univ.of_isClosed_subset isClosed_closure
      (Set.subset_univ _)
  calc
    _ = ∫ P, ∑ i : ι, ∑ j : ι,
          C i j * ((A * P).trace * P j i)
          ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [] with P
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = ∑ i : ι, ∑ j : ι,
          ∫ P, C i j * ((A * P).trace * P j i)
            ∂complexProjectiveHaarLaw ι := by
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        rw [integral_finsetSum]
        intro j hj
        exact hterm i j
      · intro i hi
        apply integrable_finsetSum Finset.univ
        intro j hj
        exact hterm i j
    _ = ∑ i : ι, ∑ j : ι,
          C i j * (∫ P, ((A * P).trace * P j i)
            ∂complexProjectiveHaarLaw ι) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul]
    _ = _ := by
      change
        (∑ i : ι, ∑ j : ι,
          C i j * (∫ P, (A * P).trace * P j i
            ∂complexProjectiveHaarLaw ι)) =
        ∑ i : ι, ∑ j : ι,
          C i j * (∫ P, (A * P).trace • P
            ∂complexProjectiveHaarLaw ι) j i
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [integral_matrix_apply ι _ _ hmatrix j i]
      rfl

/-- The scalar two-trace contraction, with the dimension factor kept on the
left exactly as it occurs in the projective measurement. -/
theorem card_mul_integral_complexProjectiveHaar_trace_mul_two
    (A C : Matrix ι ι ℂ) :
    (Fintype.card ι : ℂ) *
        (∫ P, (A * P).trace * (C * P).trace
          ∂complexProjectiveHaarLaw ι) =
      ((A.trace * C.trace + (C * A).trace) /
        ((Fintype.card ι + 1 : ℕ) : ℂ)) := by
  rw [integral_complexProjectiveHaar_trace_mul_two_eq_trace_integral ι A C]
  have h := congrArg (fun M : Matrix ι ι ℂ ↦ (C * M).trace)
    (complexProjectiveHaarForward_eq_closedForm_unconditional A)
  unfold projectiveBasisForward at h
  simp [haarBasisForwardClosedForm, haarDimensionPlusOne,
    Matrix.mul_add, Matrix.trace_add, Matrix.trace_smul,
    smul_eq_mul, mul_assoc, mul_comm] at h
  rw [h]
  push_cast
  ring

end TwoTraceMoment

section BornIntegral

variable {D : ℕ} [Nonempty (Fin D)]

theorem measurable_projectiveHaarPOVM_bornDensity
    (ρ : DensityOperator (Fin D)) :
    Measurable (bornDensityFrom (projectiveHaarPOVMEffect (D := D)) ρ) := by
  unfold bornDensityFrom projectiveHaarPOVMEffect
  fun_prop

theorem projectiveHaarPOVM_bornDensity_toReal_ae
    (hD : 0 < D) (ρ : DensityOperator (Fin D)) :
    ∀ᵐ B ∂projectiveHaarPOVMBase (D := D),
      (bornDensityFrom (projectiveHaarPOVMEffect (D := D)) ρ B).toReal =
        (ρ.matrix * B).trace.re := by
  filter_upwards
    [projectiveHaarPOVM_bornDensity_ae_nonnegative (D := D) hD ρ]
      with B hB
  have hB' : 0 ≤ (ρ.matrix * B).trace.re := by
    simpa [projectiveHaarPOVMEffect] using hB
  simp [bornDensityFrom, projectiveHaarPOVMEffect,
    ENNReal.toReal_ofReal hB']

/-- Integration under the physical Born law is the dimension-scaled
projective Haar integral weighted by the real Born trace. -/
theorem integral_projectiveHaarPOVM_bornMeasure_eq_card_mul
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (g : Matrix (Fin D) (Fin D) ℂ → ℝ) :
    (∫ B, g B ∂(projectiveHaarPOVM D hD).bornMeasure ρ) =
      (D : ℝ) *
        ∫ B, g B * (ρ.matrix * B).trace.re
          ∂complexProjectiveHaarLaw (Fin D) := by
  change
    (∫ B, g B ∂bornMeasureFrom
      (projectiveHaarPOVMBase (D := D))
      (projectiveHaarPOVMEffect (D := D)) ρ) = _
  unfold bornMeasureFrom
  rw [integral_withDensity_eq_integral_toReal_smul
    (measurable_projectiveHaarPOVM_bornDensity (D := D) ρ)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  rw [integral_congr_ae]
  · unfold projectiveHaarPOVMBase
    rw [integral_smul_measure]
    simp only [ENNReal.toReal_natCast, smul_eq_mul]
    ring
  · filter_upwards
      [projectiveHaarPOVM_bornDensity_toReal_ae (D := D) hD ρ]
        with B hB
    simp only [hB, smul_eq_mul]
    ring

end BornIntegral

section RealTraceMoments

variable (ι : Type*) [Fintype ι] [Nonempty ι] [DecidableEq ι]

theorem integral_complexProjectiveHaar_trace_mul_two_re
    (A C : Matrix ι ι ℂ) (hA : A.IsHermitian) (hC : C.IsHermitian) :
    (∫ P, (A * P).trace.re * (C * P).trace.re
        ∂complexProjectiveHaarLaw ι) =
      (∫ P, (A * P).trace * (C * P).trace
        ∂complexProjectiveHaarLaw ι).re := by
  calc
    _ = ∫ P, ((A * P).trace * (C * P).trace).re
          ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [complexProjectiveHaar_ae_posSemidef ι] with P hP
      rw [trace_mul_eq_re_of_isHermitian A P hA hP.isHermitian,
        trace_mul_eq_re_of_isHermitian C P hC hP.isHermitian]
      simp
    _ = _ := integral_re
      (integrable_complexProjectiveHaar_trace_mul_two ι A C)

theorem card_mul_integral_complexProjectiveHaar_trace_mul_two_re_trace_one
    (A C : Matrix ι ι ℂ) (hA : A.IsHermitian) (hC : C.IsHermitian)
    (hAtrace : A.trace = 1) (hCtrace : C.trace = 1) :
    (Fintype.card ι : ℝ) *
        (∫ P, (A * P).trace.re * (C * P).trace.re
          ∂complexProjectiveHaarLaw ι) =
      (1 + (C * A).trace.re) / (Fintype.card ι + 1) := by
  rw [integral_complexProjectiveHaar_trace_mul_two_re ι A C hA hC]
  have h := congrArg Complex.re
    (card_mul_integral_complexProjectiveHaar_trace_mul_two ι A C)
  simp [hAtrace, hCtrace] at h
  rw [h]
  rw [Complex.div_re]
  simp [Complex.normSq_apply]
  field_simp

theorem integral_complexProjectiveHaar_trace_mul_three_re
    (A C E : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hE : E.IsHermitian) :
    (∫ P, (A * P).trace.re * (C * P).trace.re * (E * P).trace.re
        ∂complexProjectiveHaarLaw ι) =
      (∫ P, (A * P).trace * (C * P).trace * (E * P).trace
        ∂complexProjectiveHaarLaw ι).re := by
  calc
    _ = ∫ P, ((A * P).trace * (C * P).trace * (E * P).trace).re
          ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [complexProjectiveHaar_ae_posSemidef ι] with P hP
      rw [trace_mul_eq_re_of_isHermitian A P hA hP.isHermitian,
        trace_mul_eq_re_of_isHermitian C P hC hP.isHermitian,
        trace_mul_eq_re_of_isHermitian E P hE hP.isHermitian]
      simp
    _ = _ := integral_re
      (integrable_complexProjectiveHaar_trace_mul_three ι A C E)

theorem integrable_complexProjectiveHaar_trace_mul_three_re
    (A C E : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hC : C.IsHermitian) (hE : E.IsHermitian) :
    Integrable
      (fun P : Matrix ι ι ℂ ↦
        (A * P).trace.re * (C * P).trace.re * (E * P).trace.re)
      (complexProjectiveHaarLaw ι) := by
  apply (integrable_complexProjectiveHaar_trace_mul_three ι A C E).re.congr
  filter_upwards [complexProjectiveHaar_ae_posSemidef ι] with P hP
  rw [trace_mul_eq_re_of_isHermitian A P hA hP.isHermitian,
    trace_mul_eq_re_of_isHermitian C P hC hP.isHermitian,
    trace_mul_eq_re_of_isHermitian E P hE hP.isHermitian]
  simp

/-- The exact Born-weighted overlap-square moment before calibration. -/
theorem card_mul_integral_complexProjectiveHaar_trace_mul_rankOne_sq_re
    (A O : Matrix ι ι ℂ) (hA : A.IsHermitian) (hO : O.IsHermitian)
    (hAtrace : A.trace = 1) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    (Fintype.card ι : ℝ) *
        (∫ P, (A * P).trace.re * (O * P).trace.re * (O * P).trace.re
          ∂complexProjectiveHaarLaw ι) =
      (2 + 4 * (A * O).trace.re) /
        ((Fintype.card ι + 1) * (Fintype.card ι + 2)) := by
  rw [integral_complexProjectiveHaar_trace_mul_three_re
    ι A O O hA hO hO]
  have h := congrArg Complex.re
    (integral_complexProjectiveHaar_trace_mul_rankOne_sq
      A O hAtrace hOtrace hOidempotent)
  rw [h]
  have hAOim : (A * O).trace.im = 0 :=
    trace_mul_im_eq_zero_of_isHermitian A O hA hO
  unfold complexProjectiveThirdMomentDenominator
  simp [Complex.mul_re, Complex.inv_re, Complex.normSq_apply, hAOim]
  field_simp

end RealTraceMoments

section BornOverlapMoments

variable {D : ℕ}

/-- Exact first overlap moment under the actual Born-biased projective Haar
POVM law. -/
theorem integral_projectiveHaarPOVM_born_overlap
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ)
    (hO : O.IsHermitian) (hOtrace : O.trace = 1) :
    (∫ B, (O * B).trace.re
        ∂(projectiveHaarPOVM D hD).bornMeasure ρ) =
      (1 + (ρ.matrix * O).trace.re) / (D + 1) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  rw [integral_projectiveHaarPOVM_bornMeasure_eq_card_mul hD ρ]
  have hmoment :=
    card_mul_integral_complexProjectiveHaar_trace_mul_two_re_trace_one
      (Fin D) ρ.matrix O ρ.isHermitian hO ρ.trace_eq_one hOtrace
  rw [Matrix.trace_mul_comm O ρ.matrix] at hmoment
  simpa [Fintype.card_fin, mul_comm] using hmoment

/-- Exact second overlap moment under the actual Born-biased projective Haar
POVM law. -/
theorem integral_projectiveHaarPOVM_born_overlap_sq
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ)
    (hO : O.IsHermitian) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    (∫ B, ((O * B).trace.re) ^ 2
        ∂(projectiveHaarPOVM D hD).bornMeasure ρ) =
      (2 + 4 * (ρ.matrix * O).trace.re) /
        ((D + 1) * (D + 2)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  rw [integral_projectiveHaarPOVM_bornMeasure_eq_card_mul hD ρ]
  have hmoment :=
    card_mul_integral_complexProjectiveHaar_trace_mul_rankOne_sq_re
      (Fin D) ρ.matrix O ρ.isHermitian hO ρ.trace_eq_one hOtrace
        hOidempotent
  simpa [Fintype.card_fin, pow_two, mul_assoc, mul_comm, mul_left_comm]
    using hmoment

set_option maxHeartbeats 1200000 in
/-- Square integrability of the overlap under the concrete Born law. -/
theorem integrable_projectiveHaarPOVM_born_overlap_sq
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ) (hO : O.IsHermitian) :
    Integrable (fun B ↦ ((O * B).trace.re) ^ 2)
      ((projectiveHaarPOVM D hD).bornMeasure ρ) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  change Integrable (fun B ↦ ((O * B).trace.re) ^ 2)
    (bornMeasureFrom (projectiveHaarPOVMBase (D := D))
      (projectiveHaarPOVMEffect (D := D)) ρ)
  unfold bornMeasureFrom
  apply (integrable_withDensity_iff
    (measurable_projectiveHaarPOVM_bornDensity (D := D) ρ)
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
  apply Integrable.congr
    ((integrable_complexProjectiveHaar_trace_mul_three_re
      (Fin D) ρ.matrix O O ρ.isHermitian hO hO).smul_measure (by simp))
  filter_upwards
    [projectiveHaarPOVM_bornDensity_toReal_ae (D := D) hD ρ]
      with B hB
  simp only [hB]
  ring

theorem memLp_projectiveHaarPOVM_born_overlap_two
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ) (hO : O.IsHermitian) :
    MemLp (fun B ↦ (O * B).trace.re) 2
      ((projectiveHaarPOVM D hD).bornMeasure ρ) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).2
  exact integrable_projectiveHaarPOVM_born_overlap_sq hD ρ O hO

end BornOverlapMoments

section BornScoreBridge

variable {D : ℕ}

theorem memLp_projectiveHaarPOVM_born_calibratedScore_two
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ) (hO : O.IsHermitian) :
    MemLp (haarCalibratedRankOneScore O) 2
      ((projectiveHaarPOVM D hD).bornMeasure ρ) := by
  letI : IsProbabilityMeasure ((projectiveHaarPOVM D hD).bornMeasure ρ) :=
    (projectiveHaarPOVM D hD).born_probability ρ
  have hx := memLp_projectiveHaarPOVM_born_overlap_two hD ρ O hO
  have hscaled := hx.const_mul (((D + 1 : ℕ) : ℝ))
  have hone : MemLp (fun _ : Matrix (Fin D) (Fin D) ℂ ↦ (1 : ℝ)) 2
      ((projectiveHaarPOVM D hD).bornMeasure ρ) := memLp_const 1
  convert hscaled.sub hone using 1
  ext B
  simp [haarCalibratedRankOneScore, Fintype.card_fin]

theorem integral_projectiveHaarPOVM_born_calibratedScore
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ)
    (hO : O.IsHermitian) (hOtrace : O.trace = 1) :
    (∫ B, haarCalibratedRankOneScore O B
        ∂(projectiveHaarPOVM D hD).bornMeasure ρ) =
      (ρ.matrix * O).trace.re := by
  let μ := (projectiveHaarPOVM D hD).bornMeasure ρ
  letI : IsProbabilityMeasure μ :=
    (projectiveHaarPOVM D hD).born_probability ρ
  have hxLp := memLp_projectiveHaarPOVM_born_overlap_two hD ρ O hO
  have hx : Integrable (fun B ↦ (O * B).trace.re) μ :=
    hxLp.integrable (by norm_num)
  have hmean := integral_projectiveHaarPOVM_born_overlap hD ρ O hO hOtrace
  simp only [haarCalibratedRankOneScore, Fintype.card_fin]
  change
    (∫ B, (((D + 1 : ℕ) : ℝ) * (O * B).trace.re - 1) ∂μ) = _
  rw [integral_sub (hx.const_mul _)
      (integrable_const (μ := μ) (1 : ℝ)),
    integral_const_mul, integral_const, hmean]
  simp only [measure_univ, measureReal_def, ENNReal.toReal_one, one_smul]
  field_simp
  push_cast
  ring

set_option maxHeartbeats 1200000 in
theorem integral_projectiveHaarPOVM_born_calibratedScore_sq
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ)
    (hO : O.IsHermitian) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    (∫ B, (haarCalibratedRankOneScore O B) ^ 2
        ∂(projectiveHaarPOVM D hD).bornMeasure ρ) =
      (D : ℝ) * (1 + 2 * (ρ.matrix * O).trace.re) / (D + 2) := by
  let μ := (projectiveHaarPOVM D hD).bornMeasure ρ
  letI : IsProbabilityMeasure μ :=
    (projectiveHaarPOVM D hD).born_probability ρ
  let x : Matrix (Fin D) (Fin D) ℂ → ℝ := fun B ↦ (O * B).trace.re
  let c : ℝ := D + 1
  have hxSq : Integrable (fun B ↦ (x B) ^ 2) μ := by
    simpa [μ, x] using
      integrable_projectiveHaarPOVM_born_overlap_sq hD ρ O hO
  have hxLp := memLp_projectiveHaarPOVM_born_overlap_two hD ρ O hO
  have hx : Integrable x μ := by
    simpa [μ, x] using hxLp.integrable (by norm_num)
  have hmean := integral_projectiveHaarPOVM_born_overlap hD ρ O hO hOtrace
  have hsecond := integral_projectiveHaarPOVM_born_overlap_sq
    hD ρ O hO hOtrace hOidempotent
  have hfun :
      (fun B ↦ (haarCalibratedRankOneScore O B) ^ 2) =
        (fun B ↦ c ^ 2 * (x B) ^ 2 - 2 * c * x B + 1) := by
    funext B
    simp [haarCalibratedRankOneScore, c, x, Fintype.card_fin]
    ring
  rw [hfun]
  have hfirstTerm : Integrable (fun B ↦ c ^ 2 * (x B) ^ 2) μ :=
    hxSq.const_mul _
  have hsecondTerm : Integrable (fun B ↦ 2 * c * x B) μ := by
    simpa [mul_assoc] using hx.const_mul (2 * c)
  change
    (∫ B, c ^ 2 * (x B) ^ 2 - 2 * c * x B + 1 ∂μ) = _
  have hadd :
      (∫ B, c ^ 2 * (x B) ^ 2 - 2 * c * x B + 1 ∂μ) =
        (∫ B, c ^ 2 * (x B) ^ 2 - 2 * c * x B ∂μ) +
          ∫ _B, (1 : ℝ) ∂μ := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      integral_add (hfirstTerm.sub hsecondTerm)
        (integrable_const (μ := μ) (1 : ℝ))
  have hsub :
      (∫ B, c ^ 2 * (x B) ^ 2 - 2 * c * x B ∂μ) =
        (∫ B, c ^ 2 * (x B) ^ 2 ∂μ) -
          ∫ B, 2 * c * x B ∂μ := by
    simpa only [Pi.sub_apply] using
      integral_sub hfirstTerm hsecondTerm
  rw [hadd, hsub, integral_const_mul, integral_const_mul, integral_const]
  simp only [measure_univ, measureReal_def, ENNReal.toReal_one, one_smul]
  dsimp [x, μ]
  rw [hsecond, hmean]
  dsimp [c]
  field_simp
  ring

/-- The previously unasserted score-moment bridge is discharged for the
actual physical Born law of the exact projective Haar POVM. -/
theorem projectiveHaarPOVM_born_rankOneScoreMomentBridge
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ)
    (hO : O.IsHermitian) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    HaarRankOneScoreMomentBridge
      ((projectiveHaarPOVM D hD).bornMeasure ρ) O
      (ρ.matrix * O).trace.re := by
  refine ⟨memLp_projectiveHaarPOVM_born_calibratedScore_two hD ρ O hO,
    integral_projectiveHaarPOVM_born_calibratedScore hD ρ O hO hOtrace,
    ?_⟩
  simpa [Fintype.card_fin] using
    integral_projectiveHaarPOVM_born_calibratedScore_sq hD ρ O hO hOtrace
      hOidempotent

/-- The concrete Born score has the dimension-free variance bound required
by the physical upper-bound pipeline. -/
theorem variance_projectiveHaarPOVM_born_calibratedScore_le_two
    (hD : 0 < D) (ρ : DensityOperator (Fin D))
    (O : Matrix (Fin D) (Fin D) ℂ)
    (hO : O.IsHermitian) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    variance (haarCalibratedRankOneScore O)
        ((projectiveHaarPOVM D hD).bornMeasure ρ) ≤ 2 := by
  letI : IsProbabilityMeasure ((projectiveHaarPOVM D hD).bornMeasure ρ) :=
    (projectiveHaarPOVM D hD).born_probability ρ
  exact variance_haarCalibratedRankOneScore_le_two _ O _
    (projectiveHaarPOVM_born_rankOneScoreMomentBridge
      hD ρ O hO hOtrace hOidempotent)

end BornScoreBridge

end

end TomographyOracleCore
