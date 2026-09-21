import TomographyOracleCore.PhysicalHaarOneCopyPearson

namespace TomographyOracleCore

open MeasureTheory InformationTheory
open scoped ENNReal

noncomputable section

theorem integrable_llr_of_integrable_pearson
    {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν)
    (hpearson : Integrable
      (fun z ↦ ((μ.rnDeriv ν z).toReal - 1) ^ 2) ν) :
    Integrable (llr μ ν) μ := by
  apply (integrable_klFun_rnDeriv_iff hμν).1
  apply hpearson.mono'
  · exact (measurable_klFun.comp
      (ENNReal.measurable_toReal.comp
        (Measure.measurable_rnDeriv _ _))).aestronglyMeasurable
  · filter_upwards with z
    rw [Real.norm_eq_abs, abs_of_nonneg (klFun_nonneg ENNReal.toReal_nonneg)]
    exact klFun_le_sq_sub_one ENNReal.toReal_nonneg

theorem integrable_pearson_rnDeriv_withDensity_of_integrable_difference
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SigmaFinite μ]
    (p q : Ω → ℝ≥0∞)
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ)
    (hp_ne_top : ∀ᵐ z ∂μ, p z ≠ ∞)
    (hq_ne_zero : ∀ᵐ z ∂μ, q z ≠ 0)
    (hq_ne_top : ∀ᵐ z ∂μ, q z ≠ ∞)
    (hdiff : Integrable
      (fun z ↦ ((p z).toReal - (q z).toReal) ^ 2 / (q z).toReal) μ) :
    Integrable
      (fun z ↦ (((μ.withDensity p).rnDeriv (μ.withDensity q) z).toReal - 1) ^ 2)
      (μ.withDensity q) := by
  have hratio := rnDeriv_withDensity_div μ p q hp hq
    hp_ne_top hq_ne_zero hq_ne_top
  have hratio_q :
      (μ.withDensity p).rnDeriv (μ.withDensity q) =ᵐ[μ.withDensity q]
        fun z ↦ p z / q z :=
    (withDensity_absolutelyContinuous μ q).ae_eq hratio
  have hratio_int : Integrable
      (fun z ↦ ((p z / q z).toReal - 1) ^ 2) (μ.withDensity q) := by
    rw [integrable_withDensity_iff_integrable_smul₀' hq
      (hq_ne_top.mono fun z hz ↦ (lt_top_iff_ne_top).2 hz)]
    apply hdiff.congr
    filter_upwards [hq_ne_zero, hq_ne_top] with z hq0 hqtop
    have hqreal : (q z).toReal ≠ 0 := by
      exact ENNReal.toReal_ne_zero.mpr ⟨hq0, hqtop⟩
    simp only [ENNReal.toReal_div, smul_eq_mul]
    field_simp
  apply hratio_int.congr
  filter_upwards [hratio_q] with z hz
  rw [hz]

theorem integrable_llr_withDensity_of_integrable_difference
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : Ω → ℝ≥0∞)
    [IsFiniteMeasure (μ.withDensity p)] [IsFiniteMeasure (μ.withDensity q)]
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ)
    (hp_ne_top : ∀ᵐ z ∂μ, p z ≠ ∞)
    (hq_ne_zero : ∀ᵐ z ∂μ, q z ≠ 0)
    (hq_ne_top : ∀ᵐ z ∂μ, q z ≠ ∞)
    (hdiff : Integrable
      (fun z ↦ ((p z).toReal - (q z).toReal) ^ 2 / (q z).toReal) μ) :
    Integrable (llr (μ.withDensity p) (μ.withDensity q))
      (μ.withDensity p) := by
  have hac : μ.withDensity p ≪ μ.withDensity q :=
    withDensity_absolutelyContinuous_withDensity μ p q hq hq_ne_zero
  exact integrable_llr_of_integrable_pearson _ _ hac
    (integrable_pearson_rnDeriv_withDensity_of_integrable_difference
      μ p q hp hq hp_ne_top hq_ne_zero hq_ne_top hdiff)

theorem toReal_klDiv_withDensity_eq_integral_klFun_div
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (p q : Ω → ℝ≥0∞)
    [IsFiniteMeasure (μ.withDensity p)] [IsFiniteMeasure (μ.withDensity q)]
    (hp : AEMeasurable p μ) (hq : AEMeasurable q μ)
    (hp_ne_top : ∀ᵐ z ∂μ, p z ≠ ∞)
    (hq_ne_zero : ∀ᵐ z ∂μ, q z ≠ 0)
    (hq_ne_top : ∀ᵐ z ∂μ, q z ≠ ∞) :
    (klDiv (μ.withDensity p) (μ.withDensity q)).toReal =
      ∫ z, klFun (p z / q z).toReal * (q z).toReal ∂μ := by
  have hac : μ.withDensity p ≪ μ.withDensity q :=
    withDensity_absolutelyContinuous_withDensity μ p q hq hq_ne_zero
  have hratio := rnDeriv_withDensity_div μ p q hp hq
    hp_ne_top hq_ne_zero hq_ne_top
  have hratio_q :
      (μ.withDensity p).rnDeriv (μ.withDensity q) =ᵐ[μ.withDensity q]
        fun z ↦ p z / q z :=
    (withDensity_absolutelyContinuous μ q).ae_eq hratio
  have hklcongr :
      (fun z ↦ klFun
        (((μ.withDensity p).rnDeriv (μ.withDensity q) z).toReal))
        =ᵐ[μ.withDensity q]
      (fun z ↦ klFun ((p z / q z).toReal)) := by
    filter_upwards [hratio_q] with z hz
    rw [hz]
  rw [toReal_klDiv_eq_integral_klFun hac]
  rw [integral_congr_ae hklcongr]
  rw [integral_withDensity_eq_integral_toReal_smul₀ hq
    (hq_ne_top.mono fun z hz ↦ (lt_top_iff_ne_top).2 hz)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [smul_eq_mul, mul_comm]

namespace PhysicalPOVM.DominatedPOVM

open MatrixReduction
open scoped ComplexOrder

variable {k m : ℕ} {Outcome : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

def orientedHardProjectorBornDensity
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (z : Outcome)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) : ℝ≥0∞ :=
  bornDensityFrom M.effect
    (orientedHardProjectorDensityOperator U P b hm hb0 hbquarter) z

def orientedHardReferenceBornDensity
    (M : DominatedPOVM (k + 2) Outcome)
    (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (z : Outcome)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) : ℝ≥0∞ :=
  bornDensityFrom M.effect
    (orientedHardReferenceDensityOperator k b hk hb0 hbquarter U) z

def orientedPOVMKLDensityIntegrand
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (z : Outcome)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) : ℝ :=
  let p := orientedHardProjectorBornDensity M P b hm hb0 hbquarter z U
  let q := orientedHardReferenceBornDensity M b hk hb0 hbquarter z U
  klFun (p / q).toReal * q.toReal

theorem measurable_uncurry_orientedHardProjectorBornDensity
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    Measurable (Function.uncurry
      (orientedHardProjectorBornDensity M P b hm hb0 hbquarter)) := by
  unfold Function.uncurry orientedHardProjectorBornDensity bornDensityFrom
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ (fun i _ ↦
    Finset.measurable_sum Finset.univ (fun j _ ↦
      (((measurable_complexMatrix_apply (Fin (k + 2)) i j).comp
        ((continuous_unitaryConjugateMatrix_fixed
          (hardProjectorMatrix P b)).measurable.comp measurable_snd)).mul
        ((M.effect_measurable j i).comp measurable_fst))))

theorem measurable_uncurry_orientedHardReferenceBornDensity
    (M : DominatedPOVM (k + 2) Outcome)
    (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    Measurable (Function.uncurry
      (orientedHardReferenceBornDensity M b hk hb0 hbquarter)) := by
  unfold Function.uncurry orientedHardReferenceBornDensity bornDensityFrom
  apply ENNReal.measurable_ofReal.comp
  apply Complex.measurable_re.comp
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.measurable_sum Finset.univ (fun i _ ↦
    Finset.measurable_sum Finset.univ (fun j _ ↦
      (((measurable_complexMatrix_apply (Fin (k + 2)) i j).comp
        ((continuous_unitaryConjugateMatrix_fixed
          (hardReferenceMatrix k b)).measurable.comp measurable_snd)).mul
        ((M.effect_measurable j i).comp measurable_fst))))

theorem measurable_uncurry_orientedPOVMKLDensityIntegrand
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    Measurable (Function.uncurry
      (orientedPOVMKLDensityIntegrand M P b hm hk hb0 hbquarter)) := by
  let p := Function.uncurry
    (orientedHardProjectorBornDensity M P b hm hb0 hbquarter)
  let q := Function.uncurry
    (orientedHardReferenceBornDensity M b hk hb0 hbquarter)
  have hp : Measurable p :=
    measurable_uncurry_orientedHardProjectorBornDensity M P b hm hb0 hbquarter
  have hq : Measurable q :=
    measurable_uncurry_orientedHardReferenceBornDensity M b hk hb0 hbquarter
  unfold Function.uncurry orientedPOVMKLDensityIntegrand
  exact (measurable_klFun.comp
    (ENNReal.measurable_toReal.comp (hp.div hq))).mul
      (ENNReal.measurable_toReal.comp hq)

theorem ae_orientedBornDifference_eq_orientedPOVMEffectPearsonIntegrand
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    (fun z ↦
      let p := orientedHardProjectorBornDensity M P b hm hb0 hbquarter z U
      let q := orientedHardReferenceBornDensity M b hk hb0 hbquarter z U
      (p.toReal - q.toReal) ^ 2 / q.toReal) =ᵐ[M.base]
    (fun z ↦ orientedPOVMEffectPearsonIntegrand k b
      (centeredProjectorTail P) M z U) := by
  filter_upwards [
      M.born_density_ae_nonnegative
        (orientedHardProjectorDensityOperator U P b hm hb0 hbquarter),
      M.born_density_ae_nonnegative
        (orientedHardReferenceDensityOperator k b hk hb0 hbquarter U)] with z hp hq
  unfold orientedHardProjectorBornDensity orientedHardReferenceBornDensity
    bornDensityFrom
  dsimp only
  rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
  change
    ((unitaryConjugateMatrix U (hardProjectorMatrix P b) * M.effect z).trace.re -
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * M.effect z).trace.re) ^ 2 /
      (unitaryConjugateMatrix U (hardReferenceMatrix k b) * M.effect z).trace.re = _
  rw [bornTrace_orientedHardProjector_sub_orientedHardReference U P b (M.effect z)]
  unfold orientedPOVMEffectPearsonIntegrand orientedEffectPearsonIntegrand
  rw [embeddedTailMatrix_eq_embeddedCenteredProjectorTail]

theorem ae_orientedPOVMKLDensityIntegrand_le_effectPearson
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    (fun z ↦ orientedPOVMKLDensityIntegrand
      M P b hm hk hb.le hbquarter z U) ≤ᵐ[M.base]
    (fun z ↦ orientedPOVMEffectPearsonIntegrand k b
      (centeredProjectorTail P) M z U) := by
  filter_upwards [
      orientedHardReferenceBornDensity_ae_ne_zero M hk b hb hbquarter U,
      bornDensityFrom_ae_ne_top M
        (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U),
      ae_orientedBornDifference_eq_orientedPOVMEffectPearsonIntegrand
        M P b hm hk hb.le hbquarter U] with z hq0 hqtop hdiff
  let p := orientedHardProjectorBornDensity M P b hm hb.le hbquarter z U
  let q := orientedHardReferenceBornDensity M b hk hb.le hbquarter z U
  have hqreal : q.toReal ≠ 0 := by
    exact ENNReal.toReal_ne_zero.mpr ⟨hq0, hqtop⟩
  calc
    orientedPOVMKLDensityIntegrand M P b hm hk hb.le hbquarter z U =
        klFun (p / q).toReal * q.toReal := by rfl
    _ ≤ ((p / q).toReal - 1) ^ 2 * q.toReal := by
      exact mul_le_mul_of_nonneg_right
        (klFun_le_sq_sub_one ENNReal.toReal_nonneg) ENNReal.toReal_nonneg
    _ = (p.toReal - q.toReal) ^ 2 / q.toReal := by
      rw [ENNReal.toReal_div]
      field_simp
    _ = orientedPOVMEffectPearsonIntegrand k b
        (centeredProjectorTail P) M z U := hdiff

set_option maxHeartbeats 800000 in
theorem integrable_orientedPOVMKLDensityIntegrand_prod
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    Integrable (fun x :
      unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) × Outcome ↦
        orientedPOVMKLDensityIntegrand
          M P b hm hk hb.le hbquarter x.2 x.1)
      ((unitaryHaarProbability (k + 2)).prod M.base) := by
  letI : IsFiniteMeasure M.base := M.base_finite
  have hb1 : b < 1 := lt_of_le_of_lt hbquarter (by norm_num)
  let G : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) × Outcome → ℝ :=
    fun x ↦ orientedPOVMKLDensityIntegrand
      M P b hm hk hb.le hbquarter x.2 x.1
  let F : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) × Outcome → ℝ :=
    fun x ↦ orientedPOVMEffectPearsonIntegrand k b
      (centeredProjectorTail P) M x.2 x.1
  change Integrable G ((unitaryHaarProbability (k + 2)).prod M.base)
  have hGmeas : Measurable G := by
    change Measurable (Function.uncurry
      (orientedPOVMKLDensityIntegrand M P b hm hk hb.le hbquarter) ∘ Prod.swap)
    exact (measurable_uncurry_orientedPOVMKLDensityIntegrand
      M P b hm hk hb.le hbquarter).comp measurable_swap
  have hFmeas : Measurable F := by
    change Measurable (Function.uncurry
      (orientedPOVMEffectPearsonIntegrand k b (centeredProjectorTail P) M) ∘
        Prod.swap)
    exact (measurable_uncurry_orientedPOVMEffectPearsonIntegrand
      k b (centeredProjectorTail P) M).comp measurable_swap
  have hF : Integrable F
      ((unitaryHaarProbability (k + 2)).prod M.base) := by
    change Integrable (Function.uncurry
      (orientedPOVMEffectPearsonIntegrand k b (centeredProjectorTail P) M) ∘
        Prod.swap) ((unitaryHaarProbability (k + 2)).prod M.base)
    exact (integrable_uncurry_orientedPOVMEffectPearsonIntegrand
      k hk b hb.le hbquarter hb1 (centeredProjectorTail P)
        (centeredProjectorTail_isHermitian P)
        (centeredProjectorTail_trace_eq_zero P hm hk) M).swap
  apply hF.mono'
  · exact hGmeas.aestronglyMeasurable
  · change ∀ᵐ x ∂(unitaryHaarProbability (k + 2)).prod M.base,
      ‖G x‖ ≤ F x
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hGmeas.norm hFmeas)).2
    filter_upwards with U
    filter_upwards [ae_orientedPOVMKLDensityIntegrand_le_effectPearson
      M P b hm hk hb hbquarter U] with z hz
    change ‖orientedPOVMKLDensityIntegrand
      M P b hm hk hb.le hbquarter z U‖ ≤
        orientedPOVMEffectPearsonIntegrand k b
          (centeredProjectorTail P) M z U
    have hGnonneg : 0 ≤ orientedPOVMKLDensityIntegrand
        M P b hm hk hb.le hbquarter z U := by
      unfold orientedPOVMKLDensityIntegrand
      dsimp only
      exact mul_nonneg (klFun_nonneg ENNReal.toReal_nonneg)
        ENNReal.toReal_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hGnonneg]
    exact hz

theorem toReal_klDiv_orientedHardProjector_orientedHardReference_eq_integral
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    (klDiv
      (M.bornMeasure (orientedHardProjectorDensityOperator
        U P b hm hb.le hbquarter))
      (M.bornMeasure (orientedHardReferenceDensityOperator
        k b hk hb.le hbquarter U))).toReal =
      ∫ z, orientedPOVMKLDensityIntegrand
        M P b hm hk hb.le hbquarter z U ∂M.base := by
  let ρp := orientedHardProjectorDensityOperator U P b hm hb.le hbquarter
  let ρq := orientedHardReferenceDensityOperator k b hk hb.le hbquarter U
  letI : IsFiniteMeasure M.base := M.base_finite
  letI : IsProbabilityMeasure
      (M.base.withDensity (bornDensityFrom M.effect ρp)) := by
    change IsProbabilityMeasure (M.bornMeasure ρp)
    exact M.born_probability ρp
  letI : IsProbabilityMeasure
      (M.base.withDensity (bornDensityFrom M.effect ρq)) := by
    change IsProbabilityMeasure (M.bornMeasure ρq)
    exact M.born_probability ρq
  change (klDiv
      (M.base.withDensity (bornDensityFrom M.effect ρp))
      (M.base.withDensity (bornDensityFrom M.effect ρq))).toReal = _
  exact toReal_klDiv_withDensity_eq_integral_klFun_div M.base
    (bornDensityFrom M.effect ρp) (bornDensityFrom M.effect ρq)
    (measurable_bornDensityFrom M ρp).aemeasurable
    (measurable_bornDensityFrom M ρq).aemeasurable
    (bornDensityFrom_ae_ne_top M ρp)
    (orientedHardReferenceBornDensity_ae_ne_zero M hk b hb hbquarter U)
    (bornDensityFrom_ae_ne_top M ρq)

theorem ae_integrable_orientedHardProjector_bornDensity_difference
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      Integrable (fun z ↦
        let p := orientedHardProjectorBornDensity
          M P b hm hb.le hbquarter z U
        let q := orientedHardReferenceBornDensity
          M b hk hb.le hbquarter z U
        (p.toReal - q.toReal) ^ 2 / q.toReal) M.base := by
  letI : IsFiniteMeasure M.base := M.base_finite
  have hb1 : b < 1 := lt_of_le_of_lt hbquarter (by norm_num)
  have hF := integrable_uncurry_orientedPOVMEffectPearsonIntegrand
    k hk b hb.le hbquarter hb1 (centeredProjectorTail P)
      (centeredProjectorTail_isHermitian P)
      (centeredProjectorTail_trace_eq_zero P hm hk) M
  filter_upwards [hF.prod_left_ae] with U hU
  exact hU.congr
    (ae_orientedBornDifference_eq_orientedPOVMEffectPearsonIntegrand
      M P b hm hk hb.le hbquarter U).symm

theorem ae_integrable_llr_orientedHardProjector_orientedHardReference
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      Integrable
        (llr
          (M.bornMeasure (orientedHardProjectorDensityOperator
            U P b hm hb.le hbquarter))
          (M.bornMeasure (orientedHardReferenceDensityOperator
            k b hk hb.le hbquarter U)))
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter)) := by
  filter_upwards [ae_integrable_orientedHardProjector_bornDensity_difference
    M P b hm hk hb hbquarter] with U hdiff
  let ρp := orientedHardProjectorDensityOperator U P b hm hb.le hbquarter
  let ρq := orientedHardReferenceDensityOperator k b hk hb.le hbquarter U
  letI : IsFiniteMeasure M.base := M.base_finite
  letI : IsProbabilityMeasure
      (M.base.withDensity (bornDensityFrom M.effect ρp)) := by
    change IsProbabilityMeasure (M.bornMeasure ρp)
    exact M.born_probability ρp
  letI : IsProbabilityMeasure
      (M.base.withDensity (bornDensityFrom M.effect ρq)) := by
    change IsProbabilityMeasure (M.bornMeasure ρq)
    exact M.born_probability ρq
  change Integrable
    (llr
      (M.base.withDensity (bornDensityFrom M.effect ρp))
      (M.base.withDensity (bornDensityFrom M.effect ρq)))
    (M.base.withDensity (bornDensityFrom M.effect ρp))
  exact integrable_llr_withDensity_of_integrable_difference M.base
    (bornDensityFrom M.effect ρp) (bornDensityFrom M.effect ρq)
    (measurable_bornDensityFrom M ρp).aemeasurable
    (measurable_bornDensityFrom M ρq).aemeasurable
    (bornDensityFrom_ae_ne_top M ρp)
    (orientedHardReferenceBornDensity_ae_ne_zero M hk b hb hbquarter U)
    (bornDensityFrom_ae_ne_top M ρq) hdiff

theorem ae_klDiv_orientedHardProjector_orientedHardReference_ne_top
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      klDiv
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U)) ≠ ∞ := by
  filter_upwards [ae_integrable_llr_orientedHardProjector_orientedHardReference
    M P b hm hk hb hbquarter] with U hllr
  let ρp := orientedHardProjectorDensityOperator U P b hm hb.le hbquarter
  let ρq := orientedHardReferenceDensityOperator k b hk hb.le hbquarter U
  letI : IsProbabilityMeasure (M.bornMeasure ρp) := M.born_probability ρp
  letI : IsProbabilityMeasure (M.bornMeasure ρq) := M.born_probability ρq
  apply klDiv_ne_top_of_llr_integrable
    (M.bornMeasure ρp) (M.bornMeasure ρq)
  · change M.base.withDensity (bornDensityFrom M.effect ρp) ≪
      M.base.withDensity (bornDensityFrom M.effect ρq)
    exact withDensity_absolutelyContinuous_withDensity M.base _ _
      (measurable_bornDensityFrom M ρq).aemeasurable
      (orientedHardReferenceBornDensity_ae_ne_zero M hk b hb hbquarter U)
  · exact hllr

set_option maxHeartbeats 800000 in
theorem integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le_pearsonChiSquare
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      (klDiv
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U))).toReal
      ∂unitaryHaarProbability (k + 2)) ≤
    ∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U))
      ∂unitaryHaarProbability (k + 2) := by
  letI : IsFiniteMeasure M.base := M.base_finite
  have hb1 : b < 1 := lt_of_le_of_lt hbquarter (by norm_num)
  let G : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) × Outcome → ℝ :=
    fun x ↦ orientedPOVMKLDensityIntegrand
      M P b hm hk hb.le hbquarter x.2 x.1
  let F : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) × Outcome → ℝ :=
    fun x ↦ orientedPOVMEffectPearsonIntegrand k b
      (centeredProjectorTail P) M x.2 x.1
  have hG : Integrable G
      ((unitaryHaarProbability (k + 2)).prod M.base) := by
    exact integrable_orientedPOVMKLDensityIntegrand_prod
      M P b hm hk hb hbquarter
  have hF : Integrable F
      ((unitaryHaarProbability (k + 2)).prod M.base) := by
    change Integrable (Function.uncurry
      (orientedPOVMEffectPearsonIntegrand k b (centeredProjectorTail P) M) ∘
        Prod.swap) ((unitaryHaarProbability (k + 2)).prod M.base)
    exact (integrable_uncurry_orientedPOVMEffectPearsonIntegrand
      k hk b hb.le hbquarter hb1 (centeredProjectorTail P)
        (centeredProjectorTail_isHermitian P)
        (centeredProjectorTail_trace_eq_zero P hm hk) M).swap
  have hsections : ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      (∫ z, G (U, z) ∂M.base) ≤ ∫ z, F (U, z) ∂M.base := by
    filter_upwards [hG.prod_right_ae, hF.prod_right_ae] with U hGU hFU
    apply integral_mono_ae hGU hFU
    simpa only [G, F] using
      ae_orientedPOVMKLDensityIntegrand_le_effectPearson
        M P b hm hk hb hbquarter U
  calc
    _ = ∫ U, ∫ z, G (U, z) ∂M.base
          ∂unitaryHaarProbability (k + 2) := by
      apply integral_congr_ae
      filter_upwards with U
      exact toReal_klDiv_orientedHardProjector_orientedHardReference_eq_integral
        M P b hm hk hb hbquarter U
    _ ≤ ∫ U, ∫ z, F (U, z) ∂M.base
          ∂unitaryHaarProbability (k + 2) := by
      exact integral_mono_ae hG.integral_prod_left hF.integral_prod_left hsections
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with U
      symm
      exact pearsonChiSquare_orientedHardProjector_orientedHardReference_eq_integral
        M P b hm hk hb hbquarter U

theorem integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le_exact
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      (klDiv
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U))).toReal
      ∂unitaryHaarProbability (k + 2)) ≤
      (2 * b ^ 2 / (1 - b)) *
        (1 / (m : ℝ) - 1 / (k : ℝ)) := by
  exact (integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le_pearsonChiSquare
    M P b hm hk hb hbquarter).trans
      (integral_unitaryHaar_pearsonChiSquare_orientedHardProjector_le_exact
        M P b hm hk hb hbquarter)

theorem integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      (klDiv
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U))).toReal
      ∂unitaryHaarProbability (k + 2)) ≤
      8 * b ^ 2 / (3 * (m : ℝ)) := by
  exact (integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le_pearsonChiSquare
    M P b hm hk hb hbquarter).trans
      (integral_unitaryHaar_pearsonChiSquare_orientedHardProjector_le
        M P b hm hk hb hbquarter)

end PhysicalPOVM.DominatedPOVM

end

end TomographyOracleCore

