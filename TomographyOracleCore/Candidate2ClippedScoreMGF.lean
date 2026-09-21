import TomographyOracleCore.Candidate2ClippedSpreadBias
import Mathlib.Probability.Moments.SubGaussian

/-!
# Scalar exponential moments for the clipped Candidate 2 score

This module proves the bounded-range concentration facts for one fixed scalar
score.  It uses Hoeffding's lemma with its exact range constant, tensorizes it
over independent coordinates, and records the optimized one-sided tail.

These are scalar statements.  No finite-net construction or uniform bound over
the unit sphere is asserted here.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

/-- On nonnegative input, the rescaled clipped score is at most its clipping
level `lambda⁻¹`. -/
theorem clippedSpread_le_inv
    {lambda y : ℝ} (hlambda : 0 < lambda) (hy : 0 ≤ y) :
    clippedSpread lambda y ≤ lambda⁻¹ := by
  have hprod : 0 ≤ lambda * y := mul_nonneg hlambda.le hy
  have hleft : ¬lambda * y < -1 := by linarith
  by_cases htail : 1 < lambda * y
  · rw [clippedSpread, clippedPsi, if_neg hleft, if_pos htail, mul_one]
  · rw [clippedSpread, clippedPsi, if_neg hleft, if_neg htail,
      ← mul_assoc, inv_mul_cancel₀ hlambda.ne', one_mul]
    rw [← one_div]
    exact (le_div_iff₀ hlambda).2 (by
      simpa [mul_comm] using not_lt.mp htail)

/-- The scalar clipping map is measurable. -/
theorem measurable_clippedSpread (lambda : ℝ) :
    Measurable (clippedSpread lambda) := by
  rw [show clippedSpread lambda =
      fun y => lambda⁻¹ * max (-1) (min (lambda * y) 1) by
    funext y
    rw [clippedSpread, clippedPsi_eq_max_min]]
  fun_prop

/-- Almost-sure range of a clipped nonnegative score. -/
theorem ae_clippedSpread_mem_Icc
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {Y : Omega → ℝ} {lambda : ℝ}
    (hlambda : 0 < lambda) (hYnonneg : ∀ᵐ omega ∂mu, 0 ≤ Y omega) :
    ∀ᵐ omega ∂mu,
      clippedSpread lambda (Y omega) ∈ Set.Icc 0 lambda⁻¹ := by
  filter_upwards [hYnonneg] with omega hY
  exact ⟨clippedSpread_nonneg hlambda hY,
    clippedSpread_le_inv hlambda hY⟩

/-- Explicit Hoeffding MGF for a centered scalar variable in `[a,b]`.
The exponent is `(b-a)^2 t^2 / 8`. -/
theorem mgf_centered_bounded_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {a b t : ℝ}
    (hX : AEMeasurable X mu)
    (hXrange : ∀ᵐ omega ∂mu, X omega ∈ Set.Icc a b)
    (hab : a ≤ b) :
    mgf (fun omega ↦ X omega - ∫ z, X z ∂mu) mu t ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / 8) := by
  have hSub := hasSubgaussianMGF_of_mem_Icc hX hXrange
  have h := hSub.mgf_le t
  refine h.trans_eq ?_
  congr 1
  simp only [NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat]
  rw [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)]
  ring

/-- Every exponential tilt of a centered bounded scalar is integrable. -/
theorem integrable_exp_mul_centered_bounded
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {X : Omega → ℝ} {a b t : ℝ}
    (hX : AEMeasurable X mu)
    (hXrange : ∀ᵐ omega ∂mu, X omega ∈ Set.Icc a b) :
    Integrable
      (fun omega ↦ Real.exp (t * (X omega - ∫ z, X z ∂mu))) mu :=
  (hasSubgaussianMGF_of_mem_Icc hX hXrange).integrable_exp_mul t

/-- Clipped-score specialization of Hoeffding's lemma.  Since the score lies
in `[0, lambda⁻¹]`, its centered MGF has exponent
`t^2 / (8 lambda^2)`. -/
theorem mgf_centered_clippedSpread_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {Y : Omega → ℝ} (hY : AEMeasurable Y mu)
    (hYnonneg : ∀ᵐ omega ∂mu, 0 ≤ Y omega)
    {lambda t : ℝ} (hlambda : 0 < lambda) :
    mgf (fun omega ↦
      clippedSpread lambda (Y omega) -
        ∫ z, clippedSpread lambda (Y z) ∂mu) mu t ≤
      Real.exp (t ^ 2 / (8 * lambda ^ 2)) := by
  have hclip : AEMeasurable (fun omega ↦ clippedSpread lambda (Y omega)) mu :=
    (measurable_clippedSpread lambda).comp_aemeasurable hY
  have h := mgf_centered_bounded_le hclip
    (ae_clippedSpread_mem_Icc hlambda hYnonneg)
    (inv_nonneg.mpr hlambda.le) (t := t)
  calc
    mgf (fun omega ↦
      clippedSpread lambda (Y omega) -
        ∫ z, clippedSpread lambda (Y z) ∂mu) mu t ≤
        Real.exp ((lambda⁻¹ - 0) ^ 2 * t ^ 2 / 8) := h
    _ = Real.exp (t ^ 2 / (8 * lambda ^ 2)) := by
      congr 1
      field_simp [hlambda.ne']
      ring

/-- Centered empirical mean of scalar coordinates.  The coordinates may have
different laws; each is centered by its own expectation. -/
def centeredScalarEmpiricalMean
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {T : ℕ} (X : Fin T → Omega → ℝ)
    (omega : Omega) : ℝ :=
  ((T : ℝ)⁻¹) * ∑ i, (X i omega - ∫ z, X i z ∂mu)

/-- An independent empirical mean of variables in a common interval `[a,b]`
is sub-Gaussian with exact Hoeffding parameter `(b-a)^2/(4T)`. -/
theorem centeredScalarEmpiricalMean_hasSubgaussianMGF
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (X : Fin T → Omega → ℝ)
    (hIndep : iIndepFun X mu)
    (hX : ∀ i, Measurable (X i))
    {a b : ℝ} (hXrange : ∀ i, ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc a b)
    (hab : a ≤ b) :
    HasSubgaussianMGF (centeredScalarEmpiricalMean mu X)
      (NNReal.mk ((b - a) ^ 2 / (4 * (T : ℝ))) (by positivity)) mu := by
  let c : ℝ≥0 := (‖b - a‖₊ / 2) ^ 2
  have hIndepCentered : iIndepFun
      (fun i omega ↦ X i omega - ∫ z, X i z ∂mu) mu := by
    simpa [Function.comp_def] using
      hIndep.comp
        (fun i x ↦ x - ∫ z, X i z ∂mu)
        (fun _i ↦ measurable_id.sub measurable_const)
  have hEach (i : Fin T) : HasSubgaussianMGF
      (fun omega ↦ X i omega - ∫ z, X i z ∂mu) c mu := by
    exact hasSubgaussianMGF_of_mem_Icc
      (hX i).aemeasurable (hXrange i)
  have hSum : HasSubgaussianMGF
      (fun omega ↦ ∑ i, (X i omega - ∫ z, X i z ∂mu))
      (∑ _i : Fin T, c) mu := by
    simpa using HasSubgaussianMGF.sum_of_iIndepFun
      hIndepCentered (s := Finset.univ)
        (c := fun _i ↦ c) (fun i _hi ↦ hEach i)
  have hScaled := hSum.const_mul ((T : ℝ)⁻¹)
  have hc :
      NNReal.mk (((T : ℝ)⁻¹) ^ 2) (sq_nonneg ((T : ℝ)⁻¹)) *
          (∑ _i : Fin T, c) =
        NNReal.mk ((b - a) ^ 2 / (4 * (T : ℝ))) (by positivity) := by
    apply NNReal.eq
    dsimp [c]
    simp only [NNReal.coe_sum,
      NNReal.coe_pow, NNReal.coe_div, NNReal.coe_ofNat]
    rw [coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr hab)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne']
    ring
  change HasSubgaussianMGF
    (fun omega ↦ ((T : ℝ)⁻¹) *
      ∑ i, (X i omega - ∫ z, X i z ∂mu))
    (NNReal.mk (((T : ℝ)⁻¹) ^ 2) (sq_nonneg ((T : ℝ)⁻¹)) *
      (∑ _i : Fin T, c)) mu at hScaled
  rw [hc] at hScaled
  change HasSubgaussianMGF
    (fun omega ↦ ((T : ℝ)⁻¹) *
      ∑ i, (X i omega - ∫ z, X i z ∂mu))
    (NNReal.mk ((b - a) ^ 2 / (4 * (T : ℝ))) (by positivity)) mu
  exact hScaled

/-- Explicit MGF form of independent bounded-coordinate tensorization. -/
theorem mgf_centeredScalarEmpiricalMean_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (X : Fin T → Omega → ℝ)
    (hIndep : iIndepFun X mu)
    (hX : ∀ i, Measurable (X i))
    {a b : ℝ} (hXrange : ∀ i, ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc a b)
    (hab : a ≤ b) (t : ℝ) :
    mgf (centeredScalarEmpiricalMean mu X) mu t ≤
      Real.exp ((b - a) ^ 2 * t ^ 2 / (8 * (T : ℝ))) := by
  have h := (centeredScalarEmpiricalMean_hasSubgaussianMGF
    hT X hIndep hX hXrange hab).mgf_le t
  refine h.trans_eq ?_
  congr 1
  simp only [NNReal.coe_mk]
  ring

/-- Optimized one-sided Hoeffding tail for an independent bounded empirical
mean.  A strict interval width makes the conventional exponent
`-2 T epsilon^2/(b-a)^2` nondegenerate. -/
theorem measure_centeredScalarEmpiricalMean_ge_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (X : Fin T → Omega → ℝ)
    (hIndep : iIndepFun X mu)
    (hX : ∀ i, Measurable (X i))
    {a b : ℝ} (hXrange : ∀ i, ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc a b)
    (hab : a < b) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤ centeredScalarEmpiricalMean mu X omega} ≤
      Real.exp (-2 * (T : ℝ) * epsilon ^ 2 / (b - a) ^ 2) := by
  have h := (centeredScalarEmpiricalMean_hasSubgaussianMGF
    hT X hIndep hX hXrange hab.le).measure_ge_le hepsilon
  refine h.trans_eq ?_
  congr 1
  simp only [NNReal.coe_mk]
  field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne',
    sub_ne_zero.mpr hab.ne']
  ring

/-- Two-sided Hoeffding tail for the absolute centered empirical mean. -/
theorem measure_abs_centeredScalarEmpiricalMean_ge_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (X : Fin T → Omega → ℝ)
    (hIndep : iIndepFun X mu)
    (hX : ∀ i, Measurable (X i))
    {a b : ℝ} (hXrange : ∀ i, ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc a b)
    (hab : a < b) {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤
        |centeredScalarEmpiricalMean mu X omega|} ≤
      2 * Real.exp (-2 * (T : ℝ) * epsilon ^ 2 / (b - a) ^ 2) := by
  let c : ℝ≥0 := NNReal.mk
    ((b - a) ^ 2 / (4 * (T : ℝ))) (by positivity)
  have hSub : HasSubgaussianMGF
      (centeredScalarEmpiricalMean mu X) c mu :=
    centeredScalarEmpiricalMean_hasSubgaussianMGF
      hT X hIndep hX hXrange hab.le
  have hexponent :
      -epsilon ^ 2 / (2 * (c : ℝ)) =
        -2 * (T : ℝ) * epsilon ^ 2 / (b - a) ^ 2 := by
    dsimp [c]
    field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne',
      sub_ne_zero.mpr hab.ne']
    ring
  have hupper := hSub.measure_ge_le hepsilon
  have hlower := hSub.neg.measure_ge_le hepsilon
  have hset :
      {omega | epsilon ≤ |centeredScalarEmpiricalMean mu X omega|} =
        {omega | epsilon ≤ centeredScalarEmpiricalMean mu X omega} ∪
        {omega | epsilon ≤ -centeredScalarEmpiricalMean mu X omega} := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_union, le_abs]
  rw [hset]
  calc
    mu.real
        ({omega | epsilon ≤ centeredScalarEmpiricalMean mu X omega} ∪
          {omega | epsilon ≤ -centeredScalarEmpiricalMean mu X omega}) ≤
        mu.real {omega | epsilon ≤ centeredScalarEmpiricalMean mu X omega} +
          mu.real {omega | epsilon ≤
            -centeredScalarEmpiricalMean mu X omega} :=
      measureReal_union_le _ _
    _ ≤ Real.exp (-epsilon ^ 2 / (2 * (c : ℝ))) +
        Real.exp (-epsilon ^ 2 / (2 * (c : ℝ))) :=
      add_le_add hupper hlower
    _ = 2 * Real.exp
        (-2 * (T : ℝ) * epsilon ^ 2 / (b - a) ^ 2) := by
      rw [hexponent]
      ring

/-- Coordinatewise clipping preserves independence. -/
theorem iIndepFun_clippedSpread
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {T : ℕ} (Y : Fin T → Omega → ℝ)
    (hIndep : iIndepFun Y mu) (lambda : ℝ) :
    iIndepFun
      (fun i omega ↦ clippedSpread lambda (Y i omega)) mu := by
  simpa [Function.comp_def] using
    hIndep.comp (fun _i ↦ clippedSpread lambda)
      (fun _i ↦ measurable_clippedSpread lambda)

/-- The independently sampled centered clipped-score average. -/
def centeredClippedSpreadEmpiricalMean
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) {T : ℕ} (lambda : ℝ)
    (Y : Fin T → Omega → ℝ) : Omega → ℝ :=
  centeredScalarEmpiricalMean mu
    (fun i omega ↦ clippedSpread lambda (Y i omega))

/-- Independent-sample MGF for the clipped score.  The exact exponent is
`t^2/(8 T lambda^2)`. -/
theorem mgf_centeredClippedSpreadEmpiricalMean_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (Y : Fin T → Omega → ℝ)
    (hIndep : iIndepFun Y mu)
    (hY : ∀ i, Measurable (Y i))
    (hYnonneg : ∀ i, ∀ᵐ omega ∂mu, 0 ≤ Y i omega)
    {lambda : ℝ} (hlambda : 0 < lambda) (t : ℝ) :
    mgf (centeredClippedSpreadEmpiricalMean mu lambda Y) mu t ≤
      Real.exp (t ^ 2 / (8 * (T : ℝ) * lambda ^ 2)) := by
  let X : Fin T → Omega → ℝ :=
    fun i omega ↦ clippedSpread lambda (Y i omega)
  have hX (i : Fin T) : Measurable (X i) :=
    (measurable_clippedSpread lambda).comp (hY i)
  have hXrange (i : Fin T) : ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc 0 lambda⁻¹ :=
    ae_clippedSpread_mem_Icc hlambda (hYnonneg i)
  have h := mgf_centeredScalarEmpiricalMean_le
    hT X (iIndepFun_clippedSpread Y hIndep lambda)
      hX hXrange (inv_nonneg.mpr hlambda.le) t
  change mgf (centeredClippedSpreadEmpiricalMean mu lambda Y) mu t ≤ _ at h
  refine h.trans_eq ?_
  congr 1
  field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne', hlambda.ne']
  ring

/-- Optimized Markov--Chernoff tail for the centered clipped-score empirical
mean.  Its exponent is `-2 T lambda^2 epsilon^2`. -/
theorem measure_centeredClippedSpreadEmpiricalMean_ge_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (Y : Fin T → Omega → ℝ)
    (hIndep : iIndepFun Y mu)
    (hY : ∀ i, Measurable (Y i))
    (hYnonneg : ∀ i, ∀ᵐ omega ∂mu, 0 ≤ Y i omega)
    {lambda epsilon : ℝ} (hlambda : 0 < lambda)
    (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤
        centeredClippedSpreadEmpiricalMean mu lambda Y omega} ≤
      Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2) := by
  let X : Fin T → Omega → ℝ :=
    fun i omega ↦ clippedSpread lambda (Y i omega)
  have hX (i : Fin T) : Measurable (X i) :=
    (measurable_clippedSpread lambda).comp (hY i)
  have hXrange (i : Fin T) : ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc 0 lambda⁻¹ :=
    ae_clippedSpread_mem_Icc hlambda (hYnonneg i)
  have h := measure_centeredScalarEmpiricalMean_ge_le
    hT X (iIndepFun_clippedSpread Y hIndep lambda)
      hX hXrange (inv_pos.mpr hlambda) hepsilon
  change mu.real {omega | epsilon ≤
      centeredClippedSpreadEmpiricalMean mu lambda Y omega} ≤ _ at h
  refine h.trans_eq ?_
  congr 1
  field_simp [hlambda.ne']
  ring

/-- Two-sided clipped-score tail used for a later finite-net union bound. -/
theorem measure_abs_centeredClippedSpreadEmpiricalMean_ge_le
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (Y : Fin T → Omega → ℝ)
    (hIndep : iIndepFun Y mu)
    (hY : ∀ i, Measurable (Y i))
    (hYnonneg : ∀ i, ∀ᵐ omega ∂mu, 0 ≤ Y i omega)
    {lambda epsilon : ℝ} (hlambda : 0 < lambda)
    (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | epsilon ≤
        |centeredClippedSpreadEmpiricalMean mu lambda Y omega|} ≤
      2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2) := by
  let X : Fin T → Omega → ℝ :=
    fun i omega ↦ clippedSpread lambda (Y i omega)
  have hX (i : Fin T) : Measurable (X i) :=
    (measurable_clippedSpread lambda).comp (hY i)
  have hXrange (i : Fin T) : ∀ᵐ omega ∂mu,
      X i omega ∈ Set.Icc 0 lambda⁻¹ :=
    ae_clippedSpread_mem_Icc hlambda (hYnonneg i)
  have h := measure_abs_centeredScalarEmpiricalMean_ge_le
    hT X (iIndepFun_clippedSpread Y hIndep lambda)
      hX hXrange (inv_pos.mpr hlambda) hepsilon
  change mu.real {omega | epsilon ≤
      |centeredClippedSpreadEmpiricalMean mu lambda Y omega|} ≤ _ at h
  refine h.trans_eq ?_
  congr 2
  field_simp [hlambda.ne']
  ring

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
