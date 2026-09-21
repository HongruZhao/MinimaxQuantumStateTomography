import TomographyOracleCore.SharedHaarFanoAssembly
import TomographyOracleCore.KernelConditionalKL

namespace TomographyOracleCore.Revision.NonadaptiveFano

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal
noncomputable section

/-! The information-to-testing reduction of paper Lemma 13. The context
`Z` is the shared rotation and public design seed. The same context law is
used for every label, so independence of the label is built into the law.
Outcomes and contexts are arbitrary measurable spaces, with a countably
generated outcome space for measurable Radon--Nikodym derivatives. A
decoder is an arbitrary Markov kernel and may use its own randomness. -/

/-- Extended Pearson divergence of two kernel fibres. Singular fibres have
infinite divergence; hence a finite budget never hides an absolute-
continuity or integrability premise. -/
def kernelChiSquare {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (K Q : Kernel Z Y) (z : Z) : ℝ≥0∞ := by
  classical
  exact if K z ≪ Q z then
    ∫⁻ y, ENNReal.ofReal (((K.rnDeriv Q z y).toReal - 1) ^ 2) ∂Q z
  else ∞

theorem measurable_kernelChiSquare {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (K Q : Kernel Z Y) [IsFiniteKernel K] [IsFiniteKernel Q] :
    Measurable (kernelChiSquare K Q) := by
  have h : Measurable (fun z =>
      ∫⁻ y, ENNReal.ofReal (((K.rnDeriv Q z y).toReal - 1) ^ 2) ∂Q z) := by
    apply Measurable.lintegral_kernel_prod_right
    fun_prop
  exact Measurable.ite (Kernel.measurableSet_absolutelyContinuous K Q)
    h measurable_const

/-- The averaged conditional Pearson divergence bounds joint KL, without
assuming pointwise finiteness or absolute continuity. -/
theorem jointKL_le_average_chiSquare {Z Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace Y]
    [MeasurableSpace.CountablyGenerated Y]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (K Q : Kernel Z Y) [IsMarkovKernel K] [IsMarkovKernel Q] :
    klDiv (mu ⊗ₘ K) (mu ⊗ₘ Q) ≤
      ∫⁻ z, kernelChiSquare K Q z ∂mu := by
  classical
  by_cases htop : (∫⁻ z, kernelChiSquare K Q z ∂mu) = ∞
  · rw [htop]; exact le_top
  have hac : ∀ᵐ z ∂mu, K z ≪ Q z := by
    filter_upwards [ae_lt_top (measurable_kernelChiSquare K Q) htop] with z hz
    by_contra h
    simp [kernelChiSquare, h] at hz
  let f : Z → Y → ℝ≥0∞ := K.rnDeriv Q
  have hf : Measurable (Function.uncurry f) := K.measurable_rnDeriv Q
  have hjoint : mu ⊗ₘ K =
      (mu ⊗ₘ Q).withDensity (fun p => f p.1 p.2) := by
    calc
      mu ⊗ₘ K = mu ⊗ₘ Q.withDensity f := by
        apply Measure.compProd_congr
        filter_upwards [hac] with z hz
        exact (Kernel.withDensity_rnDeriv_eq hz).symm
      _ = _ := Measure.compProd_withDensity hf
  have hjointac : mu ⊗ₘ K ≪ mu ⊗ₘ Q :=
    Measure.AbsolutelyContinuous.compProd_right hac
  have hrn : (mu ⊗ₘ K).rnDeriv (mu ⊗ₘ Q) =ᵐ[mu ⊗ₘ Q]
      fun p => f p.1 p.2 := by
    rw [hjoint]
    exact Measure.rnDeriv_withDensity (mu ⊗ₘ Q) hf
  rw [klDiv_eq_lintegral_klFun_of_ac hjointac]
  calc
    _ = ∫⁻ p, ENNReal.ofReal (klFun ((f p.1 p.2).toReal)) ∂mu ⊗ₘ Q := by
      apply lintegral_congr_ae
      filter_upwards [hrn] with p hp
      rw [hp]
    _ ≤ ∫⁻ p, ENNReal.ofReal (((f p.1 p.2).toReal - 1) ^ 2) ∂mu ⊗ₘ Q := by
      apply lintegral_mono
      intro p
      exact ENNReal.ofReal_le_ofReal (klFun_le_sq_sub_one ENNReal.toReal_nonneg)
    _ = ∫⁻ z, ∫⁻ y, ENNReal.ofReal (((f z y).toReal - 1) ^ 2) ∂Q z ∂mu := by
      rw [Measure.lintegral_compProd]
      fun_prop
    _ = ∫⁻ z, kernelChiSquare K Q z ∂mu := by
      apply lintegral_congr_ae
      filter_upwards [hac] with z hz
      simp [kernelChiSquare, hz, f]

/-- Run any randomized decoder on a family of full transcript measures. -/
def decodedLaw {N : ℕ} {Record : Type*} [MeasurableSpace Record]
    (P : Fin N → Measure Record) (decode : Kernel Record (Fin N)) :
    Kernel (Fin N) (Fin N) where
  toFun x := decode ∘ₘ P x
  measurable' := Measurable.of_discrete

instance decodedLaw_markov {N : ℕ} {Record : Type*} [MeasurableSpace Record]
    (P : Fin N → Measure Record) [∀ x, IsProbabilityMeasure (P x)]
    (decode : Kernel Record (Fin N)) [IsMarkovKernel decode] :
    IsMarkovKernel (decodedLaw P decode) := by
  constructor
  intro x
  change IsProbabilityMeasure (decode ∘ₘ P x)
  infer_instance

/-- The literal uniform-prior probability that the decoded label is wrong. -/
def labelError {N : ℕ} (K : Kernel (Fin N) (Fin N)) : ℝ :=
  (N : ℝ)⁻¹ * ∑ x, (K x).real {y | y ≠ x}

/-- Fano for arbitrary observation spaces and randomized decoders, from
reference KL. The finite experiment is the decoded label, not the original
outcome space; data processing justifies this reduction. -/
theorem fano_of_referenceKL {N : ℕ} [NeZero N]
    {Record : Type*} [MeasurableSpace Record]
    (P : Fin N → Measure Record) [∀ x, IsProbabilityMeasure (P x)]
    (Q : Measure Record) [IsProbabilityMeasure Q]
    (decode : Kernel Record (Fin N)) [IsMarkovKernel decode]
    (B : ℝ) (hB : 0 ≤ B) (hN : 2 ≤ N)
    (hKL : ∀ x, klDiv (P x) Q ≤ ENNReal.ofReal B) :
    1 - (B + Real.log 2) / Real.log N ≤ labelError (decodedLaw P decode) := by
  let K := decodedLaw P decode
  let q := decode ∘ₘ Q
  let : IsProbabilityMeasure q := by dsimp [q]; infer_instance
  have hdecoded (x : Fin N) : klDiv (K x) q ≤ ENNReal.ofReal B :=
    (klDiv_comp_right_le (P x) Q decode).trans (hKL x)
  have hfinite (x : Fin N) : klDiv (K x) q ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdecoded x)
  let J := FiniteUniformJoint.ofMarkovKernel K
  have hinfo : J.posteriorKLSum ≤ B := by
    apply FiniteUniformJoint.ofMarkovKernel_posteriorKLSum_le_klDiv_reference K q B hfinite
    intro x
    simpa [ENNReal.toReal_ofReal hB] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (hdecoded x)
  have hpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  have hfano := J.fanoErrorLower_le_errorProbability id (by simpa using hN)
  have hidentity := J.posteriorKLEntropyIdentity_proved id
  have hmono : 1 - (B + Real.log 2) / Real.log N ≤
      fanoErrorLower (J.entropyChainInformation id) (Real.log N) := by
    unfold fanoErrorLower
    have hi : J.entropyChainInformation id ≤ B := by rw [← hidentity]; exact hinfo
    have hd : (J.entropyChainInformation id + Real.log 2) / Real.log N ≤
        (B + Real.log 2) / Real.log N :=
      div_le_div_of_nonneg_right (by linarith) hpos.le
    linarith
  have herr : (J.toPosteriorExperiment id).errorProbability = labelError K := by
    simpa [J, labelError] using FiniteUniformJoint.ofMarkovKernel_errorProbability_id_eq K
  rw [herr] at hfano
  exact hmono.trans (by simpa using hfano)

/-- Law-level form of paper Lemma 13, valid on arbitrary context and outcome
spaces. All budgets are one-copy chi-square budgets; neither tensorization
nor Fano nor a multi-copy information bound is assumed. -/
theorem nonadaptive_fano_of_chiSquare {N T : ℕ} [NeZero N]
    {Z Outcome : Type*} [MeasurableSpace Z] [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (mu : Measure Z) [IsProbabilityMeasure mu]
    (shots : Fin N → Fin T → Kernel Z Outcome)
    (referenceShots : Fin T → Kernel Z Outcome)
    [∀ x t, IsMarkovKernel (shots x t)]
    [∀ t, IsMarkovKernel (referenceShots t)]
    (records : Fin N → Kernel Z (Fin T → Outcome))
    (referenceRecord : Kernel Z (Fin T → Outcome))
    [∀ x, IsMarkovKernel (records x)] [IsMarkovKernel referenceRecord]
    (hprod : ∀ x z, records x z = Measure.pi fun t => shots x t z)
    (hrefprod : ∀ z, referenceRecord z = Measure.pi fun t => referenceShots t z)
    (decode : Kernel (Z × (Fin T → Outcome)) (Fin N)) [IsMarkovKernel decode]
    (budget : ℝ) (hbudget : 0 ≤ budget) (hN : 2 ≤ N)
    (hone : ∀ x t, (∫⁻ z, kernelChiSquare (shots x t) (referenceShots t) z ∂mu)
      ≤ ENNReal.ofReal budget) :
    1 - ((T : ℝ) * budget + Real.log 2) / Real.log N ≤
      labelError (decodedLaw (fun x => mu ⊗ₘ records x) decode) := by
  apply fano_of_referenceKL (fun x => mu ⊗ₘ records x)
    (mu ⊗ₘ referenceRecord) decode ((T : ℝ) * budget) (by positivity) hN
  intro x
  rw [klDiv_sharedLatent_pi_eq_sum T mu (shots x) referenceShots
    (records x) referenceRecord (hprod x) hrefprod]
  calc
    _ ≤ ∑ t : Fin T, ENNReal.ofReal budget := by
      apply Finset.sum_le_sum
      intro t _
      exact (jointKL_le_average_chiSquare mu (shots x t) (referenceShots t)).trans (hone x t)
    _ = ENNReal.ofReal ((T : ℝ) * budget) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]

/-- Seedwise form of the paper lemma. A POVM fixed by any seed value
has the assumed Haar-averaged chi-square budget. Integrating the independent
seed is proved here, rather than included as a joint-information premise.
The kernels can be any outcome laws on a countably generated space. -/
theorem lemma13_laws {N T : ℕ} [NeZero N]
    {Orientation Seed Outcome : Type*}
    [MeasurableSpace Orientation] [MeasurableSpace Seed] [MeasurableSpace Outcome]
    [MeasurableSpace.CountablyGenerated Outcome]
    (rotation : Measure Orientation) [IsProbabilityMeasure rotation]
    (seed : Measure Seed) [IsProbabilityMeasure seed]
    (shots : Fin N → Fin T → Kernel (Orientation × Seed) Outcome)
    (referenceShots : Fin T → Kernel (Orientation × Seed) Outcome)
    [∀ x t, IsMarkovKernel (shots x t)]
    [∀ t, IsMarkovKernel (referenceShots t)]
    (records : Fin N → Kernel (Orientation × Seed) (Fin T → Outcome))
    (referenceRecord : Kernel (Orientation × Seed) (Fin T → Outcome))
    [∀ x, IsMarkovKernel (records x)] [IsMarkovKernel referenceRecord]
    (hprod : ∀ x z, records x z = Measure.pi fun t => shots x t z)
    (hrefprod : ∀ z, referenceRecord z = Measure.pi fun t => referenceShots t z)
    (decode : Kernel ((Orientation × Seed) × (Fin T → Outcome)) (Fin N))
    [IsMarkovKernel decode]
    (budget : ℝ) (hbudget : 0 ≤ budget) (hN : 2 ≤ N)
    (hone : ∀ x t r,
      (∫⁻ w, kernelChiSquare (shots x t) (referenceShots t) (w, r) ∂rotation)
        ≤ ENNReal.ofReal budget) :
    1 - ((T : ℝ) * budget + Real.log 2) / Real.log N ≤
      labelError (decodedLaw (fun x => (rotation.prod seed) ⊗ₘ records x) decode) := by
  apply nonadaptive_fano_of_chiSquare (rotation.prod seed) shots referenceShots
    records referenceRecord hprod hrefprod decode budget hbudget hN
  intro x t
  rw [lintegral_prod_symm _ (measurable_kernelChiSquare (shots x t) (referenceShots t)).aemeasurable]
  calc
    _ ≤ ∫⁻ _r, ENNReal.ofReal budget ∂seed := lintegral_mono (hone x t)
    _ = ENNReal.ofReal budget := by simp

end
end TomographyOracleCore.Revision.NonadaptiveFano
