import TomographyOracleCore.Candidate2ClippedScoreMGF

/-!
# Finite-net concentration for the clipped spread process

This module performs only finite union bounds.  A finite set of directions and
an explicit covering witness are inputs; no sphere covering-number theorem is
assumed.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped BigOperators RealInnerProductSpace

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

/-- Union bound for a finite family of independent clipped-score empirical
means.  The cardinality of the supplied direction set remains explicit. -/
theorem measure_exists_mem_abs_centeredClippedSpreadEmpiricalMean_ge_le
    {Omega Direction : Type*}
    [MeasurableSpace Omega]
    {mu : Measure Omega} [IsProbabilityMeasure mu]
    {T : ℕ} (hT : 0 < T) (net : Finset Direction)
    (Y : Direction → Fin T → Omega → ℝ)
    (hIndep : ∀ u ∈ net, iIndepFun (Y u) mu)
    (hY : ∀ u ∈ net, ∀ i, Measurable (Y u i))
    (hYnonneg : ∀ u ∈ net, ∀ i, ∀ᵐ omega ∂mu, 0 ≤ Y u i omega)
    {lambda epsilon : ℝ} (hlambda : 0 < lambda)
    (hepsilon : 0 ≤ epsilon) :
    mu.real {omega | ∃ u ∈ net,
        epsilon ≤ |centeredClippedSpreadEmpiricalMean
          mu lambda (Y u) omega|} ≤
      (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  let bad : Direction → Set Omega := fun u =>
    {omega | epsilon ≤
      |centeredClippedSpreadEmpiricalMean mu lambda (Y u) omega|}
  have hset :
      {omega | ∃ u ∈ net,
        epsilon ≤ |centeredClippedSpreadEmpiricalMean
          mu lambda (Y u) omega|} =
        ⋃ u ∈ net, bad u := by
    ext omega
    simp [bad]
  rw [hset]
  calc
    mu.real (⋃ u ∈ net, bad u) ≤
        ∑ u ∈ net, mu.real (bad u) :=
      measureReal_biUnion_finset_le net bad
    _ ≤ ∑ _u ∈ net,
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
      exact Finset.sum_le_sum fun u hu =>
        measure_abs_centeredClippedSpreadEmpiricalMean_ge_le
          hT (Y u) (hIndep u hu) (hY u hu) (hYnonneg u hu)
            hlambda hepsilon
    _ = (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
      simp [nsmul_eq_mul]

section Directional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Squared directional observations preserve independence of vector-valued
sample coordinates. -/
theorem iIndepFun_directionalSquares
    {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} {T : ℕ} (Z : Fin T → Omega → E)
    (hIndep : iIndepFun Z mu) (u : E) :
    iIndepFun (fun i omega => ⟪Z i omega, u⟫_ℝ ^ 2) mu := by
  simpa [Function.comp_def] using
    hIndep.comp (fun _i x => ⟪x, u⟫_ℝ ^ 2) (fun _i => by fun_prop)

/-- Measurability of squared directional observations. -/
theorem measurable_directionalSquare
    {Omega : Type*} [MeasurableSpace Omega]
    {Z : Omega → E} (hZ : Measurable Z) (u : E) :
    Measurable (fun omega => ⟪Z omega, u⟫_ℝ ^ 2) := by
  fun_prop

/-- Identically distributed vector observations have the same clipped
directional expectation. -/
theorem integral_clippedDirectionalSquare_eq_of_identDistrib
    {Omega : Type*} [MeasurableSpace Omega]
    {sampleLaw : Measure Omega} {populationLaw : Measure E}
    {Z : Omega → E} (hIdent : IdentDistrib Z id sampleLaw populationLaw)
    (lambda : ℝ) (u : E) :
    (∫ omega, clippedSpread lambda (⟪Z omega, u⟫_ℝ ^ 2) ∂sampleLaw) =
      ∫ x, clippedSpread lambda (⟪x, u⟫_ℝ ^ 2) ∂populationLaw := by
  have hMeas : Measurable
      (fun x : E => clippedSpread lambda (⟪x, u⟫_ℝ ^ 2)) := by
    exact (measurable_clippedSpread lambda).comp
      (measurable_directionalSquare measurable_id u)
  simpa only [Function.comp_apply, id_eq] using
    (hIdent.comp hMeas).integral_eq

/-- For identically distributed coordinates, the abstract centered clipped
empirical mean is the directional spread mean minus its population clipped
expectation. -/
theorem centeredClippedSpreadEmpiricalMean_directional_eq
    {Omega : Type*} [MeasurableSpace Omega]
    {sampleLaw : Measure Omega} {populationLaw : Measure E}
    {T : ℕ} (hT : 0 < T) (Z : Fin T → Omega → E)
    (hIdent : ∀ i, IdentDistrib (Z i) id sampleLaw populationLaw)
    (lambda : ℝ) (u : E) (omega : Omega) :
    centeredClippedSpreadEmpiricalMean sampleLaw lambda
        (fun i omega => ⟪Z i omega, u⟫_ℝ ^ 2) omega =
      directionalSpreadMean lambda (fun i => Z i omega) u -
        ∫ x, clippedSpread lambda (⟪x, u⟫_ℝ ^ 2) ∂populationLaw := by
  have hmean (i : Fin T) :
      (∫ z, clippedSpread lambda (⟪Z i z, u⟫_ℝ ^ 2) ∂sampleLaw) =
        ∫ x, clippedSpread lambda (⟪x, u⟫_ℝ ^ 2) ∂populationLaw :=
    integral_clippedDirectionalSquare_eq_of_identDistrib
      (hIdent i) lambda u
  unfold centeredClippedSpreadEmpiricalMean centeredScalarEmpiricalMean
  unfold directionalSpreadMean spreadMean empiricalMean directionalSquares
  simp_rw [hmean]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp [show (T : ℝ) ≠ 0 by exact_mod_cast hT.ne']

/-- Exact bridge from population-centered spread to the independently
centered clipped empirical mean.  The discrepancy is precisely the verified
directional clipping bias. -/
theorem centeredDirectionalSpread_eq_centeredClipped_sub_bias
    {Omega : Type*} [MeasurableSpace Omega]
    {sampleLaw : Measure Omega} {populationLaw : Measure E}
    {T : ℕ} (hT : 0 < T) (Z : Fin T → Omega → E)
    (hIdent : ∀ i, IdentDistrib (Z i) id sampleLaw populationLaw)
    (lambda : ℝ) (u : E)
    (hRaw : Integrable (fun x : E => ⟪x, u⟫_ℝ ^ 2) populationLaw)
    (hClip : Integrable
      (fun x : E => clippedSpread lambda (⟪x, u⟫_ℝ ^ 2)) populationLaw)
    (omega : Omega) :
    centeredDirectionalSpread populationLaw lambda
        (fun i => Z i omega) u =
      centeredClippedSpreadEmpiricalMean sampleLaw lambda
          (fun i z => ⟪Z i z, u⟫_ℝ ^ 2) omega -
        directionalClippingBias populationLaw lambda u := by
  rw [centeredClippedSpreadEmpiricalMean_directional_eq
    hT Z hIdent lambda u omega]
  unfold centeredDirectionalSpread directionalClippingBias
  rw [integral_sub hRaw hClip]
  ring

/-- A clipped squared marginal is integrable under every finite measure. -/
theorem integrable_clippedDirectionalSquare
    {populationLaw : Measure E} [IsFiniteMeasure populationLaw]
    {lambda : ℝ} (hlambda : 0 < lambda) (u : E) :
    Integrable
      (fun x : E => clippedSpread lambda (⟪x, u⟫_ℝ ^ 2))
      populationLaw := by
  apply Integrable.of_mem_Icc 0 lambda⁻¹
  · exact ((measurable_clippedSpread lambda).comp
      (measurable_directionalSquare measurable_id u)).aemeasurable
  · exact ae_clippedSpread_mem_Icc hlambda
      (Filter.Eventually.of_forall fun _x => sq_nonneg _)

/-- Directional specialization of the finite clipped-score union bound. -/
theorem measure_exists_mem_abs_centeredDirectionalClipped_ge_le
    {Omega : Type*} [MeasurableSpace Omega]
    {sampleLaw : Measure Omega} [IsProbabilityMeasure sampleLaw]
    {T : ℕ} (hT : 0 < T) (net : Finset E)
    (Z : Fin T → Omega → E) (hIndep : iIndepFun Z sampleLaw)
    (hZ : ∀ i, Measurable (Z i))
    {lambda epsilon : ℝ} (hlambda : 0 < lambda)
    (hepsilon : 0 ≤ epsilon) :
    sampleLaw.real {omega | ∃ u ∈ net,
        epsilon ≤ |centeredClippedSpreadEmpiricalMean sampleLaw lambda
          (fun i omega => ⟪Z i omega, u⟫_ℝ ^ 2) omega|} ≤
      (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  apply measure_exists_mem_abs_centeredClippedSpreadEmpiricalMean_ge_le
    hT net (fun u i omega => ⟪Z i omega, u⟫_ℝ ^ 2)
      (fun _u _hu => iIndepFun_directionalSquares Z hIndep _)
      (fun u _hu i => measurable_directionalSquare (hZ i) u)
      (fun _u _hu _i => Filter.Eventually.of_forall fun _omega => sq_nonneg _)
      hlambda hepsilon

/-- Full finite-net transfer for the population-centered clipped spread
process.  The theorem assumes only an explicit finite set and an explicit
covering witness.  The event is intersected with the deterministic sample-norm
bound required by the verified Lipschitz theorem.

At each net point, `biasBound` pays for centering at the unclipped population
quadratic form.  The final probability contains no hidden covering-number
claim: its prefactor is exactly `net.card`. -/
theorem measure_unitSphere_centeredDirectionalSpread_ge_le_of_finiteNet
    [CompleteSpace E] [SecondCountableTopology E]
    {Omega : Type*} [MeasurableSpace Omega]
    {sampleLaw : Measure Omega} [IsProbabilityMeasure sampleLaw]
    {populationLaw : Measure E} [IsProbabilityMeasure populationLaw]
    (hpopulation : MemLp id 2 populationLaw)
    {T : ℕ} (hT : 0 < T) (Z : Fin T → Omega → E)
    (hIndep : iIndepFun Z sampleLaw)
    (hZ : ∀ i, Measurable (Z i))
    (hIdent : ∀ i, IdentDistrib (Z i) id sampleLaw populationLaw)
    (net : Finset E)
    {eta : ℝ}
    (hcover : ∀ u : E, ‖u‖ = 1 →
      ∃ v ∈ net, ‖v‖ = 1 ∧ ‖u - v‖ ≤ eta)
    {q lambda epsilon biasBound : ℝ}
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon)
    (hbias : ∀ v ∈ net,
      directionalClippingBias populationLaw lambda v ≤ biasBound) :
    sampleLaw.real {omega |
      (∀ i, ‖Z i omega‖ ^ 2 ≤ q) ∧
      ∃ u : E, ‖u‖ = 1 ∧
        epsilon + biasBound +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          |centeredDirectionalSpread populationLaw lambda
            (fun i => Z i omega) u|} ≤
      (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  let clippedCentered : Omega → E → ℝ := fun omega u =>
    centeredClippedSpreadEmpiricalMean sampleLaw lambda
      (fun i z => ⟪Z i z, u⟫_ℝ ^ 2) omega
  let badNet : Set Omega :=
    {omega | ∃ v ∈ net, epsilon ≤ |clippedCentered omega v|}
  have hsubset :
      {omega |
        (∀ i, ‖Z i omega‖ ^ 2 ≤ q) ∧
        ∃ u : E, ‖u‖ = 1 ∧
          epsilon + biasBound +
              2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
            |centeredDirectionalSpread populationLaw lambda
              (fun i => Z i omega) u|} ⊆ badNet := by
    intro omega homega
    rcases homega with ⟨hnorm, u, hu, hlarge⟩
    obtain ⟨v, hvnet, hv, huv⟩ := hcover u hu
    have htransfer := abs_centeredDirectionalSpread_le_of_nearby_unit
      hpopulation hT hlambda (fun i => Z i omega) hnorm
        u v hu hv huv
    have hnetLarge : epsilon + biasBound ≤
        |centeredDirectionalSpread populationLaw lambda
          (fun i => Z i omega) v| := by
      linarith
    have hRaw : Integrable (fun x : E => ⟪x, v⟫_ℝ ^ 2)
        populationLaw := by
      simpa only [id_eq] using
        (hpopulation.inner_const v).integrable_sq
    have hClip : Integrable
        (fun x : E => clippedSpread lambda (⟪x, v⟫_ℝ ^ 2))
        populationLaw :=
      integrable_clippedDirectionalSquare hlambda v
    have hbridge :=
      centeredDirectionalSpread_eq_centeredClipped_sub_bias
        hT Z hIdent lambda v hRaw hClip omega
    have hbiasNonneg :
        0 ≤ directionalClippingBias populationLaw lambda v :=
      directionalClippingBias_nonneg populationLaw hlambda v
    have habs :
        |centeredDirectionalSpread populationLaw lambda
            (fun i => Z i omega) v| ≤
          |clippedCentered omega v| +
            directionalClippingBias populationLaw lambda v := by
      rw [hbridge]
      dsimp only [clippedCentered]
      calc
        |centeredClippedSpreadEmpiricalMean sampleLaw lambda
              (fun i z => ⟪Z i z, v⟫_ℝ ^ 2) omega -
            directionalClippingBias populationLaw lambda v| ≤
            |centeredClippedSpreadEmpiricalMean sampleLaw lambda
              (fun i z => ⟪Z i z, v⟫_ℝ ^ 2) omega| +
              |directionalClippingBias populationLaw lambda v| :=
          abs_sub _ _
        _ = |centeredClippedSpreadEmpiricalMean sampleLaw lambda
              (fun i z => ⟪Z i z, v⟫_ℝ ^ 2) omega| +
              directionalClippingBias populationLaw lambda v := by
          rw [abs_of_nonneg hbiasNonneg]
    have hclipLarge : epsilon ≤ |clippedCentered omega v| := by
      have hbiasUpper := hbias v hvnet
      linarith
    exact ⟨v, hvnet, hclipLarge⟩
  calc
    sampleLaw.real {omega |
        (∀ i, ‖Z i omega‖ ^ 2 ≤ q) ∧
        ∃ u : E, ‖u‖ = 1 ∧
          epsilon + biasBound +
              2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
            |centeredDirectionalSpread populationLaw lambda
              (fun i => Z i omega) u|} ≤
        sampleLaw.real badNet := measureReal_mono hsubset
    _ ≤ (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
      dsimp only [badNet, clippedCentered]
      exact measure_exists_mem_abs_centeredDirectionalClipped_ge_le
        hT net Z hIndep hZ hlambda hepsilon

/-- Almost-sure sample-norm specialization of the finite-net theorem.  This
removes the norm-bound conjunct from the event without changing its
probability.  Fixed-norm product samples satisfy the added premise
coordinatewise. -/
theorem measure_unitSphere_centeredDirectionalSpread_ge_le_of_finiteNet_of_ae_norm
    [CompleteSpace E] [SecondCountableTopology E]
    {Omega : Type*} [MeasurableSpace Omega]
    {sampleLaw : Measure Omega} [IsProbabilityMeasure sampleLaw]
    {populationLaw : Measure E} [IsProbabilityMeasure populationLaw]
    (hpopulation : MemLp id 2 populationLaw)
    {T : ℕ} (hT : 0 < T) (Z : Fin T → Omega → E)
    (hIndep : iIndepFun Z sampleLaw)
    (hZ : ∀ i, Measurable (Z i))
    (hIdent : ∀ i, IdentDistrib (Z i) id sampleLaw populationLaw)
    (net : Finset E)
    {eta : ℝ}
    (hcover : ∀ u : E, ‖u‖ = 1 →
      ∃ v ∈ net, ‖v‖ = 1 ∧ ‖u - v‖ ≤ eta)
    {q lambda epsilon biasBound : ℝ}
    (hnorm : ∀ i, ∀ᵐ omega ∂sampleLaw, ‖Z i omega‖ ^ 2 ≤ q)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon)
    (hbias : ∀ v ∈ net,
      directionalClippingBias populationLaw lambda v ≤ biasBound) :
    sampleLaw.real {omega |
      ∃ u : E, ‖u‖ = 1 ∧
        epsilon + biasBound +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          |centeredDirectionalSpread populationLaw lambda
            (fun i => Z i omega) u|} ≤
      (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  let bad : Set Omega := {omega |
    ∃ u : E, ‖u‖ = 1 ∧
      epsilon + biasBound +
          2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
        |centeredDirectionalSpread populationLaw lambda
          (fun i => Z i omega) u|}
  let restrictedBad : Set Omega := {omega |
    (∀ i, ‖Z i omega‖ ^ 2 ≤ q) ∧
    ∃ u : E, ‖u‖ = 1 ∧
      epsilon + biasBound +
          2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
        |centeredDirectionalSpread populationLaw lambda
          (fun i => Z i omega) u|}
  have hnormAll : ∀ᵐ omega ∂sampleLaw,
      ∀ i, ‖Z i omega‖ ^ 2 ≤ q :=
    Filter.eventually_all.mpr hnorm
  have hsets : bad =ᵐ[sampleLaw] restrictedBad := by
    filter_upwards [hnormAll] with omega homega
    change
      (∃ u : E, ‖u‖ = 1 ∧
        epsilon + biasBound +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          |centeredDirectionalSpread populationLaw lambda
            (fun i => Z i omega) u|) =
      ((∀ i, ‖Z i omega‖ ^ 2 ≤ q) ∧
        ∃ u : E, ‖u‖ = 1 ∧
          epsilon + biasBound +
              2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
            |centeredDirectionalSpread populationLaw lambda
              (fun i => Z i omega) u|)
    apply propext
    constructor
    · exact fun h => ⟨homega, h⟩
    · exact fun h => h.2
  change sampleLaw.real bad ≤ _
  rw [measureReal_congr hsets]
  change sampleLaw.real {omega |
      (∀ i, ‖Z i omega‖ ^ 2 ≤ q) ∧
      ∃ u : E, ‖u‖ = 1 ∧
        epsilon + biasBound +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          |centeredDirectionalSpread populationLaw lambda
            (fun i => Z i omega) u|} ≤ _
  exact measure_unitSphere_centeredDirectionalSpread_ge_le_of_finiteNet
    hpopulation hT Z hIndep hZ hIdent net hcover
      hlambda hepsilon hbias

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [BorelSpace E] in
/-- A coordinate of the canonical finite product sample is identically
distributed with the population identity map. -/
theorem identDistrib_productCoordinate_id
    {T : ℕ} (populationLaw : Measure E)
    [IsProbabilityMeasure populationLaw] (i : Fin T) :
    IdentDistrib (productCoordinate (E := E) i) id
      (Measure.pi fun _ : Fin T => populationLaw) populationLaw := by
  refine IdentDistrib.mk
    (measurable_productCoordinate i).aemeasurable
    measurable_id.aemeasurable ?_
  rw [map_productCoordinate_eq, Measure.map_id]

omit [InnerProductSpace ℝ E] [BorelSpace E] in
/-- An almost-sure population norm bound pulls back to every coordinate of
the canonical finite product sample. -/
theorem ae_productCoordinate_norm_sq_le
    {T : ℕ} (populationLaw : Measure E)
    [IsProbabilityMeasure populationLaw] {q : ℝ}
    (hnorm : ∀ᵐ x ∂populationLaw, ‖x‖ ^ 2 = q) (i : Fin T) :
    ∀ᵐ omega ∂(Measure.pi fun _ : Fin T => populationLaw),
      ‖productCoordinate (E := E) i omega‖ ^ 2 ≤ q := by
  have hi : ∀ᵐ omega ∂(Measure.pi fun _ : Fin T => populationLaw),
      ‖Function.eval i omega‖ ^ 2 = q :=
    (measurePreserving_eval (fun _ : Fin T => populationLaw) i).quasiMeasurePreserving.ae hnorm
  filter_upwards [hi] with omega homega
  simpa only [productCoordinate] using homega.le

/-- Canonical finite-product specialization.  In addition to an explicit
finite net and covering witness, it assumes only a fixed population norm and
the verified `L6--L2` marginal condition.  The clipping-bias term is therefore
fully instantiated as
`lambda^2 * kappa^6 * ‖populationCovariance populationLaw‖^3`.

No estimate for the size of `net` is asserted here. -/
theorem measure_pi_unitSphere_centeredDirectionalSpread_ge_le_of_fixedNorm_finiteNet
    [CompleteSpace E] [SecondCountableTopology E]
    (populationLaw : Measure E) [IsProbabilityMeasure populationLaw]
    {T : ℕ} (hT : 0 < T)
    (net : Finset E) {eta q kappa lambda epsilon : ℝ}
    (hcover : ∀ u : E, ‖u‖ = 1 →
      ∃ v ∈ net, ‖v‖ = 1 ∧ ‖u - v‖ ≤ eta)
    (hnetUnit : ∀ v ∈ net, ‖v‖ = 1)
    (hnorm : ∀ᵐ x ∂populationLaw, ‖x‖ ^ 2 = q)
    (hL6 : HasL6L2Marginals populationLaw kappa)
    (hlambda : 0 < lambda) (hepsilon : 0 ≤ epsilon) :
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
      ∃ u : E, ‖u‖ = 1 ∧
        epsilon +
              lambda ^ 2 * kappa ^ 6 *
                ‖populationCovariance populationLaw‖ ^ 3 +
            2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
          |centeredDirectionalSpread populationLaw lambda omega u|} ≤
      (net.card : ℝ) *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  have h :=
    measure_unitSphere_centeredDirectionalSpread_ge_le_of_finiteNet_of_ae_norm
      (fixedNorm_memLp hnorm 2) hT
      (fun i => productCoordinate (E := E) i)
      (iIndepFun_productCoordinate populationLaw)
      (fun i => measurable_productCoordinate i)
      (fun i => identDistrib_productCoordinate_id populationLaw i)
      net hcover
      (fun i => ae_productCoordinate_norm_sq_le populationLaw hnorm i)
      hlambda hepsilon
      (fun v hv => fixedNorm_directionalClippingBias_le_covarianceScale
        hnorm hL6 hlambda v (hnetUnit v hv))
  simpa only [productCoordinate] using h

end Directional

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
