import TomographyOracleCore.MathlibImports
import TomographyOracleCore.DecayUpper
import TomographyOracleCore.RobustNoise

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory

/-!
# From random/high-probability oracles to an expected oracle

The decay-class theorem consumes an oracle for expected trace error.  This
file derives that object from two more primitive inputs:

* a samplewise oracle with an integrable random noise level; or
* an oracle valid on a measurable high-probability event, together with the
  deterministic trace-loss cap on the exceptional event.

Thus the expected oracle is a proved bridge, not a conclusion-shaped
hypothesis.  A concentration theorem still has to supply the event or the
integrable noise bound for the concrete measurement ensemble.
-/

/-- Increasing the noise coefficient preserves an oracle bound. -/
theorem OracleBound.mono_noise
    {err noise₁ noise₂ : ℝ} {tail : ℕ → ℝ} {D : ℕ}
    (horacle : OracleBound err tail noise₁ D)
    (hnoise : noise₁ ≤ noise₂) :
    OracleBound err tail noise₂ D := by
  intro s hs1 hsD
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hscaled : noise₁ * (s : ℝ) ≤ noise₂ * (s : ℝ) :=
    mul_le_mul_of_nonneg_right hnoise hs
  exact (horacle s hs1 hsD).trans (by linarith)

/-- Integration preserves a simultaneous oracle when its random noise level
is integrable.  This is the direct route used when one has an expectation or
tail-integral bound for the forward error. -/
theorem expectedOracle_of_samplewise_random_noise
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error noise : Omega → ℝ) (tail : ℕ → ℝ) (D : ℕ)
    (herror : Integrable error mu) (hnoise : Integrable noise mu)
    (hsample : ∀ omega, OracleBound (error omega) tail (noise omega) D) :
    OracleBound (∫ omega, error omega ∂mu) tail
      (∫ omega, noise omega ∂mu) D := by
  intro s hs1 hsD
  let rhs : Omega → ℝ := fun omega =>
    4 * tail s + noise omega * (s : ℝ)
  have hconst : Integrable (fun _omega : Omega => 4 * tail s) mu :=
    integrable_const (4 * tail s)
  have hrhs : Integrable rhs mu := by
    dsimp [rhs]
    exact hconst.add (hnoise.mul_const (s : ℝ))
  have hmono : (∫ omega, error omega ∂mu) ≤ ∫ omega, rhs omega ∂mu := by
    apply integral_mono herror hrhs
    intro omega
    exact hsample omega s hs1 hsD
  have hrhs_integral :
      (∫ omega, rhs omega ∂mu) =
        4 * tail s + (∫ omega, noise omega ∂mu) * (s : ℝ) := by
    dsimp [rhs]
    rw [integral_add hconst (hnoise.mul_const (s : ℝ))]
    have hconst_integral :
        (∫ _omega : Omega, 4 * tail s ∂mu) = 4 * tail s := by
      simp [measureReal_def]
    have hnoise_integral :
        (∫ omega, noise omega * (s : ℝ) ∂mu) =
          (∫ omega, noise omega ∂mu) * (s : ℝ) :=
      integral_mul_const (s : ℝ) noise
    rw [hconst_integral, hnoise_integral]
  rw [hrhs_integral] at hmono
  exact hmono

/-- Expected-noise version of the preceding result.  A bound on the mean
random noise coefficient yields a deterministic expected oracle. -/
theorem expectedOracle_of_samplewise_random_noise_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error noise : Omega → ℝ) (tail : ℕ → ℝ) (D : ℕ)
    (herror : Integrable error mu) (hnoise : Integrable noise mu)
    (hsample : ∀ omega, OracleBound (error omega) tail (noise omega) D)
    (noiseBound : ℝ)
    (hnoiseMean : (∫ omega, noise omega ∂mu) ≤ noiseBound) :
    OracleBound (∫ omega, error omega ∂mu) tail noiseBound D :=
  (expectedOracle_of_samplewise_random_noise mu error noise tail D
    herror hnoise hsample).mono_noise hnoiseMean

/-- Generic good-event expectation inequality.  On the good event `good`,
`error ≤ goodBound`; everywhere, `error ≤ cap`.  The expected error is at
most `goodBound + cap * P(good^c)` whenever `goodBound` is nonnegative. -/
theorem integral_le_goodBound_add_cap_mul_badProbability
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error : Omega → ℝ) (good : Set Omega)
    (hgood_measurable : MeasurableSet good)
    (herror : Integrable error mu)
    (goodBound cap : ℝ) (hgoodBound : 0 ≤ goodBound)
    (hgood : ∀ omega ∈ good, error omega ≤ goodBound)
    (hcap : ∀ omega, error omega ≤ cap) :
    (∫ omega, error omega ∂mu) ≤
      goodBound + cap * mu.real goodᶜ := by
  let badIndicator : Omega → ℝ := goodᶜ.indicator (fun _ => 1)
  let envelope : Omega → ℝ := fun omega =>
    goodBound + cap * badIndicator omega
  have hone_integrable : Integrable (fun _omega : Omega => (1 : ℝ)) mu :=
    integrable_const 1
  have hbound_integrable :
      Integrable (fun _omega : Omega => goodBound) mu :=
    integrable_const goodBound
  have hbad_integrable : Integrable badIndicator mu := by
    dsimp [badIndicator]
    exact hone_integrable.indicator hgood_measurable.compl
  have henvelope_integrable : Integrable envelope mu := by
    dsimp [envelope]
    exact hbound_integrable.add (hbad_integrable.const_mul cap)
  have hpointwise : ∀ omega, error omega ≤ envelope omega := by
    intro omega
    by_cases homega : omega ∈ good
    · have hnotbad : omega ∉ goodᶜ := by simpa using homega
      simpa [envelope, badIndicator, Set.indicator_of_notMem hnotbad] using
        hgood omega homega
    · have hbad : omega ∈ goodᶜ := by simpa using homega
      have hcapOmega := hcap omega
      have hcap_le : cap ≤ goodBound + cap := by linarith
      simpa [envelope, badIndicator, Set.indicator_of_mem hbad] using
        hcapOmega.trans hcap_le
  have hmono := integral_mono herror henvelope_integrable hpointwise
  have henvelope_integral :
      (∫ omega, envelope omega ∂mu) =
        goodBound + cap * mu.real goodᶜ := by
    dsimp [envelope]
    rw [integral_add hbound_integrable (hbad_integrable.const_mul cap)]
    have hbound_integral :
        (∫ _omega : Omega, goodBound ∂mu) = goodBound := by
      simp [measureReal_def]
    have hcap_integral :
        (∫ omega, cap * badIndicator omega ∂mu) =
          cap * ∫ omega, badIndicator omega ∂mu :=
      integral_const_mul cap badIndicator
    have hindicator_integral :
        (∫ omega, badIndicator omega ∂mu) = mu.real goodᶜ := by
      simpa [badIndicator] using integral_indicator_const
        (μ := mu) (1 : ℝ) hgood_measurable.compl
    rw [hbound_integral, hcap_integral, hindicator_integral]
  rw [henvelope_integral] at hmono
  exact hmono

/-- If the bad-event probability is at most `delta`, the previous result has
the familiar `cap * delta` exceptional-event contribution. -/
theorem integral_le_goodBound_add_cap_mul_delta
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error : Omega → ℝ) (good : Set Omega)
    (hgood_measurable : MeasurableSet good)
    (herror : Integrable error mu)
    (goodBound cap delta : ℝ)
    (hgoodBound : 0 ≤ goodBound) (hcap_nonnegative : 0 ≤ cap)
    (hbad : mu.real goodᶜ ≤ delta)
    (hgood : ∀ omega ∈ good, error omega ≤ goodBound)
    (hcap : ∀ omega, error omega ≤ cap) :
    (∫ omega, error omega ∂mu) ≤ goodBound + cap * delta := by
  have hbase := integral_le_goodBound_add_cap_mul_badProbability
    mu error good hgood_measurable herror goodBound cap hgoodBound hgood hcap
  have hmul : cap * mu.real goodᶜ ≤ cap * delta :=
    mul_le_mul_of_nonneg_left hbad hcap_nonnegative
  nlinarith

/-- ENNReal formulation matching probability/concentration theorems in
mathlib. -/
theorem integral_le_goodBound_add_cap_mul_delta_of_measure_le
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error : Omega → ℝ) (good : Set Omega)
    (hgood_measurable : MeasurableSet good)
    (herror : Integrable error mu)
    (goodBound cap delta : ℝ)
    (hgoodBound : 0 ≤ goodBound) (hcap_nonnegative : 0 ≤ cap)
    (hdelta : 0 ≤ delta)
    (hbad : mu goodᶜ ≤ ENNReal.ofReal delta)
    (hgood : ∀ omega ∈ good, error omega ≤ goodBound)
    (hcap : ∀ omega, error omega ≤ cap) :
    (∫ omega, error omega ∂mu) ≤ goodBound + cap * delta := by
  apply integral_le_goodBound_add_cap_mul_delta mu error good
    hgood_measurable herror goodBound cap delta hgoodBound hcap_nonnegative
  · rw [measureReal_def]
    calc
      (mu goodᶜ).toReal ≤ (ENNReal.ofReal delta).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hbad
      _ = delta := ENNReal.toReal_ofReal hdelta
  · exact hgood
  · exact hcap

/-- A simultaneous oracle on a good event yields an expected simultaneous
oracle.  The exceptional contribution `cap * delta` is absorbed into the
linear-in-`s` noise term using `s ≥ 1`.

The hypotheses `tail ≥ 0` and `noise ≥ 0` ensure the good-event oracle right
side is nonnegative, as required by the generic expectation lemma. -/
theorem expectedOracle_of_good_event
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error : Omega → ℝ) (good : Set Omega)
    (hgood_measurable : MeasurableSet good)
    (herror : Integrable error mu)
    (tail : ℕ → ℝ) (noise cap delta : ℝ) (D : ℕ)
    (hnoise : 0 ≤ noise) (hcap_nonnegative : 0 ≤ cap)
    (hdelta : 0 ≤ delta)
    (htail : ∀ s, 1 ≤ s → s ≤ D → 0 ≤ tail s)
    (hbad : mu goodᶜ ≤ ENNReal.ofReal delta)
    (hgoodOracle : ∀ omega ∈ good,
      OracleBound (error omega) tail noise D)
    (hcap : ∀ omega, error omega ≤ cap) :
    OracleBound (∫ omega, error omega ∂mu) tail
      (noise + cap * delta) D := by
  intro s hs1 hsD
  let goodBound : ℝ := 4 * tail s + noise * (s : ℝ)
  have hs_nonnegative : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hgoodBound : 0 ≤ goodBound := by
    dsimp [goodBound]
    exact add_nonneg (mul_nonneg (by norm_num) (htail s hs1 hsD))
      (mul_nonneg hnoise hs_nonnegative)
  have hgood_s : ∀ omega ∈ good, error omega ≤ goodBound := by
    intro omega homega
    exact hgoodOracle omega homega s hs1 hsD
  have hexpect := integral_le_goodBound_add_cap_mul_delta_of_measure_le
    mu error good hgood_measurable herror goodBound cap delta hgoodBound
    hcap_nonnegative hdelta hbad hgood_s hcap
  have hdelta_absorb : cap * delta ≤ cap * delta * (s : ℝ) := by
    have hs_real : 1 ≤ (s : ℝ) := by exact_mod_cast hs1
    nlinarith [mul_nonneg hcap_nonnegative hdelta]
  dsimp [goodBound] at hexpect
  calc
    (∫ omega, error omega ∂mu)
        ≤ 4 * tail s + noise * (s : ℝ) + cap * delta := hexpect
    _ ≤ 4 * tail s + (noise + cap * delta) * (s : ℝ) := by
      nlinarith

/-- Trace-distance specialization: with deterministic cap `2` and a good
event oracle of noise `4 * eta`, the expected oracle has noise
`4 * (eta + delta / 2)`. -/
theorem expectedOracle_of_good_event_trace_cap
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (error : Omega → ℝ) (good : Set Omega)
    (hgood_measurable : MeasurableSet good)
    (herror : Integrable error mu)
    (tail : ℕ → ℝ) (eta delta : ℝ) (D : ℕ)
    (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (htail : ∀ s, 1 ≤ s → s ≤ D → 0 ≤ tail s)
    (hbad : mu goodᶜ ≤ ENNReal.ofReal delta)
    (hgoodOracle : ∀ omega ∈ good,
      OracleBound (error omega) tail (4 * eta) D)
    (hcap : ∀ omega, error omega ≤ 2) :
    OracleBound (∫ omega, error omega ∂mu) tail
      (4 * (eta + delta / 2)) D := by
  have h := expectedOracle_of_good_event mu error good hgood_measurable
    herror tail (4 * eta) 2 delta D (by positivity) (by norm_num) hdelta
    htail hbad hgoodOracle hcap
  convert h using 1
  ring

/-- Direct fixed-design class upper bound from state-dependent good events.

For every state, `randomError state` is the realized trace error under its own
probability law `mu state`.  The good-event oracle has noise `4 * eta`, its
failure probability is at most `delta`, and the trace loss is always at most
two.  The theorem first proves the expected oracle with effective scale
`eta + delta / 2`, then invokes the already verified integer/end-point decay
optimization and genuine class-risk infima. -/
theorem fixedDesignClassRisk_decay_upper_of_good_events
    {Design Estimator State Omega : Type*}
    [Nonempty Estimator] [MeasurableSpace Omega]
    (states : Set State) (hstates : states.Nonempty)
    (pointRisk : Design → Estimator → State → ℝ)
    (hpoint_nonnegative : ∀ design estimator state,
      state ∈ states → 0 ≤ pointRisk design estimator state)
    (hbdd : ∀ design estimator,
      BddAbove (pointRisk design estimator '' states))
    (design : Design) (estimator : Estimator)
    (mu : State → Measure Omega)
    (hprobability : ∀ state ∈ states, IsProbabilityMeasure (mu state))
    (randomError : State → Omega → ℝ)
    (good : State → Set Omega)
    (tail : State → ℕ → ℝ)
    (D : ℕ) (L eta delta alpha : ℝ)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (heta : 0 < eta)
    (hdelta : 0 ≤ delta) (halpha : 1 < alpha)
    (hsemantic : ∀ state ∈ states,
      pointRisk design estimator state =
        ∫ omega, randomError state omega ∂(mu state))
    (hintegrable : ∀ state ∈ states,
      Integrable (randomError state) (mu state))
    (hgood_measurable : ∀ state ∈ states,
      MeasurableSet (good state))
    (hbad : ∀ state ∈ states,
      mu state (good state)ᶜ ≤ ENNReal.ofReal delta)
    (hgoodOracle : ∀ state ∈ states, ∀ omega ∈ good state,
      OracleBound (randomError state omega) (tail state) (4 * eta) D)
    (hcap : ∀ state ∈ states, ∀ omega,
      randomError state omega ≤ 2)
    (htail_nonnegative : ∀ state ∈ states, ∀ s,
      1 ≤ s → s ≤ D → 0 ≤ tail state s)
    (htail : ∀ state ∈ states, ∀ s, 1 ≤ s → s ≤ D →
      tail state s ≤ L * (s : ℝ) ^ (1 - alpha))
    (htailD : ∀ state ∈ states, tail state D = 0) :
    fixedDesignRisk (classRisk states pointRisk) design ≤
      12 * decayUpperRate D L (eta + delta / 2) alpha := by
  have heta_effective : 0 < eta + delta / 2 := by positivity
  have hexpectedOracle : ∀ state ∈ states,
      OracleBound (pointRisk design estimator state) (tail state)
        (4 * (eta + delta / 2)) D := by
    intro state hstate
    let _ : IsProbabilityMeasure (mu state) := hprobability state hstate
    rw [hsemantic state hstate]
    exact expectedOracle_of_good_event_trace_cap
      (mu state) (randomError state) (good state)
      (hgood_measurable state hstate) (hintegrable state hstate)
      (tail state) eta delta D heta.le hdelta
      (htail_nonnegative state hstate) (hbad state hstate)
      (hgoodOracle state hstate) (hcap state hstate)
  exact fixedDesignClassRisk_decay_upper_of_expected_oracle
    states hstates pointRisk hpoint_nonnegative hbdd design estimator tail
    D L (eta + delta / 2) alpha hD hL heta_effective halpha
    (fun state hstate => by
      let _ : IsProbabilityMeasure (mu state) := hprobability state hstate
      rw [hsemantic state hstate]
      have hcapIntegral :
          (∫ omega, randomError state omega ∂(mu state)) ≤ 2 := by
        have hconst : Integrable (fun _omega : Omega => (2 : ℝ)) (mu state) :=
          integrable_const 2
        have hmono := integral_mono (hintegrable state hstate) hconst
          (hcap state hstate)
        simpa [measureReal_def] using hmono
      exact hcapIntegral)
    hexpectedOracle htail htailD

end TomographyOracleCore
