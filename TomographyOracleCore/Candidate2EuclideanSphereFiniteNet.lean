import TomographyOracleCore.Candidate2ClippedSpreadFiniteNet
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.Topology.MetricSpace.CoveringNumbers

/-!
# Explicit finite nets of a Euclidean unit sphere

This module proves the standard volumetric estimate for an internal net of a
finite-dimensional real unit sphere.  Neither the net nor its cardinality is
postulated: a maximal separated set supplies the cover, and disjoint Haar
balls supply the count.
-/

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal Function

namespace TomographyOracleCore.PeriodicForwardCovariance.PeakySpread

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Volumetric packing estimate in the Euclidean unit ball.  A finite family
whose distinct points are at least `eta` apart has real cardinality at most
`(1 + 2 / eta)^finrank`. -/
theorem real_card_le_unitBall_of_separated
    (s : Finset E) {eta : ℝ} (heta : 0 < eta)
    (hs : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → eta ≤ ‖x - y‖) :
    (s.card : ℝ) ≤ (1 + 2 / eta) ^ finrank ℝ E := by
  borelize E
  let mu : Measure E := Measure.addHaar
  let delta : ℝ := eta / 2
  let rho : ℝ := 1 + eta / 2
  have hdelta : 0 < delta := by dsimp [delta]; linarith
  have hrho : 0 < rho := by dsimp [rho]; linarith
  set A := ⋃ x ∈ s, ball (x : E) delta with hA
  have hdisjoint : Set.Pairwise (s : Set E)
      (Disjoint on fun x => ball (x : E) delta) := by
    rintro x hx y hy hxy
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have h := hsep x hx y hy hxy
    dsimp [delta]
    linarith
  have hsubset : A ⊆ ball (0 : E) rho := by
    refine iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    calc
      delta + dist x 0 ≤ delta + 1 := by
        rw [dist_zero_right]
        exact add_le_add_right (hs x hx) delta
      _ = rho := by dsimp [rho]; ring
  have hvolume :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (delta ^ finrank ℝ E) *
          mu (ball 0 1) ≤
        ENNReal.ofReal (rho ^ finrank ℝ E) * mu (ball 0 1) := by
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal (delta ^ finrank ℝ E) *
            mu (ball 0 1) = mu A := by
        rw [hA, measure_biUnion_finset hdisjoint
          (fun x _hx => measurableSet_ball)]
        simp only [mu.addHaar_ball_of_pos _ hdelta]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ mu (ball (0 : E) rho) := measure_mono hsubset
      _ = ENNReal.ofReal (rho ^ finrank ℝ E) * mu (ball 0 1) := by
        simp only [mu.addHaar_ball_of_pos _ hrho]
  have hcancel :
      (s.card : ℝ≥0∞) * ENNReal.ofReal (delta ^ finrank ℝ E) ≤
        ENNReal.ofReal (rho ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left
      (measure_ball_pos mu (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hvolume
  have hmul :
      (s.card : ℝ) * delta ^ finrank ℝ E ≤ rho ^ finrank ℝ E := by
    have h := ENNReal.toReal_le_of_le_ofReal
      (pow_nonneg hrho.le _) hcancel
    simpa [ENNReal.toReal_ofNat, pow_nonneg hdelta.le] using h
  have hdeltaPow : 0 < delta ^ finrank ℝ E := pow_pos hdelta _
  calc
    (s.card : ℝ) ≤ rho ^ finrank ℝ E / delta ^ finrank ℝ E :=
      (le_div_iff₀ hdeltaPow).2 hmul
    _ = (rho / delta) ^ finrank ℝ E :=
      (div_pow rho delta (finrank ℝ E)).symm
    _ = (1 + 2 / eta) ^ finrank ℝ E := by
      congr 1
      dsimp [rho, delta]
      field_simp [heta.ne']
      ring

/-- For every positive radius, the Euclidean unit sphere has an internal
finite net of that radius with the standard volumetric cardinality bound.

The centers have norm exactly one, so the resulting witnesses can be passed
directly to `measure_unitSphere_centeredDirectionalSpread_ge_le_of_finiteNet`.
-/
theorem exists_unitSphere_finset_net_card_le
    {eta : ℝ} (heta : 0 < eta) :
    ∃ net : Finset E,
      (∀ v ∈ net, ‖v‖ = 1) ∧
      (∀ u : E, ‖u‖ = 1 →
        ∃ v ∈ net, ‖v‖ = 1 ∧ ‖u - v‖ ≤ eta) ∧
      (net.card : ℝ) ≤ (1 + 2 / eta) ^ finrank ℝ E := by
  let eps : ℝ≥0 := ⟨eta, heta.le⟩
  let sphere : Set E := Metric.sphere (0 : E) 1
  obtain ⟨cover, _hcoverSubset, hcoverFinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := eps / 2) (by
        apply div_ne_zero
        · exact ne_of_gt (show 0 < eps by exact heta)
        · norm_num) (isCompact_sphere (0 : E) 1)
  have hpacking : Metric.packingNumber eps sphere ≤ cover.encard := by
    calc
      Metric.packingNumber eps sphere =
          Metric.packingNumber (2 * (eps / 2)) sphere := by
        congr 2
        field_simp
      _ ≤ Metric.externalCoveringNumber (eps / 2) sphere :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber
          (eps / 2) sphere
      _ ≤ cover.encard := hcover.externalCoveringNumber_le_encard
  have hpackingFinite : Metric.packingNumber eps sphere ≠ ⊤ :=
    ne_top_of_le_ne_top
      (Set.encard_ne_top_iff.mpr hcoverFinite) hpacking
  let maximal : Set E := Metric.maximalSeparatedSet eps sphere
  have hmaximalFinite : maximal.Finite := by
    rw [← Set.encard_ne_top_iff]
    dsimp only [maximal]
    rw [Metric.encard_maximalSeparatedSet hpackingFinite]
    exact hpackingFinite
  let net : Finset E := hmaximalFinite.toFinset
  have hnetCoe : (net : Set E) = maximal := by
    exact hmaximalFinite.coe_toFinset
  have hnetUnit : ∀ v ∈ net, ‖v‖ = 1 := by
    intro v hv
    have hvMaximal : v ∈ maximal := by
      have hvNetSet : v ∈ (net : Set E) := hv
      rw [hnetCoe] at hvNetSet
      exact hvNetSet
    have hvSphere : v ∈ sphere :=
      Metric.maximalSeparatedSet_subset hvMaximal
    simpa only [sphere, mem_sphere_zero_iff_norm] using hvSphere
  have hnetCover : ∀ u : E, ‖u‖ = 1 →
      ∃ v ∈ net, ‖v‖ = 1 ∧ ‖u - v‖ ≤ eta := by
    intro u hu
    have huSphere : u ∈ sphere := by
      simpa only [sphere, mem_sphere_zero_iff_norm] using hu
    obtain ⟨v, hvMaximal, huv⟩ :=
      Metric.isCover_maximalSeparatedSet hpackingFinite huSphere
    have hvNet : v ∈ net := by
      have hvNetSet : v ∈ (net : Set E) := by
        rw [hnetCoe]
        exact hvMaximal
      exact hvNetSet
    change edist u v ≤ ↑eps at huv
    have huvNN : nndist u v ≤ eps := by
      exact ENNReal.coe_le_coe.mp (by
        simpa only [edist_nndist] using huv)
    have huvReal : dist u v ≤ eta := by
      exact_mod_cast huvNN
    exact ⟨v, hvNet, hnetUnit v hvNet, by
      simpa only [dist_eq_norm] using huvReal⟩
  refine ⟨net, hnetUnit, hnetCover, ?_⟩
  apply real_card_le_unitBall_of_separated net heta
  · intro v hv
    exact (hnetUnit v hv).le
  · intro x hx y hy hxy
    have hxMaximal : x ∈ maximal := by
      have hxNetSet : x ∈ (net : Set E) := hx
      rwa [hnetCoe] at hxNetSet
    have hyMaximal : y ∈ maximal := by
      have hyNetSet : y ∈ (net : Set E) := hy
      rwa [hnetCoe] at hyNetSet
    have hsepENN :=
      Metric.isSeparated_maximalSeparatedSet hxMaximal hyMaximal hxy
    have hsepNN : eps < nndist x y := by
      exact ENNReal.coe_lt_coe.mp (by
        simpa only [edist_nndist] using hsepENN)
    have hsepReal : eta < dist x y := by
      exact_mod_cast hsepNN
    rw [dist_eq_norm] at hsepReal
    exact hsepReal.le

/-- Fixed-norm product-sample consequence with the net cardinality eliminated.
This is the direct composition of the explicit Euclidean net above with the
finite-net clipped-spread theorem. -/
theorem measure_pi_unitSphere_centeredDirectionalSpread_ge_le_of_fixedNorm
    [MeasurableSpace E] [BorelSpace E]
    [CompleteSpace E] [SecondCountableTopology E]
    (populationLaw : Measure E) [IsProbabilityMeasure populationLaw]
    {T : ℕ} (hT : 0 < T)
    {eta q kappa lambda epsilon : ℝ}
    (heta : 0 < eta)
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
      (1 + 2 / eta) ^ finrank ℝ E *
        (2 * Real.exp (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
  obtain ⟨net, hnetUnit, hnetCover, hnetCard⟩ :=
    exists_unitSphere_finset_net_card_le (E := E) heta
  calc
    (Measure.pi fun _ : Fin T => populationLaw).real {omega |
        ∃ u : E, ‖u‖ = 1 ∧
          epsilon +
                lambda ^ 2 * kappa ^ 6 *
                  ‖populationCovariance populationLaw‖ ^ 3 +
              2 * (q + ‖populationCovariance populationLaw‖) * eta ≤
            |centeredDirectionalSpread populationLaw lambda omega u|} ≤
        (net.card : ℝ) *
          (2 * Real.exp
            (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) :=
      measure_pi_unitSphere_centeredDirectionalSpread_ge_le_of_fixedNorm_finiteNet
        populationLaw hT net hnetCover hnetUnit hnorm hL6 hlambda hepsilon
    _ ≤ (1 + 2 / eta) ^ finrank ℝ E *
          (2 * Real.exp
            (-2 * (T : ℝ) * lambda ^ 2 * epsilon ^ 2)) := by
      exact mul_le_mul_of_nonneg_right hnetCard (by positivity)

end

end TomographyOracleCore.PeriodicForwardCovariance.PeakySpread
