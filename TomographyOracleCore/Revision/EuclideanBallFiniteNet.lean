import TomographyOracleCore.Candidate2EuclideanSphereFiniteNet

namespace TomographyOracleCore.Revision.EuclideanBallFiniteNet

open MeasureTheory Metric Set Module
open scoped ENNReal NNReal Function
open PeriodicForwardCovariance.PeakySpread
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An internal finite net of the closed unit ball, including dimension zero. -/
theorem exists_unitBall_finset_net_card_le {eta : ℝ} (heta : 0 < eta) :
    ∃ net : Finset E,
      (∀ v ∈ net, ‖v‖ ≤ 1) ∧
      (∀ u : E, ‖u‖ ≤ 1 → ∃ v ∈ net, ‖u - v‖ ≤ eta) ∧
      (net.card : ℝ) ≤ (1 + 2 / eta) ^ finrank ℝ E := by
  let eps : ℝ≥0 := ⟨eta, heta.le⟩
  let ball : Set E := Metric.closedBall (0 : E) 1
  obtain ⟨cover, _, hcoverFinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (ε := eps / 2) (by
        apply div_ne_zero
        · exact ne_of_gt (show 0 < eps by exact heta)
        · norm_num) (isCompact_closedBall (0 : E) 1)
  have hpacking : Metric.packingNumber eps ball ≤ cover.encard := by
    calc
      Metric.packingNumber eps ball =
          Metric.packingNumber (2 * (eps / 2)) ball := by congr 2; field_simp
      _ ≤ Metric.externalCoveringNumber (eps / 2) ball :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber (eps / 2) ball
      _ ≤ cover.encard := hcover.externalCoveringNumber_le_encard
  have hfinite : Metric.packingNumber eps ball ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hcoverFinite) hpacking
  let maximal : Set E := Metric.maximalSeparatedSet eps ball
  have hmfinite : maximal.Finite := by
    rw [← Set.encard_ne_top_iff]
    dsimp only [maximal]
    rw [Metric.encard_maximalSeparatedSet hfinite]
    exact hfinite
  let net := hmfinite.toFinset
  have hmem (v : E) : v ∈ net ↔ v ∈ maximal := hmfinite.mem_toFinset
  have hunit : ∀ v ∈ net, ‖v‖ ≤ 1 := by
    intro v hv
    have h := Metric.maximalSeparatedSet_subset ((hmem v).mp hv)
    simpa only [ball, mem_closedBall_zero_iff] using h
  refine ⟨net, hunit, ?_, ?_⟩
  · intro u hu
    have hu' : u ∈ ball := by simpa only [ball, mem_closedBall_zero_iff] using hu
    obtain ⟨v, hv, huv⟩ := Metric.isCover_maximalSeparatedSet hfinite hu'
    refine ⟨v, (hmem v).mpr hv, ?_⟩
    change edist u v ≤ ↑eps at huv
    have huv' : nndist u v ≤ eps := ENNReal.coe_le_coe.mp (by
      simpa only [edist_nndist] using huv)
    have : dist u v ≤ eta := by exact_mod_cast huv'
    simpa only [dist_eq_norm] using this
  · apply real_card_le_unitBall_of_separated net heta hunit
    intro x hx y hy hxy
    have h := Metric.isSeparated_maximalSeparatedSet
      ((hmem x).mp hx) ((hmem y).mp hy) hxy
    have h' : eps < nndist x y := ENNReal.coe_lt_coe.mp (by
      simpa only [edist_nndist] using h)
    have h'' : eta < dist x y := by exact_mod_cast h'
    simpa only [dist_eq_norm] using h''.le

end
end TomographyOracleCore.Revision.EuclideanBallFiniteNet
