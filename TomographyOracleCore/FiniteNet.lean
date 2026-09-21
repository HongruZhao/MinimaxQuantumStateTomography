import TomographyOracleCore.MathlibImports
import TomographyOracleCore.RobustNoise

namespace TomographyOracleCore

open Metric Set Module MeasureTheory
open scoped ENNReal NNReal Function

/-! A quantitative `1/4`-net for a finite-dimensional real unit sphere. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A quarter-separated subset of the unit ball has at most `9^dim` points.
The proof is the standard disjoint `1/8`-balls inside the `9/8`-ball volume
argument. -/
theorem card_le_nine_pow_finrank_of_quarter_separated
    (s : Finset E) (hs : ∀ c ∈ s, ‖c‖ ≤ 1)
    (hsep : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → (1 : ℝ) / 4 ≤ ‖c - d‖) :
    s.card ≤ 9 ^ finrank ℝ E := by
  borelize E
  let mu : Measure E := Measure.addHaar
  let delta : ℝ := (1 : ℝ) / 8
  let rho : ℝ := (9 : ℝ) / 8
  have hrho : 0 < rho := by norm_num [rho]
  set A := ⋃ c ∈ s, ball (c : E) delta with hA
  have hdisjoint : Set.Pairwise (s : Set E)
      (Disjoint on fun c ↦ ball (c : E) delta) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have hdelta : delta + delta = (1 : ℝ) / 4 := by norm_num [delta]
    rw [hdelta]
    exact hsep c hc d hd hcd
  have hsubset : A ⊆ ball (0 : E) rho := by
    refine iUnion₂_subset fun x hx ↦ ?_
    apply ball_subset_ball'
    calc
      delta + dist x 0 ≤ delta + 1 := by
        rw [dist_zero_right]
        exact add_le_add le_rfl (hs x hx)
      _ = rho := by norm_num [delta, rho]
  have hmeasure :
      (s.card : ENNReal) * ENNReal.ofReal (delta ^ finrank ℝ E) *
          mu (ball 0 1) ≤
        ENNReal.ofReal (rho ^ finrank ℝ E) * mu (ball 0 1) :=
    calc
      (s.card : ENNReal) * ENNReal.ofReal (delta ^ finrank ℝ E) *
          mu (ball 0 1) = mu A := by
        rw [hA, measure_biUnion_finset hdisjoint fun c _ ↦ measurableSet_ball]
        have hdelta : 0 < delta := by norm_num [delta]
        simp only [mu.addHaar_ball_of_pos _ hdelta]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ mu (ball (0 : E) rho) := measure_mono hsubset
      _ = ENNReal.ofReal (rho ^ finrank ℝ E) * mu (ball 0 1) := by
        simp only [mu.addHaar_ball_of_pos _ hrho]
  have hcancel :
      (s.card : ENNReal) * ENNReal.ofReal (delta ^ finrank ℝ E) ≤
        ENNReal.ofReal (rho ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left
      (measure_ball_pos mu (0 : E) zero_lt_one).ne'
      measure_ball_lt_top.ne).1 hmeasure
  have hreal : (s.card : ℝ) ≤ (9 : ℝ) ^ finrank ℝ E := by
    have htoReal := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hrho.le _) hcancel
    simpa [rho, delta, div_eq_mul_inv, mul_pow] using htoReal
  exact_mod_cast hreal

/-- Existence of a finite internal `1/4`-net of the real unit sphere with the
explicit volumetric cardinality `9^finrank`. -/
theorem exists_quarter_sphere_net :
    ∃ net : Finset E,
      (∀ u ∈ net, ‖u‖ = 1) ∧
      (∀ x : E, ‖x‖ = 1 → ∃ u ∈ net, ‖x - u‖ ≤ (1 : ℝ) / 4) ∧
      net.card ≤ 9 ^ finrank ℝ E := by
  let sphereSet : Set E := sphere (0 : E) 1
  let eps : NNReal := 1 / 4
  have heps : eps ≠ 0 := by norm_num [eps]
  have hsphereCompact : IsCompact sphereSet := by
    simpa [sphereSet] using isCompact_sphere (0 : E) 1
  obtain ⟨cover, hcoverSubset, hcoverFinite, hcover⟩ :=
    Metric.exists_finite_isCover_of_isCompact
      (s := sphereSet) (ε := (1 / 8 : NNReal)) (by norm_num) hsphereCompact
  have hpackingLe : Metric.packingNumber eps sphereSet ≤ cover.encard := by
    calc
      Metric.packingNumber eps sphereSet =
          Metric.packingNumber (2 * (1 / 8 : NNReal)) sphereSet := by norm_num [eps]
      _ ≤ Metric.externalCoveringNumber (1 / 8 : NNReal) sphereSet :=
        Metric.packingNumber_two_mul_le_externalCoveringNumber _ _
      _ ≤ cover.encard := hcover.externalCoveringNumber_le_encard
  have hpackingFinite : Metric.packingNumber eps sphereSet ≠ ⊤ :=
    ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hcoverFinite) hpackingLe
  let netSet : Set E := Metric.maximalSeparatedSet eps sphereSet
  have hnetFinite : netSet.Finite := by
    apply Set.encard_ne_top_iff.mp
    dsimp [netSet]
    rw [Metric.encard_maximalSeparatedSet hpackingFinite]
    exact hpackingFinite
  let net : Finset E := hnetFinite.toFinset
  refine ⟨net, ?_, ?_, ?_⟩
  · intro u hu
    have huSet : u ∈ netSet := by simpa [net] using hu
    have huSphere := Metric.maximalSeparatedSet_subset huSet
    simpa [sphereSet, mem_sphere, dist_zero_right] using huSphere
  · intro x hx
    have hxSphere : x ∈ sphereSet := by
      simpa [sphereSet, mem_sphere, dist_zero_right] using hx
    obtain ⟨u, huSet, hxu⟩ := Metric.isCover_maximalSeparatedSet hpackingFinite hxSphere
    refine ⟨u, ?_, ?_⟩
    · simpa [net] using huSet
    · change edist x u ≤ (eps : ENNReal) at hxu
      rw [edist_dist, ENNReal.ofReal_le_coe] at hxu
      simpa [eps, dist_eq_norm] using hxu
  · apply card_le_nine_pow_finrank_of_quarter_separated net
    · intro u hu
      have huSet : u ∈ netSet := by simpa [net] using hu
      have huSphere := Metric.maximalSeparatedSet_subset huSet
      have hunorm : ‖u‖ = 1 := by
        simpa [sphereSet, mem_sphere, dist_zero_right] using huSphere
      exact hunorm.le
    · intro c hc d hd hcd
      have hcSet : c ∈ netSet := by simpa [net] using hc
      have hdSet : d ∈ netSet := by simpa [net] using hd
      have hsepSet : Metric.IsSeparated (eps : ENNReal) netSet := by
        simpa [netSet] using
          (Metric.isSeparated_maximalSeparatedSet (ε := eps) (A := sphereSet))
      have hseparated := hsepSet hcSet hdSet hcd
      change (eps : ENNReal) < edist c d at hseparated
      rw [edist_dist, ENNReal.coe_lt_ofReal] at hseparated
      have hdist : (1 : ℝ) / 4 < dist c d := by simpa [eps] using hseparated
      rw [dist_eq_norm] at hdist
      exact hdist.le

/-- Complex `D`-dimensional specialization.  Its real dimension is `2 * D`,
so the volumetric net has cardinality at most `9^(2D)`. -/
theorem exists_complex_quarter_sphere_net (D : ℕ) :
    ∃ net : Finset (EuclideanSpace ℂ (Fin D)),
      (∀ u ∈ net, ‖u‖ = 1) ∧
      (∀ x : EuclideanSpace ℂ (Fin D), ‖x‖ = 1 →
        ∃ u ∈ net, ‖x - u‖ ≤ (1 : ℝ) / 4) ∧
      net.card ≤ 9 ^ (2 * D) := by
  simpa [finrank_real_of_complex, finrank_euclideanSpace_fin] using
    (exists_quarter_sphere_net (E := EuclideanSpace ℂ (Fin D)))

end TomographyOracleCore
