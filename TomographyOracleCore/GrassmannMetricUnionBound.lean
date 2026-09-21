import TomographyOracleCore.GrassmannGreedy
import Mathlib.MeasureTheory.Measure.Real

namespace TomographyOracleCore

open MatrixReduction MeasureTheory Set

/-!
# The probability-union step in Grassmann metric exclusion

The cited Grassmann argument samples a random projector and bounds the
probability that it lies in one trace-distance ball.  This module proves the
remaining finite-union argument: if every bad ball has mass at most
`exp (-gamma * m * k)`, then every list shorter than
`exp (gamma * m * k)` misses at least one sampled projector.

The sample space and sampler are abstract so that the geometric input can be
instantiated directly with normalized Haar measure on the real special
orthogonal group.  No measurability premise is needed for this union-bound
step: `Measure.real` is an outer measure on arbitrary sets.
-/

/-- The event that a sampled projector is closer than normalized distance
`1/4` to a fixed projector. -/
noncomputable def grassmannQuarterBadEvent
    {Ω : Type*} {k m : ℕ}
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (P : RankMComplexOrthogonalProjector k m) : Set Ω :=
  {ω |
    projectorHermitianTraceDistance (sample ω) P / (2 * (m : ℝ)) <
      (1 / 4 : ℝ)}

/-- The one-ball mass scale needed by the manuscript's quarter-distance
packing. -/
noncomputable def grassmannQuarterBadMassBound (k m : ℕ) : ℝ :=
  Real.exp
    (-(grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ)))

theorem grassmannQuarterBadMassBound_pos (k m : ℕ) :
    0 < grassmannQuarterBadMassBound k m := by
  exact Real.exp_pos _

/-- Strictly fewer than `exp (gamma*m*k)` balls, each of mass at most
`exp (-gamma*m*k)`, have total mass strictly below one. -/
theorem length_mul_grassmannQuarterBadMassBound_lt_one
    {α : Type*} {k m : ℕ} {L : List α}
    (hL : (L.length : ℝ) <
      Real.exp
        (grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ))) :
    (L.length : ℝ) * grassmannQuarterBadMassBound k m < 1 := by
  let a : ℝ := grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ)
  change (L.length : ℝ) < Real.exp a at hL
  have hmul := mul_lt_mul_of_pos_right hL (Real.exp_pos (-a))
  rw [grassmannQuarterBadMassBound]
  change (L.length : ℝ) * Real.exp (-a) < 1
  calc
    (L.length : ℝ) * Real.exp (-a) < Real.exp a * Real.exp (-a) := hmul
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The source-faithful finite-union statement: if the one-ball estimate is
known for centers produced by the same sampler, a finite sampled list below
the exponential threshold admits one more separated sample.

This is weaker than asking for the estimate around every complex projector,
and is exactly what the greedy construction needs when all preceding
projectors were themselves obtained from the Haar sampler. -/
theorem exists_sample_outside_grassmannQuarterBadEvents
    {Ω : Type*} [MeasurableSpace Ω]
    {k m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (hsmall : ∀ ω₀ : Ω,
      μ.real (grassmannQuarterBadEvent sample (sample ω₀)) ≤
        grassmannQuarterBadMassBound k m)
    (W : List Ω)
    (hW : (W.length : ℝ) <
      Real.exp
        (grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ))) :
    ∃ ω : Ω, ∀ ω₀ ∈ W,
      (1 / 4 : ℝ) ≤
        projectorHermitianTraceDistance (sample ω) (sample ω₀) /
          (2 * (m : ℝ)) := by
  classical
  let badUnion : Set Ω :=
    ⋃ i : Fin W.length,
      grassmannQuarterBadEvent sample (sample (W.get i))
  have hunion_le :
      μ.real badUnion ≤
        ∑ i : Fin W.length,
          μ.real (grassmannQuarterBadEvent sample (sample (W.get i))) := by
    exact measureReal_iUnion_fintype_le _
  have hsum_le :
      (∑ i : Fin W.length,
          μ.real (grassmannQuarterBadEvent sample (sample (W.get i)))) ≤
        (W.length : ℝ) * grassmannQuarterBadMassBound k m := by
    calc
      (∑ i : Fin W.length,
          μ.real (grassmannQuarterBadEvent sample (sample (W.get i)))) ≤
          ∑ _i : Fin W.length, grassmannQuarterBadMassBound k m := by
            exact Finset.sum_le_sum fun i _hi ↦ hsmall (W.get i)
      _ = (W.length : ℝ) * grassmannQuarterBadMassBound k m := by
        simp
  have hunion_lt_one : μ.real badUnion < 1 :=
    lt_of_le_of_lt (hunion_le.trans hsum_le)
      (length_mul_grassmannQuarterBadMassBound_lt_one hW)
  have hbad_ne_univ : badUnion ≠ Set.univ := by
    intro hbad
    have : μ.real badUnion = 1 := by simp [hbad]
    linarith
  obtain ⟨ω, hω⟩ := Set.nonempty_compl.mpr hbad_ne_univ
  refine ⟨ω, ?_⟩
  intro ω₀ hω₀
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hω₀
  have hnotbad :
      ω ∉ grassmannQuarterBadEvent sample (sample ω₀) := by
    intro hbad
    have hmem : ω ∈ badUnion := by
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simpa only [← hi] using hbad
    exact hω hmem
  exact not_lt.mp hnotbad

/-- Greedy induction performed entirely inside the range of the supplied
probability sampler. -/
theorem exists_greedy_sample_list_of_probability_selfSmallBall
    {Ω : Type*} [MeasurableSpace Ω]
    {k m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (hm : 1 ≤ m)
    (hsmall : ∀ ω₀ : Ω,
      μ.real (grassmannQuarterBadEvent sample (sample ω₀)) ≤
        grassmannQuarterBadMassBound k m) :
    ∀ n : ℕ, n ≤ grassmannPackingCard k m →
      ∃ W : List Ω,
        W.length = n ∧
          W.Pairwise (fun ω ω₀ ↦
            (m : ℝ) / 2 ≤
              projectorHermitianTraceDistance (sample ω) (sample ω₀)) := by
  intro n hn
  induction n with
  | zero =>
      exact ⟨[], rfl, by simp⟩
  | succ n ih =>
      have hnlt : n < grassmannPackingCard k m := Nat.lt_of_succ_le hn
      obtain ⟨W, hlen, hpair⟩ := ih (Nat.le_of_lt hnlt)
      have hthreshold :
          (W.length : ℝ) <
            Real.exp
              (grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ)) := by
        rw [grassmannQuarterMetricExponent_eq_gamma0]
        rw [hlen]
        exact index_lt_grassmannPackingCard_strict_threshold hnlt
      obtain ⟨ω, hω⟩ :=
        exists_sample_outside_grassmannQuarterBadEvents μ sample hsmall W
          hthreshold
      refine ⟨ω :: W, by simp [hlen], ?_⟩
      exact List.pairwise_cons.mpr ⟨fun ω₀ hω₀ ↦
        projector_separation_of_normalized_quarter
          (sample ω) (sample ω₀) hm (hω ω₀ hω₀), hpair⟩

/-- The exact ceiling-cardinality complex Grassmann packing follows from a
one-ball estimate only at centers in the range of the sampler.  This avoids
the unnecessarily stronger premise that the estimate hold around arbitrary
complex projectors. -/
theorem exists_complexGrassmannPackingWitness_card_eq_of_probability_selfSmallBall
    {Ω : Type*} [MeasurableSpace Ω]
    {k m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (hm : 1 ≤ m)
    (hsmall : ∀ ω₀ : Ω,
      μ.real (grassmannQuarterBadEvent sample (sample ω₀)) ≤
        grassmannQuarterBadMassBound k m) :
    ∃ V : ComplexGrassmannPackingWitness k m,
      V.card = grassmannPackingCard k m := by
  obtain ⟨W, hlen, hpair⟩ :=
    exists_greedy_sample_list_of_probability_selfSmallBall μ sample hm hsmall
      (grassmannPackingCard k m) le_rfl
  refine ⟨{
    card := W.length
    projector := fun i ↦ sample (W.get i)
    log_cardinality_lower := ?_
    pairwise_separated := ?_
  }, hlen⟩
  · rw [hlen]
    simpa only [grassmannGamma0] using grassmannPackingCard_log_lower k m
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · exact hpair.rel_get_of_lt hijlt
    · rw [projectorHermitianTraceDistance_comm]
      exact hpair.rel_get_of_lt hjilt

/-- A probability-space one-ball estimate implies the exact one-step metric
exclusion proposition used by `GrassmannGreedy`.

This theorem discharges the finite union bound and the extraction of a
deterministic projector.  Its sole geometric premise is the pointwise
one-ball mass estimate `hsmall` for a supplied random-projector sampler. -/
theorem flammiaQuarterMetricExclusionAt_of_probability_smallBall
    {Ω : Type*} [MeasurableSpace Ω]
    {k m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (hsmall : ∀ P : RankMComplexOrthogonalProjector k m,
      μ.real (grassmannQuarterBadEvent sample P) ≤
        grassmannQuarterBadMassBound k m) :
    FlammiaQuarterMetricExclusionAt k m := by
  classical
  intro L hL
  let badUnion : Set Ω :=
    ⋃ i : Fin L.length, grassmannQuarterBadEvent sample (L.get i)
  have hunion_le :
      μ.real badUnion ≤
        ∑ i : Fin L.length,
          μ.real (grassmannQuarterBadEvent sample (L.get i)) := by
    exact measureReal_iUnion_fintype_le _
  have hsum_le :
      (∑ i : Fin L.length,
          μ.real (grassmannQuarterBadEvent sample (L.get i))) ≤
        (L.length : ℝ) * grassmannQuarterBadMassBound k m := by
    calc
      (∑ i : Fin L.length,
          μ.real (grassmannQuarterBadEvent sample (L.get i))) ≤
          ∑ _i : Fin L.length, grassmannQuarterBadMassBound k m := by
            exact Finset.sum_le_sum fun i _hi ↦ hsmall (L.get i)
      _ = (L.length : ℝ) * grassmannQuarterBadMassBound k m := by
        simp
  have hunion_lt_one : μ.real badUnion < 1 :=
    lt_of_le_of_lt (hunion_le.trans hsum_le)
      (length_mul_grassmannQuarterBadMassBound_lt_one hL)
  have hbad_ne_univ : badUnion ≠ Set.univ := by
    intro hbad
    have : μ.real badUnion = 1 := by simp [hbad]
    linarith
  obtain ⟨ω, hω⟩ := Set.nonempty_compl.mpr hbad_ne_univ
  refine ⟨sample ω, ?_⟩
  intro P hP
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hP
  have hnotbad : ω ∉ grassmannQuarterBadEvent sample P := by
    intro hbad
    have hmem : ω ∈ badUnion := by
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      simpa only [← hi] using hbad
    exact hω hmem
  exact not_lt.mp hnotbad

end TomographyOracleCore
