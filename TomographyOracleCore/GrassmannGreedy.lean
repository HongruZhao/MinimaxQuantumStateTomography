import TomographyOracleCore.GrassmannStatement
import TomographyOracleCore.LowerConstants

namespace TomographyOracleCore

open MatrixReduction

/-!
# Finite greedy construction of the Grassmann packing

This module isolates the only remaining geometric input to the projector
packing: a one-step metric-exclusion statement at normalized distance `1/4`.
It does not assert that statement.  From it, the file proves the entire
finite greedy induction, the strict ceiling threshold, exact cardinality,
the conversion to unnormalized trace distance, and the existing
`ComplexGrassmannPackingInput` conclusion.
-/

/-- The elementary exponent obtained from the quarter-distance specialization
of the metric exclusion estimate. -/
noncomputable def grassmannQuarterMetricExponent : ℝ :=
  (1 / 32 : ℝ) * ((2 / 3 : ℝ) - 1 / 4) ^ 2

/-- Exact extraction of the manuscript constant `25/4608`. -/
theorem grassmannQuarterMetricExponent_eq_gamma0 :
    grassmannQuarterMetricExponent = grassmannGamma0 := by
  norm_num [grassmannQuarterMetricExponent, grassmannGamma0]

/-- The exact ceiling cardinality used by the manuscript's greedy packing. -/
noncomputable def grassmannPackingCard (k m : ℕ) : ℕ :=
  Nat.ceil (Real.exp (grassmannGamma0 * (m : ℝ) * (k : ℝ)))

theorem grassmannPackingCard_pos (k m : ℕ) :
    0 < grassmannPackingCard k m := by
  rw [grassmannPackingCard, Nat.ceil_pos]
  exact Real.exp_pos _

/-- Every intermediate list shorter than the ceiling cardinality satisfies
the strict real-cardinality hypothesis required by metric exclusion. -/
theorem index_lt_grassmannPackingCard_strict_threshold
    {k m s : ℕ} (hs : s < grassmannPackingCard k m) :
    (s : ℝ) < Real.exp (grassmannGamma0 * (m : ℝ) * (k : ℝ)) := by
  rw [grassmannPackingCard] at hs
  exact Nat.lt_ceil.mp hs

/-- In particular, immediately before the final greedy selection there are
strictly fewer than `exp (gamma0*m*k)` existing points. -/
theorem grassmannPackingCard_pred_strict_threshold (k m : ℕ) :
    ((grassmannPackingCard k m - 1 : ℕ) : ℝ) <
      Real.exp (grassmannGamma0 * (m : ℝ) * (k : ℝ)) := by
  apply index_lt_grassmannPackingCard_strict_threshold
  exact Nat.pred_lt (Nat.ne_of_gt (grassmannPackingCard_pos k m))

/-- Taking the ceiling loses nothing in the logarithmic cardinality lower
bound. -/
theorem grassmannPackingCard_log_lower (k m : ℕ) :
    grassmannGamma0 * (m : ℝ) * (k : ℝ) ≤
      Real.log (grassmannPackingCard k m : ℝ) := by
  let x : ℝ := grassmannGamma0 * (m : ℝ) * (k : ℝ)
  have hceil : Real.exp x ≤ (Nat.ceil (Real.exp x) : ℝ) :=
    Nat.le_ceil (Real.exp x)
  calc
    grassmannGamma0 * (m : ℝ) * (k : ℝ) = Real.log (Real.exp x) := by
      simp [x]
    _ ≤ Real.log (Nat.ceil (Real.exp x) : ℝ) :=
      Real.log_le_log (Real.exp_pos x) hceil
    _ = Real.log (grassmannPackingCard k m : ℝ) := by
      rfl

/-- The projector Hermitian trace distance is symmetric. -/
theorem projectorHermitianTraceDistance_comm {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) :
    projectorHermitianTraceDistance P Q =
      projectorHermitianTraceDistance Q P := by
  unfold projectorHermitianTraceDistance
  calc
    hermitianTraceNorm (P.matrix - Q.matrix)
        (P.isHermitian.sub Q.isHermitian) =
      hermitianTraceNorm (-(Q.matrix - P.matrix))
        (Q.isHermitian.sub P.isHermitian).neg := by
          apply hermitianTraceNorm_congr
          abel
    _ = hermitianTraceNorm (Q.matrix - P.matrix)
        (Q.isHermitian.sub P.isHermitian) :=
      hermitianTraceNorm_neg _ _

/-- The cited normalized half-trace-distance conclusion at `1/4` is exactly
the required unnormalized projector separation `m/2`. -/
theorem projector_separation_of_normalized_quarter {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) (hm : 1 ≤ m)
    (hquarter :
      (1 / 4 : ℝ) ≤
        projectorHermitianTraceDistance P Q / (2 * (m : ℝ))) :
    (m : ℝ) / 2 ≤ projectorHermitianTraceDistance P Q := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 2 * (m : ℝ) := mul_pos (by norm_num) hmpos
  have hmul := (le_div_iff₀ hden).mp hquarter
  calc
    (m : ℝ) / 2 = (1 / 4 : ℝ) * (2 * (m : ℝ)) := by ring
    _ ≤ projectorHermitianTraceDistance P Q := hmul

/-- The sole local geometric gap: any finite list strictly below the
quarter-metric threshold admits one further rank-`m` projector separated from
every listed projector.  No separation or distinctness premise is imposed on
the existing list, so this is only the one-step exclusion statement. -/
noncomputable def FlammiaQuarterMetricExclusionAt (k m : ℕ) : Prop :=
  ∀ L : List (RankMComplexOrthogonalProjector k m),
    (L.length : ℝ) <
      Real.exp (grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ)) →
    ∃ Q : RankMComplexOrthogonalProjector k m,
      ∀ P ∈ L,
        (1 / 4 : ℝ) ≤
          projectorHermitianTraceDistance Q P / (2 * (m : ℝ))

/-- Dimension-uniform packaging of the local metric-exclusion statement over
the manuscript's admissible rank range.  This proposition is not asserted. -/
noncomputable def FlammiaQuarterMetricExclusionInput : Prop :=
  ∀ k m : ℕ, 1 ≤ m → 3 * m ≤ k →
    FlammiaQuarterMetricExclusionAt k m

/-- Finite greedy induction: from the one-step exclusion statement, construct
a pairwise-separated projector list of every length up to the ceiling target. -/
theorem exists_greedy_projector_list_of_oneStep
    {k m : ℕ} (hm : 1 ≤ m)
    (hstep : FlammiaQuarterMetricExclusionAt k m) :
    ∀ n : ℕ, n ≤ grassmannPackingCard k m →
      ∃ L : List (RankMComplexOrthogonalProjector k m),
        L.length = n ∧
          L.Pairwise (fun P Q ↦
            (m : ℝ) / 2 ≤ projectorHermitianTraceDistance P Q) := by
  intro n hn
  induction n with
  | zero =>
      exact ⟨[], rfl, by simp⟩
  | succ n ih =>
      have hnlt : n < grassmannPackingCard k m := Nat.lt_of_succ_le hn
      obtain ⟨L, hlen, hpair⟩ := ih (Nat.le_of_lt hnlt)
      have hthreshold :
          (L.length : ℝ) <
            Real.exp
              (grassmannQuarterMetricExponent * (m : ℝ) * (k : ℝ)) := by
        rw [grassmannQuarterMetricExponent_eq_gamma0]
        rw [hlen]
        exact index_lt_grassmannPackingCard_strict_threshold hnlt
      obtain ⟨Q, hQ⟩ := hstep L hthreshold
      refine ⟨Q :: L, by simp [hlen], ?_⟩
      exact List.pairwise_cons.mpr ⟨fun P hP ↦
        projector_separation_of_normalized_quarter Q P hm (hQ P hP), hpair⟩

/-- Strong packing output with cardinality exactly
`ceil (exp (gamma0*m*k))`. -/
theorem exists_complexGrassmannPackingWitness_card_eq_of_oneStep
    {k m : ℕ} (hm : 1 ≤ m)
    (hstep : FlammiaQuarterMetricExclusionAt k m) :
    ∃ W : ComplexGrassmannPackingWitness k m,
      W.card = grassmannPackingCard k m := by
  obtain ⟨L, hlen, hpair⟩ :=
    exists_greedy_projector_list_of_oneStep hm hstep
      (grassmannPackingCard k m) le_rfl
  refine ⟨{
    card := L.length
    projector := L.get
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

/-- Local one-step metric exclusion already implies the complete packing
witness at fixed `(k,m)`. -/
theorem complexGrassmannPackingWitness_of_oneStep
    {k m : ℕ} (hm : 1 ≤ m)
    (hstep : FlammiaQuarterMetricExclusionAt k m) :
    Nonempty (ComplexGrassmannPackingWitness k m) := by
  obtain ⟨W, hcard⟩ :=
    exists_complexGrassmannPackingWitness_card_eq_of_oneStep hm hstep
  exact ⟨W⟩

/-- The dimension-uniform one-step exclusion input implies the existing full
`ComplexGrassmannPackingInput`; no packing assertion remains separate. -/
theorem complexGrassmannPackingInput_of_oneStep
    (hstep : FlammiaQuarterMetricExclusionInput) :
    ComplexGrassmannPackingInput := by
  intro k m _hk hm hkm
  exact complexGrassmannPackingWitness_of_oneStep hm (hstep k m hm hkm)

end TomographyOracleCore
