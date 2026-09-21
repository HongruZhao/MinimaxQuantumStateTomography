import TomographyOracleCore.HaarRankMProjector
import TomographyOracleCore.GrassmannMetricUnionBound
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Order.Star.Basic

namespace TomographyOracleCore

open MatrixReduction MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-!
# Reducing a Grassmann trace-distance ball to projector overlap

This file contains the deterministic part of the unitary-Haar route to the
Grassmann packing.  It does not postulate a concentration theorem.  Its main
point is that the only probabilistic input still needed is the scalar lower
tail estimate for the overlap with the complementary projector, as in
Lowe--Nayak, Lemma 3.2.
-/

/-- A bundled orthogonal projector is a star projection in the matrix
`C*`-algebra. -/
theorem rankMProjector_isStarProjection {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    IsStarProjection P.matrix where
  isIdempotentElem := P.isIdempotent
  isSelfAdjoint := P.isHermitian

/-- Orthogonal projectors are positive semidefinite. -/
theorem rankMProjector_posSemidef {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) : P.matrix.PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp
    (rankMProjector_isStarProjection P).nonneg

/-- The complementary projector is positive semidefinite. -/
theorem rankMProjector_complement_posSemidef {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    (1 - P.matrix).PosSemidef := by
  exact Matrix.nonneg_iff_posSemidef.mp
    (rankMProjector_isStarProjection P).one_sub.nonneg

/-- The complementary projector is an operator-norm contraction. -/
theorem rankMProjector_complement_operatorNorm_le_one {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    matrixOperatorNorm (1 - P.matrix) ≤ 1 := by
  change ‖1 - P.matrix‖ ≤ 1
  exact IsStarProjection.norm_le _
    (rankMProjector_isStarProjection P).one_sub

/-- Real trace overlap of `Q` with the orthogonal complement of `P`. -/
def projectorComplementOverlap {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) : ℝ :=
  ((1 - P.matrix) * Q.matrix).trace.re

/-- Simultaneous unitary conjugation preserves complementary overlap. -/
theorem projectorComplementOverlap_unitaryConjugate {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (P Q : RankMComplexOrthogonalProjector k m) :
    projectorComplementOverlap (unitaryConjugateRankMProjector U P)
        (unitaryConjugateRankMProjector U Q) =
      projectorComplementOverlap P Q := by
  unfold projectorComplementOverlap
  change ((1 - unitaryConjugateMatrix U P.matrix) *
      unitaryConjugateMatrix U Q.matrix).trace.re = _
  have hmap :
      (1 - unitaryConjugateMatrix U P.matrix) *
          unitaryConjugateMatrix U Q.matrix =
        unitaryConjugateMatrix U ((1 - P.matrix) * Q.matrix) := by
    let e := Unitary.conjStarAlgAut ℂ _ U
    change (1 - e P.matrix) * e Q.matrix = e ((1 - P.matrix) * Q.matrix)
    rw [map_mul, map_sub, map_one]
  rw [hmap, unitaryConjugateMatrix_trace]

/-- The complementary overlap is bounded by the Hermitian trace distance.

This is the deterministic bridge from the scalar projector-overlap tail in
Lowe--Nayak to the trace-distance ball used in the Grassmann packing.
-/
theorem projectorComplementOverlap_le_traceDistance {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) :
    projectorComplementOverlap P Q ≤
      projectorHermitianTraceDistance P Q := by
  let R : Matrix (Fin k) (Fin k) ℂ := 1 - P.matrix
  let Δ : Matrix (Fin k) (Fin k) ℂ := Q.matrix - P.matrix
  have hR : R.IsHermitian := one_sub_isHermitian P.matrix P.isHermitian
  have hRid : IsIdempotentElem R :=
    isIdempotentElem_one_sub P.matrix P.isIdempotent
  have hΔ : Δ.IsHermitian := Q.isHermitian.sub P.isHermitian
  have hRnorm : matrixOperatorNorm R ≤ 1 :=
    rankMProjector_complement_operatorNorm_le_one P
  have hRQ : (R * Q.matrix * R).PosSemidef :=
    sandwich_posSemidef R Q.matrix hR (rankMProjector_posSemidef Q)
  have hcompress : R * Δ * R = R * Q.matrix * R := by
    dsimp [R, Δ]
    have hzero : (1 - P.matrix) * P.matrix = 0 :=
      (rankMProjector_isStarProjection P).one_sub_mul_self
    calc
      (1 - P.matrix) * (Q.matrix - P.matrix) * (1 - P.matrix) =
          (1 - P.matrix) * Q.matrix * (1 - P.matrix) -
            ((1 - P.matrix) * P.matrix) * (1 - P.matrix) := by
              noncomm_ring
      _ = (1 - P.matrix) * Q.matrix * (1 - P.matrix) := by rw [hzero, zero_mul, sub_zero]
  have htrace :
      (R * Q.matrix * R).trace.re = (R * Q.matrix).trace.re := by
    rw [trace_sandwich_of_isIdempotent R Q.matrix hRid]
  have hsand := hermitianTraceNorm_sandwich_le R Δ hR hΔ hRnorm
  calc
    projectorComplementOverlap P Q = (R * Q.matrix).trace.re := by rfl
    _ = (R * Q.matrix * R).trace.re := htrace.symm
    _ = hermitianTraceNorm (R * Q.matrix * R) hRQ.isHermitian :=
      (hermitianTraceNorm_psd_eq_re_trace _ hRQ).symm
    _ = hermitianTraceNorm (R * Δ * R)
          (sandwich_isHermitian R Δ hR hΔ) := by
      exact hermitianTraceNorm_congr hcompress.symm _ _
    _ ≤ hermitianTraceNorm Δ hΔ := hsand
    _ = projectorHermitianTraceDistance Q P := rfl
    _ = projectorHermitianTraceDistance P Q :=
      (projectorHermitianTraceDistance_comm P Q).symm

/-- Membership in a normalized quarter trace-distance ball forces
complementary overlap below `m/2`. -/
theorem projectorComplementOverlap_lt_half_of_mem_grassmannQuarterBadEvent
    {Ω : Type*} {k m : ℕ}
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (ω ω₀ : Ω) (hm : 1 ≤ m)
    (hbad : ω ∈ grassmannQuarterBadEvent sample (sample ω₀)) :
    projectorComplementOverlap (sample ω₀) (sample ω) < (m : ℝ) / 2 := by
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  have hden : 0 < 2 * (m : ℝ) := mul_pos (by norm_num) hmpos
  have hdist :
      projectorHermitianTraceDistance (sample ω) (sample ω₀) < (m : ℝ) / 2 := by
    have hmul := (div_lt_iff₀ hden).mp hbad
    nlinarith
  have hover := projectorComplementOverlap_le_traceDistance
    (sample ω₀) (sample ω)
  rw [projectorHermitianTraceDistance_comm] at hover
  exact lt_of_le_of_lt hover hdist

/-- Set-level deterministic reduction of a trace-distance ball to a scalar
overlap event. -/
theorem grassmannQuarterBadEvent_subset_complementOverlapHalfEvent
    {Ω : Type*} {k m : ℕ}
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (ω₀ : Ω) (hm : 1 ≤ m) :
    grassmannQuarterBadEvent sample (sample ω₀) ⊆
      {ω | projectorComplementOverlap (sample ω₀) (sample ω) < (m : ℝ) / 2} := by
  intro ω hω
  exact projectorComplementOverlap_lt_half_of_mem_grassmannQuarterBadEvent
    sample ω ω₀ hm hω

/-- The `t = 1/4` Lowe--Nayak lower-tail threshold for the overlap between
a rank-`m` projector and a rank-`k-m` complementary projector. -/
def lownayakQuarterComplementThreshold (k m : ℕ) : ℝ :=
  (3 / 4 : ℝ) * ((m : ℝ) * ((k - m : ℕ) : ℝ) / (k : ℝ))

/-- The `t = 1/4` Lowe--Nayak Chernoff upper bound. -/
def lownayakQuarterComplementTailBound (k m : ℕ) : ℝ :=
  Real.exp (-(((k - m : ℕ) : ℝ) * (m : ℝ) / 32))

/-- In the manuscript range `3m ≤ k`, the threshold at one quarter below the
mean is at least `m/2`. -/
theorem half_rank_le_lownayakQuarterComplementThreshold
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k) :
    (m : ℝ) / 2 ≤ lownayakQuarterComplementThreshold k m := by
  have hmk : m ≤ k := le_trans (by omega : m ≤ 3 * m) hkm
  have hkpos_nat : 0 < k := lt_of_lt_of_le (by omega : 0 < 3 * m) hkm
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hkm_real : 3 * (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkm
  have hsub : ((k - m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub hmk]
  rw [lownayakQuarterComplementThreshold, hsub]
  rw [show (3 / 4 : ℝ) * ((m : ℝ) * ((k : ℝ) - (m : ℝ)) / (k : ℝ)) =
      ((3 / 4 : ℝ) * ((m : ℝ) * ((k : ℝ) - (m : ℝ)))) / (k : ℝ) by ring]
  apply (le_div_iff₀ hkpos).2
  nlinarith

/-- Consequently, every quarter trace-distance bad event lies in the exact
`t = 1/4` complementary-overlap lower-tail event. -/
theorem grassmannQuarterBadEvent_subset_lownayakQuarterComplementEvent
    {Ω : Type*} {k m : ℕ}
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (ω₀ : Ω) (hm : 1 ≤ m) (hkm : 3 * m ≤ k) :
    grassmannQuarterBadEvent sample (sample ω₀) ⊆
      {ω | projectorComplementOverlap (sample ω₀) (sample ω) <
        lownayakQuarterComplementThreshold k m} := by
  intro ω hω
  exact lt_of_lt_of_le
    (projectorComplementOverlap_lt_half_of_mem_grassmannQuarterBadEvent
      sample ω ω₀ hm hω)
    (half_rank_le_lownayakQuarterComplementThreshold hm hkm)

/-- The stronger Lowe--Nayak exponent implies the manuscript's exact
`25/4608` exponent throughout `3m ≤ k`. -/
theorem lownayakQuarterComplementTailBound_le_grassmannQuarterBadMassBound
    {k m : ℕ} (hkm : 3 * m ≤ k) :
    lownayakQuarterComplementTailBound k m ≤
      grassmannQuarterBadMassBound k m := by
  have hmk : m ≤ k := by omega
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hkm_real : 3 * (m : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkm
  have hprod : (m : ℝ) * (3 * (m : ℝ)) ≤ (m : ℝ) * (k : ℝ) :=
    mul_le_mul_of_nonneg_left hkm_real hm0
  have hsub : ((k - m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub hmk]
  rw [lownayakQuarterComplementTailBound, grassmannQuarterBadMassBound]
  apply Real.exp_le_exp.mpr
  rw [grassmannQuarterMetricExponent_eq_gamma0, grassmannGamma0, hsub]
  nlinarith

/-- Any probability-space realization of the scalar Lowe--Nayak tail gives
the one-ball estimate consumed by the already-proved greedy union packing. -/
theorem grassmannQuarterSelfSmallBall_of_lownayakComplementTail
    {Ω : Type*} [MeasurableSpace Ω]
    {k m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (htail : ∀ ω₀ : Ω,
      μ.real {ω | projectorComplementOverlap (sample ω₀) (sample ω) <
          lownayakQuarterComplementThreshold k m} ≤
        lownayakQuarterComplementTailBound k m) :
    ∀ ω₀ : Ω,
      μ.real (grassmannQuarterBadEvent sample (sample ω₀)) ≤
        grassmannQuarterBadMassBound k m := by
  intro ω₀
  calc
    μ.real (grassmannQuarterBadEvent sample (sample ω₀)) ≤
        μ.real {ω | projectorComplementOverlap (sample ω₀) (sample ω) <
          lownayakQuarterComplementThreshold k m} :=
      measureReal_mono
        (grassmannQuarterBadEvent_subset_lownayakQuarterComplementEvent
          sample ω₀ hm hkm)
    _ ≤ lownayakQuarterComplementTailBound k m := htail ω₀
    _ ≤ grassmannQuarterBadMassBound k m :=
      lownayakQuarterComplementTailBound_le_grassmannQuarterBadMassBound hkm

/-- The whole finite Grassmann packing follows once the exact scalar
projector-overlap lower tail is supplied on a probability space. -/
theorem exists_complexGrassmannPackingWitness_card_eq_of_lownayakComplementTail
    {Ω : Type*} [MeasurableSpace Ω]
    {k m : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (sample : Ω → RankMComplexOrthogonalProjector k m)
    (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (htail : ∀ ω₀ : Ω,
      μ.real {ω | projectorComplementOverlap (sample ω₀) (sample ω) <
          lownayakQuarterComplementThreshold k m} ≤
        lownayakQuarterComplementTailBound k m) :
    ∃ V : ComplexGrassmannPackingWitness k m,
      V.card = grassmannPackingCard k m := by
  exact exists_complexGrassmannPackingWitness_card_eq_of_probability_selfSmallBall
    μ sample hm
      (grassmannQuarterSelfSmallBall_of_lownayakComplementTail
        μ sample hm hkm htail)

end

end TomographyOracleCore
