import TomographyOracleCore.Revision.PhysicalFourthExpansion
import TomographyOracleCore.Revision.FourthMeasurementMoment
import TomographyOracleCore.PeriodicCliffordFourthChoKimBridge
import TomographyOracleCore.PaperMatch.SectionV.OperatorMoment

namespace TomographyOracleCore.Revision.PeriodicUniformFourthMoment

open BornFourthMoment FourthMeasurementMoment FourthVectorBoundary FourthBoundaryReindex
open PhysicalFourthExpansion CliffordFourthBasisInput FourthTwirlTensorization
open scoped BigOperators InnerProductSpace
noncomputable section

local instance (K : ℕ) : DecidableEq (PauliBinaryWord K) :=
  fun a b => Fintype.decidablePiFintype a b

/-- Exact circuit-to-transfer bound after transporting the binary register
to any enumeration of its computational basis. -/
theorem periodicUniformEighth_le_transfer {D m h : ℕ}
    (hD : 0 < D) (e : PauliBinaryWord (m * (2 * h)) ≃ Fin D)
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    finiteUnitaryUniformEighthMoment
      (fun t => reindexUnitary e (periodicTwoLayerCliffordUnitary m (2 * h)
        (cyclicQubitShift (m * (2 * h)) h) t)) u ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ (2 * m)).trace := by
  obtain ⟨v, rfl⟩ := (vectorReindex e).surjective u
  have hv : ‖v‖ = 1 := by simpa only [(vectorReindex e).norm_map] using hu
  rw [← PaperMatch.SectionV.uniformOverlapMoment_eq_finiteUniformEighth,
    PaperMatch.SectionV.uniformOverlapMoment_reindex]
  have h7 := PaperMatch.SectionV.uniformOverlapMoment_sector_expansion hm hh hK v
  have h8 := fun zeta => PaperMatch.SectionV.boundary_norm_le_one m h zeta v hv
  exact (PaperMatch.SectionV.real_moment_le_sum_abs _ _ _ h7 h8).trans
    (PaperMatch.SectionV.sum_abs_coefficients_le_trace hm hK)

theorem periodicUniformEighth_le_thirtyFour {D m h : ℕ}
    (hD : 65536 ≤ D) (e : PauliBinaryWord (m * (2 * h)) ≃ Fin D)
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (hdim : (D : ℝ) = (((2 : ℝ) ^ h) ^ 2) ^ m)
    (hblock : PeriodicCliffordFourthBlockPredicate m ((2 : ℝ) ^ h))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    finiteUnitaryUniformEighthMoment
      (fun t => reindexUnitary e (periodicTwoLayerCliffordUnitary m (2 * h)
        (cyclicQubitShift (m * (2 * h)) h) t)) u ≤
      34 / ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2) * ((D : ℝ) + 3)) := by
  apply periodicCliffordFourthU4_of_concreteExpansion
    (boundary := 1) (qubitFourthGramMatrix ((2 : ℝ) ^ h)) hD hdim hblock
    (qubitFourthGramMatrix_nonneg (by positivity))
    (qubitFourthGramMatrix_all_rowSums _) (by norm_num) (by norm_num)
  have hb := periodicUniformEighth_le_transfer (by omega : 0 < D) e hm hh hK u hu
  simpa only [one_mul, ← pow_mul, Nat.mul_comm h 2] using hb

set_option maxHeartbeats 1000000 in
/-- The concrete Pauli-coset periodic ensemble satisfies the uniform
eighth-overlap estimate. The proof directly invokes the scalar form of
Lemma 7 and the boundary bound of Lemma 8, then the coefficient and scalar
estimates. Identifying this ensemble with the paper's full uniform
projective-Clifford law is a separate correspondence obligation. -/
theorem periodic_uniform_eighth {n K : ℕ} (H : ChoKimBlockCondition n K) (hn : 0 < n)
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    finiteUnitaryUniformEighthMoment (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) u ≤
      34 / (((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) : ℝ) + 1) *
        (((2 ^ n : ℕ) : ℝ) + 2) * (((2 ^ n : ℕ) : ℝ) + 3)) := by
  obtain ⟨r, hr⟩ := H.block_even
  have hKr : K = 2 * r := by omega
  clear hr
  subst K
  have hhalf : (2 * r) / 2 = r := by omega
  have hr8 : 8 ≤ r := by
    have hover := H.oneTwentyEight_lt_overlap hn
    simp only [choKimOverlapDimension, hhalf] at hover
    by_contra hnot
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (show r ≤ 7 by omega)
    norm_num at hp
    linarith
  have hd := H.periodicCliffordFourth_dimension
  have hb := H.periodicCliffordFourth_blockPredicate hn
  simp only [choKimOverlapDimension, hhalf] at hd hb
  have hfun : choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd =
      (fun t => reindexUnitary (computableChoKimBlockIndex H.block_dvd)
        (periodicTwoLayerCliffordUnitary (n / (2 * r)) (2 * r)
          (cyclicQubitShift ((n / (2 * r)) * (2 * r)) r) t)) := by
    funext t
    unfold choKimPeriodicTwoLayerCliffordUnitaryFin choKimPeriodicTwoLayerCliffordUnitary
    rw [hhalf]
  rw [hfun]
  let e := computableChoKimBlockIndex H.block_dvd
  obtain ⟨v, rfl⟩ := (vectorReindex e).surjective u
  have hv : ‖v‖ = 1 := by simpa only [(vectorReindex e).norm_map] using hu
  rw [← PaperMatch.SectionV.uniformOverlapMoment_eq_finiteUniformEighth,
    PaperMatch.SectionV.uniformOverlapMoment_reindex]
  -- Lemma 7: the actual eighth moment is the signed sector contraction.
  have h7 := PaperMatch.SectionV.uniformOverlapMoment_sector_expansion
    (H.blockQuotient_pos hn) (by omega : 0 < r) (by omega : 3 ≤ 2 * r) v
  -- Lemma 8: every boundary has absolute value at most one, including
  -- entangled v. This theorem now uses the arbitrary-block formulation.
  have h8 := fun zeta =>
    PaperMatch.SectionV.boundary_norm_le_one (n / (2 * r)) r zeta v hv
  have hl1 := PaperMatch.SectionV.real_moment_le_sum_abs _ _ _ h7 h8
  have htransfer := hl1.trans (PaperMatch.SectionV.sum_abs_coefficients_le_trace
    (H.blockQuotient_pos hn) (by omega : 3 ≤ 2 * r))
  -- The remaining steps are the cycle trace and scalar normalization.
  apply periodicCliffordFourthU4_of_concreteExpansion
    (boundary := 1) (qubitFourthGramMatrix ((2 : ℝ) ^ r))
    (H.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn) hd hb
    (qubitFourthGramMatrix_nonneg (by positivity))
    (qubitFourthGramMatrix_all_rowSums _) (by norm_num) (by norm_num)
  simpa only [one_mul, ← pow_mul, Nat.mul_comm r 2] using htransfer

/-- Literal supremum form of Theorem 9 for the same concrete gate law.
The pointwise theorem above provides the bound for every unit test vector. -/
theorem periodic_uniform_eighth_sup {n K : ℕ}
    (H : ChoKimBlockCondition n K) (hn : 0 < n) :
    sSup {t : ℝ | ∃ u : EuclideanSpace ℂ (Fin (2 ^ n)),
      ‖u‖ = 1 ∧
        finiteUnitaryUniformEighthMoment
          (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) u = t} ≤
      34 / (((2 ^ n : ℕ) : ℝ) * (((2 ^ n : ℕ) : ℝ) + 1) *
        (((2 ^ n : ℕ) : ℝ) + 2) * (((2 ^ n : ℕ) : ℝ) + 3)) := by
  have hnonempty : Set.Nonempty {t : ℝ | ∃ u : EuclideanSpace ℂ (Fin (2 ^ n)),
      ‖u‖ = 1 ∧
        finiteUnitaryUniformEighthMoment
          (choKimPeriodicTwoLayerCliffordUnitaryFin H.block_dvd) u = t} := by
    let i : Fin (2 ^ n) := ⟨0, pow_pos (by decide) n⟩
    let u : EuclideanSpace ℂ (Fin (2 ^ n)) := PiLp.single 2 i 1
    refine ⟨_, u, ?_, rfl⟩
    simp [u, PiLp.norm_single]
  apply csSup_le hnonempty
  rintro t ⟨u, hu, rfl⟩
  exact periodic_uniform_eighth H hn u hu

end
end TomographyOracleCore.Revision.PeriodicUniformFourthMoment
