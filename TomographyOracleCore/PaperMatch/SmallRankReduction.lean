import TomographyOracleCore.PaperMatch.RankThreeLower

/-! Rank two needs no separate packing. The actual physical minimax risk is
monotone in the rank class, and the rank-two target rate is at most twice
the pure-state rate. These reductions do not assume or assert the missing
pure-state statistical lower bound. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory PhysicalRisk
open scoped ENNReal
noncomputable section

theorem rankClass_mono {d r s : ℕ} (hrs : r ≤ s) :
    rankClass d r ⊆ rankClass d s := fun _ h => h.trans hrs

theorem rankClass_worstCaseRisk_mono {d T r s : ℕ} (hrs : r ≤ s)
    (design : Design d T) (estimator : Estimator d T) :
    Model.worstCaseRiskOn (rankClass d r) design estimator ≤
      Model.worstCaseRiskOn (rankClass d s) design estimator := by
  apply iSup_le
  intro rho
  exact le_iSup (fun sigma : rankClass d s =>
    statewiseExpectedTraceRisk design estimator sigma.1)
      ⟨rho.1, rankClass_mono hrs rho.2⟩

theorem rankClass_minimaxRisk_mono {d T r s : ℕ} (hrs : r ≤ s) :
    Model.minimaxRiskOn (T := T) (rankClass d r) ≤
      Model.minimaxRiskOn (T := T) (rankClass d s) := by
  apply iInf_mono
  intro design
  apply iInf_mono
  intro estimator
  exact rankClass_worstCaseRisk_mono hrs design estimator

theorem rankRate_nonneg (d T r : ℕ) : 0 ≤ rankRate d T r := by
  unfold rankRate
  positivity

theorem rankRate_le_rank_mul_pureRate (d T r : ℕ) (hr : 1 ≤ r) :
    rankRate d T r ≤ (r : ℝ) * rankRate d T 1 := by
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  simp only [rankRate, Nat.cast_one, one_mul]
  by_cases h : Real.sqrt ((d : ℝ) / T) ≤ 1
  · rw [min_eq_right h]
    exact min_le_right _ _
  · rw [min_eq_left (le_of_not_ge h)]
    simpa using (min_le_left 1 ((r : ℝ) * Real.sqrt ((d : ℝ) / T))).trans hrR

/-- A proved pure-state lower bound transfers to rank two with constant c/2.
The premise is deliberately visible: this is not itself a pure-state bound. -/
theorem rank_two_lower_of_pure_lower {d T : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (hpure : ENNReal.ofReal (c * rankRate d T 1) ≤
      Model.minimaxRiskOn (T := T) (rankClass d 1)) :
    ENNReal.ofReal ((c / 2) * rankRate d T 2) ≤
      Model.minimaxRiskOn (T := T) (rankClass d 2) := by
  have hrate := rankRate_le_rank_mul_pureRate d T 2 (by omega)
  have hscale : (c / 2) * rankRate d T 2 ≤ c * rankRate d T 1 := by
    have h := mul_le_mul_of_nonneg_left hrate (show 0 ≤ c / 2 by positivity)
    norm_num at h
    nlinarith
  exact (ENNReal.ofReal_le_ofReal hscale).trans
    (hpure.trans (rankClass_minimaxRisk_mono (by omega : 1 ≤ 2)))

/-- Once the pure-state endpoint is supplied, all ranks follow using the
already proved rank-at-least-three endpoint and a single positive constant. -/
theorem all_rank_lower_of_pure_lower {d T : ℕ} (hd : 514 ≤ d) (hT : 1 ≤ T)
    {c : ℝ} (hc : 0 < c)
    (hpure : ENNReal.ofReal (c * rankRate d T 1) ≤
      Model.minimaxRiskOn (T := T) (rankClass d 1))
    (r : ℕ) (hr : 1 ≤ r) (hrd : r ≤ d) :
    ENNReal.ofReal (min (c / 2) rankThreeLowerConstant * rankRate d T r) ≤
      Model.minimaxRiskOn (T := T) (rankClass d r) := by
  have hrate := rankRate_nonneg d T r
  rcases show r = 1 ∨ r = 2 ∨ 3 ≤ r by omega with h | h | h
  · subst r
    apply le_trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right
        ((min_le_left _ _).trans (show c / 2 ≤ c by linarith)) hrate)) hpure
  · subst r
    exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hrate)).trans
        (rank_two_lower_of_pure_lower hc.le hpure)
  · exact (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hrate)).trans
        (rank_minimax_lower_rank_ge_three d T r hd hT h hrd)

end
end TomographyOracleCore.PaperMatch.RankMinimax
