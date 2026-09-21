import TomographyOracleCore.Revision.FixedNormBaiYinTransport
import TomographyOracleCore.Revision.PeriodicBornCovarianceNorms

namespace TomographyOracleCore.Revision.PeriodicBornRealConcentration

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance Candidate2FiniteBornVectorLaw
open FixedNormBaiYinTransport PeriodicBornMoments PeriodicBornCovarianceNorms
open scoped RealInnerProductSpace
noncomputable section

local instance {D : ℕ} : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

theorem effective_rank_rate_scalar {d s t : ℝ}
    (hd : 1 ≤ d) (hs : 0 < s) (hs2 : s ≤ 2) (ht : 0 < t) :
    s * Real.sqrt (((d + 1) / s) / t) ≤ 2 * Real.sqrt (d / t) := by
  calc
    _ = Real.sqrt (s * (d + 1) / t) := by
      nth_rw 1 [← Real.sqrt_sq hs.le]
      rw [← Real.sqrt_mul (sq_nonneg s)]
      congr 1
      field_simp
    _ ≤ Real.sqrt (4 * (d / t)) := by
      apply Real.sqrt_le_sqrt
      rw [← mul_div_assoc]
      apply div_le_div_of_nonneg_right _ ht.le
      nlinarith
    _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num

/-- Sharp concentration for the realified physical Born covariance, now
derived from the single general published input and the proved circuit
moments and the proved general covariance theorem. No scientific axiom is used. -/
theorem periodic_real_expected_covariance :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (H : ChoKimBlockCondition n K),
        0 < n → 0 < T → c * (((2 ^ n : ℕ) : ℝ)) ≤ (T : ℝ) →
        ∀ rho : MatrixReduction.DensityOperator (Fin (2 ^ n)),
          let mu := choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
          (∫ X : Fin T → EuclideanSpace ℂ (Fin (2 ^ n)),
            ‖sampleCovariance X - populationCovariance mu‖
              ∂Measure.pi (fun _ : Fin T => mu)) ≤
            A * Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := fixedNorm_baiYin_finiteDimensional 4 (by norm_num)
  refine ⟨12 * c, 2 * C, by linarith, by positivity, ?_⟩
  intro n K T H hn hT hsize rho
  let mu := choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho
  letI : IsProbabilityMeasure mu := choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability H.block_dvd rho
  let d : ℝ := ((2 ^ n : ℕ) : ℝ)
  let s : ℝ := ‖populationCovariance mu‖
  have hd : 1 ≤ d := by dsimp [d]; exact_mod_cast Nat.one_le_pow n 2 (by decide)
  have hs := periodic_real_covariance_norm_bounds H hn rho
  have hspos : 0 < s := by dsimp [s, mu]; linarith [hs.1]
  have hs2 : s ≤ 2 := by dsimp [s, mu]; linarith [hs.2]
  have hratio : (d + 1) / s ≤ 12 * d := by
    apply (div_le_iff₀ hspos).2
    have hsd : (1 / 6) * d ≤ s * d := mul_le_mul_of_nonneg_right hs.1 (by positivity)
    nlinarith
  have hthreshold : c * ((d + 1) / s) ≤ (T : ℝ) := by
    calc
      _ ≤ c * (12 * d) := mul_le_mul_of_nonneg_left hratio (by linarith)
      _ = (12 * c) * d := by ring
      _ ≤ _ := hsize
  have htrunc : d + 1 ≤ (T : ℝ) * s := by
    apply (div_le_iff₀ hspos).1
    calc
      (d + 1) / s ≤ c * ((d + 1) / s) := by
        nlinarith [div_nonneg (by positivity : 0 ≤ d + 1) hspos.le]
      _ ≤ _ := hthreshold
  have hbound := hmain (EuclideanSpace ℂ (Fin (2 ^ n))) T hT mu (d + 1)
    (by positivity) (integral_id_choKimPeriodicPhaseRandomizedBornVectorLaw_eq_zero H.block_dvd rho)
    (ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw H.block_dvd rho)
    (periodic_born_hasL6L2 H hn rho) hthreshold htrunc
  refine hbound.trans ?_
  change C * s * Real.sqrt (((d + 1) / s) / (T : ℝ)) ≤ (2 * C) * Real.sqrt (d / (T : ℝ))
  have hr := mul_le_mul_of_nonneg_left
    (effective_rank_rate_scalar (t := (T : ℝ)) hd hspos hs2 (by exact_mod_cast hT)) hC.le
  nlinarith

end
end TomographyOracleCore.Revision.PeriodicBornRealConcentration
