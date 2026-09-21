import TomographyOracleCore.DecayUpper
namespace TomographyOracleCore
noncomputable section

/-- Integer rounding with the loss cap and the decay exponent retained. -/
theorem decay_oracle_interior_beta_ten
    (err L eta beta : ℝ) (tail : ℕ → ℝ) (D : ℕ)
    (hL1 : 1 ≤ L) (heta : 0 < eta)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hu1 : 1 ≤ balancedScale L eta beta)
    (huD : balancedScale L eta beta ≤ (D : ℝ))
    (hcap : err ≤ 2)
    (horacle : OracleBound err tail (4 * eta) D)
    (htail : ∀ s, 1 ≤ s → s ≤ D → tail s ≤ L * (s : ℝ) ^ (1 - beta⁻¹)) :
    err ≤ 10 * polynomialRate L eta beta := by
  let u : ℝ := balancedScale L eta beta
  let s : ℕ := Nat.ceil u
  have hL : 0 < L := by linarith
  have hu : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hs1 : 1 ≤ s := Nat.ceil_pos.mpr hu
  have hsD : s ≤ D := Nat.ceil_le.mpr huD
  have hus : u ≤ (s : ℝ) := Nat.le_ceil u
  have hs : 0 < (s : ℝ) := by exact_mod_cast hs1
  have hceil : (s : ℝ) < u + 1 := Nat.ceil_lt_add_one hu.le
  have hs2 : (s : ℝ) ≤ 2 * u := by linarith
  have hexp : 1 - beta⁻¹ ≤ 0 := by
    have hi := (one_lt_inv₀ hbeta0).mpr hbeta1
    linarith
  have hbalanced : L * u ^ (1 - beta⁻¹) = polynomialRate L eta beta :=
    approximation_at_balanced_scale L eta beta hL heta hbeta0.ne'
  have hscale : eta * u = polynomialRate L eta beta :=
    estimation_at_balanced_scale L eta beta heta
  have hraw := horacle s hs1 hsD
  have htail_s := htail s hs1 hsD
  have happrox : L * (s : ℝ) ^ (1 - beta⁻¹) ≤ polynomialRate L eta beta := by
    rw [← hbalanced]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu hus hexp) hL.le
  by_cases hu2 : 2 ≤ u
  · have hs32 : (s : ℝ) ≤ (3 / 2 : ℝ) * u := by linarith
    have hmul := mul_le_mul_of_nonneg_left hs32 heta.le
    nlinarith
  · by_cases hbeta : beta⁻¹ ≤ 2
    · have hu2' : u ≤ 2 := le_of_not_ge hu2
      have hinv : (1 / 2 : ℝ) ≤ u⁻¹ := by
        have hh := one_div_le_one_div_of_le hu hu2'
        simpa only [one_div] using hh
      have hp : u⁻¹ ≤ u ^ (1 - beta⁻¹) := by
        simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le hu1 (show (-1 : ℝ) ≤ 1 - beta⁻¹ by linarith)
      have hm := mul_le_mul_of_nonneg_right hL1 (Real.rpow_nonneg hu.le (1 - beta⁻¹))
      nlinarith
    · have hexp2 : 2 - beta⁻¹ ≤ 0 := by linarith
      have hpowers (x : ℝ) (hx : 0 < x) :
          x ^ (1 - beta⁻¹) * x = x ^ (2 - beta⁻¹) := by
        calc
          _ = x ^ (1 - beta⁻¹) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
          _ = x ^ ((1 - beta⁻¹) + 1) := (Real.rpow_add hx _ _).symm
          _ = _ := by congr 1; ring
      have hp : L * (s : ℝ) ^ (1 - beta⁻¹) * (s : ℝ) ≤
          polynomialRate L eta beta * u := by
        calc
          _ = L * (s : ℝ) ^ (2 - beta⁻¹) := by rw [mul_assoc, hpowers _ hs]
          _ ≤ L * u ^ (2 - beta⁻¹) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hu hus hexp2) hL.le
          _ = _ := by rw [← hpowers _ hu, ← mul_assoc, hbalanced]
      have hquad := mul_nonpos_of_nonpos_of_nonneg
        (show (s : ℝ) - 2 * u ≤ 0 by linarith)
        (show 0 ≤ 2 * (s : ℝ) - u by linarith)
      have hscaledQuad := mul_nonpos_of_nonneg_of_nonpos heta.le hquad
      have hrawScaled := mul_le_mul_of_nonneg_right hraw hs.le
      have htailScaled := mul_le_mul_of_nonneg_right htail_s hs.le
      rw [← hscale] at hp ⊢
      apply (mul_le_mul_iff_left₀ hs).mp
      nlinarith

theorem decay_oracle_polynomial_beta_ten
    (err L eta beta : ℝ) (tail : ℕ → ℝ) (D : ℕ)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (heta : 0 < eta)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hcap : err ≤ 2)
    (horacle : OracleBound err tail (4 * eta) D)
    (htail : ∀ s, 1 ≤ s → s ≤ D →
      tail s ≤ L * (s : ℝ) ^ (1 - beta⁻¹))
    (htailD : tail D = 0) :
    err ≤ 10 * polynomialRate L eta beta := by
  let u : ℝ := balancedScale L eta beta
  have hu_pos : 0 < u := by
    dsimp [u, balancedScale]
    exact mul_pos (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL) beta)
      (Real.rpow_pos_of_pos heta (-beta))
  have hexp : 1 - beta⁻¹ ≤ 0 := by
    have hone_inv : 1 < beta⁻¹ := (one_lt_inv₀ hbeta0).mpr hbeta1
    linarith
  by_cases hu1 : 1 ≤ u
  · by_cases huD : u ≤ (D : ℝ)
    · exact decay_oracle_interior_beta_ten err L eta beta tail D
        hL heta hbeta0 hbeta1 hu1 huD hcap
        horacle htail
    · have hDu : (D : ℝ) ≤ u := le_of_not_ge huD
      have hfull : err ≤ (4 * eta) * (D : ℝ) := by
        simpa [htailD] using horacle D hD le_rfl
      have hscale : eta * u = polynomialRate L eta beta := by
        simpa [u] using estimation_at_balanced_scale L eta beta heta
      have hDscale : eta * (D : ℝ) ≤ polynomialRate L eta beta := by
        calc
          eta * (D : ℝ) ≤ eta * u :=
            mul_le_mul_of_nonneg_left hDu heta.le
          _ = polynomialRate L eta beta := hscale
      nlinarith
  · have hu_le_one : u ≤ 1 := le_of_not_ge hu1
    have hpow : 1 ≤ u ^ (1 - beta⁻¹) := by
      have := Real.rpow_le_rpow_of_nonpos hu_pos hu_le_one hexp
      simpa using this
    have hrate_one : 1 ≤ polynomialRate L eta beta := by
      have hbalanced :=
        approximation_at_balanced_scale L eta beta
          (lt_of_lt_of_le zero_lt_one hL) heta hbeta0.ne'
      have hLu : 1 ≤ L * u ^ (1 - beta⁻¹) := by nlinarith
      rw [← hbalanced]
      simpa [u] using hLu
    nlinarith

/-- Complete three-regime deterministic decay upper bound.  The three terms
are the loss cap, the polynomial-decay rate, and the full-rank rate. -/
theorem decay_oracle_three_regime_beta_ten
    (err L eta beta : ℝ) (tail : ℕ → ℝ) (D : ℕ)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (heta : 0 < eta)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hcap : err ≤ 2)
    (horacle : OracleBound err tail (4 * eta) D)
    (htail : ∀ s, 1 ≤ s → s ≤ D →
      tail s ≤ L * (s : ℝ) ^ (1 - beta⁻¹))
    (htailD : tail D = 0) :
    err ≤ 10 * min 1
      (min (polynomialRate L eta beta) (eta * (D : ℝ))) := by
  have hpoly := decay_oracle_polynomial_beta_ten err L eta beta tail D hD hL
    heta hbeta0 hbeta1 hcap horacle htail htailD
  have hfull : err ≤ 10 * (eta * (D : ℝ)) := by
    have hraw : err ≤ (4 * eta) * (D : ℝ) := by
      simpa [htailD] using horacle D hD le_rfl
    nlinarith
  have hcap' : err ≤ 10 * 1 := by linarith
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10)]
  apply le_min hcap'
  rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 10)]
  exact le_min hpoly hfull

/-- The same theorem in the usual exponent `alpha > 1` rather than the
reciprocal exponent `beta = 1 / alpha`. -/
theorem decay_oracle_three_regime_ten
    (err L eta alpha : ℝ) (tail : ℕ → ℝ) (D : ℕ)
    (hD : 1 ≤ D) (hL : 1 ≤ L) (heta : 0 < eta)
    (halpha : 1 < alpha) (hcap : err ≤ 2)
    (horacle : OracleBound err tail (4 * eta) D)
    (htail : ∀ s, 1 ≤ s → s ≤ D →
      tail s ≤ L * (s : ℝ) ^ (1 - alpha))
    (htailD : tail D = 0) :
    err ≤ 10 * min 1
      (min (L ^ alpha⁻¹ * eta ^ ((alpha - 1) / alpha))
        (eta * (D : ℝ))) := by
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hbeta0 : 0 < alpha⁻¹ := inv_pos.mpr halpha0
  have hbeta1 : alpha⁻¹ < 1 := (inv_lt_one₀ halpha0).mpr halpha
  have h := decay_oracle_three_regime_beta_ten err L eta alpha⁻¹ tail D
    hD hL heta hbeta0 hbeta1 hcap horacle (by
      intro s hs1 hsD
      simpa using htail s hs1 hsD) htailD
  rw [polynomialRate_reciprocal L eta alpha halpha0.ne'] at h
  exact h

end
end TomographyOracleCore
