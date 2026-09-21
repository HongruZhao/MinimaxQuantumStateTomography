import TomographyOracleCore.MathlibImports
import TomographyOracleCore.Algebra
import TomographyOracleCore.Structural

namespace TomographyOracleCore

/-!
Deterministic algebra for the effective-rank optimization in the proposed
decay-class lower bound.

This module proves only the scalar statement that follows *after* a primitive
lower bound has been established at every admissible integer rank.  It does
not construct a Grassmann packing, analyze a Haar rotation, bound mutual
information, or invoke Fano's inequality.
-/

/-- Value of the three competing lower-bound restrictions at an integer
effective rank `m`, in reciprocal-exponent notation `beta = 1 / alpha`. -/
noncomputable def decayLowerValueBeta
    (m : ℕ) (L eta beta : ℝ) : ℝ :=
  min 1 (min
    (L * (m : ℝ) ^ (1 - beta⁻¹))
    ((m : ℝ) * eta))

/-- The continuous three-regime target corresponding to
`decayLowerValueBeta`: the loss cap, the balanced polynomial rate, and the
right endpoint `M * eta`. -/
noncomputable def decayLowerRateBeta
    (M : ℕ) (L eta beta : ℝ) : ℝ :=
  min 1 (min
    (polynomialRate L eta beta)
    ((M : ℝ) * eta))

/-- Usual `alpha`-notation for the integer lower-envelope value. -/
noncomputable def decayLowerValue
    (m : ℕ) (L eta alpha : ℝ) : ℝ :=
  min 1 (min
    (L * (m : ℝ) ^ (1 - alpha))
    ((m : ℝ) * eta))

/-- Usual `alpha`-notation for the three-regime lower target. -/
noncomputable def decayLowerRate
    (M : ℕ) (L eta alpha : ℝ) : ℝ :=
  min 1 (min
    (L ^ alpha⁻¹ * eta ^ ((alpha - 1) / alpha))
    ((M : ℝ) * eta))

/-- Every admissible integer-rank value is at most the continuous
three-regime target.  The proof compares `m` with the balancing scale instead
of using a weighted geometric-mean inequality. -/
theorem decayLowerValueBeta_le_rate
    (m M : ℕ) (L eta beta : ℝ)
    (hm1 : 1 ≤ m) (hmM : m ≤ M)
    (hL : 0 < L) (heta : 0 < eta)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    decayLowerValueBeta m L eta beta ≤
      decayLowerRateBeta M L eta beta := by
  let u : ℝ := balancedScale L eta beta
  let p : ℝ := polynomialRate L eta beta
  have hu : 0 < u := by
    dsimp [u, balancedScale]
    exact mul_pos (Real.rpow_pos_of_pos hL beta)
      (Real.rpow_pos_of_pos heta (-beta))
  have hexp : 1 - beta⁻¹ < 0 := by
    have hinv : 1 < beta⁻¹ := (one_lt_inv₀ hbeta0).mpr hbeta1
    linarith
  have hest : eta * u = p := by
    simpa [u, p] using estimation_at_balanced_scale L eta beta heta
  have happ : L * u ^ (1 - beta⁻¹) = p := by
    simpa [u, p] using approximation_at_balanced_scale L eta beta
      hL heta hbeta0.ne'
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm1
  have hMcast : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmM
  have hvalue_one : decayLowerValueBeta m L eta beta ≤ 1 :=
    min_le_left _ _
  have hvalue_endpoint :
      decayLowerValueBeta m L eta beta ≤ (M : ℝ) * eta := by
    calc
      decayLowerValueBeta m L eta beta ≤ (m : ℝ) * eta :=
        (min_le_right _ _).trans (min_le_right _ _)
      _ ≤ (M : ℝ) * eta :=
        mul_le_mul_of_nonneg_right hMcast heta.le
  have hvalue_balanced : decayLowerValueBeta m L eta beta ≤ p := by
    by_cases hmu : (m : ℝ) ≤ u
    · calc
        decayLowerValueBeta m L eta beta ≤ (m : ℝ) * eta :=
          (min_le_right _ _).trans (min_le_right _ _)
        _ ≤ u * eta := mul_le_mul_of_nonneg_right hmu heta.le
        _ = eta * u := by ring
        _ = p := hest
    · have hum : u ≤ (m : ℝ) := le_of_not_ge hmu
      have hrpow :
          (m : ℝ) ^ (1 - beta⁻¹) ≤ u ^ (1 - beta⁻¹) :=
        Real.rpow_le_rpow_of_nonpos hu hum hexp.le
      calc
        decayLowerValueBeta m L eta beta ≤
            L * (m : ℝ) ^ (1 - beta⁻¹) :=
          (min_le_right _ _).trans (min_le_left _ _)
        _ ≤ L * u ^ (1 - beta⁻¹) :=
          mul_le_mul_of_nonneg_left hrpow hL.le
        _ = p := happ
  apply le_min hvalue_one
  exact le_min hvalue_balanced hvalue_endpoint

/-- Exact discrete lower-envelope optimization up to the factor two caused
by flooring the interior balancing scale.  It supplies a concrete admissible
integer `m` and includes both endpoint regimes. -/
theorem exists_decayLowerValueBeta_ge_half_rate
    (M : ℕ) (L eta beta : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (heta : 0 < eta)
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧
      decayLowerRateBeta M L eta beta / 2 ≤
        decayLowerValueBeta m L eta beta := by
  let u : ℝ := balancedScale L eta beta
  let p : ℝ := polynomialRate L eta beta
  let R : ℝ := decayLowerRateBeta M L eta beta
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hu : 0 < u := by
    dsimp [u, balancedScale]
    exact mul_pos (Real.rpow_pos_of_pos hLpos beta)
      (Real.rpow_pos_of_pos heta (-beta))
  have hp : 0 < p := by
    dsimp [p, polynomialRate]
    exact mul_pos (Real.rpow_pos_of_pos hLpos beta)
      (Real.rpow_pos_of_pos heta (1 - beta))
  have hMpos : 0 < (M : ℝ) := by exact_mod_cast hM
  have hR0 : 0 ≤ R := by
    dsimp [R, decayLowerRateBeta]
    exact le_min zero_le_one
      (le_min hp.le (mul_nonneg hMpos.le heta.le))
  have hR_one : R ≤ 1 := by
    dsimp [R, decayLowerRateBeta]
    exact min_le_left _ _
  have hR_p : R ≤ p := by
    dsimp [R, decayLowerRateBeta, p]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hR_endpoint : R ≤ (M : ℝ) * eta := by
    dsimp [R, decayLowerRateBeta]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hexp : 1 - beta⁻¹ < 0 := by
    have hinv : 1 < beta⁻¹ := (one_lt_inv₀ hbeta0).mpr hbeta1
    linarith
  have hest : eta * u = p := by
    simpa [u, p] using estimation_at_balanced_scale L eta beta heta
  have happ : L * u ^ (1 - beta⁻¹) = p := by
    simpa [u, p] using approximation_at_balanced_scale L eta beta
      hLpos heta hbeta0.ne'
  by_cases hu1 : u < 1
  · refine ⟨1, le_rfl, hM, ?_⟩
    have hone_rpow : 1 ≤ u ^ (1 - beta⁻¹) := by
      have h := Real.rpow_le_rpow_of_nonpos hu hu1.le hexp.le
      simpa using h
    have hp_one : 1 ≤ p := by
      rw [← happ]
      nlinarith
    have heta_one : 1 ≤ eta := by
      have heu : eta * u ≤ eta := by
        nlinarith
      rw [hest] at heu
      exact hp_one.trans heu
    have hhalf_one : R / 2 ≤ 1 := by nlinarith
    have hhalf_L : R / 2 ≤ L := hhalf_one.trans hL
    have hhalf_eta : R / 2 ≤ eta := hhalf_one.trans heta_one
    simpa [decayLowerValueBeta] using
      (le_min hhalf_one (le_min hhalf_L hhalf_eta))
  · have hu_one : 1 ≤ u := le_of_not_gt hu1
    by_cases huM : u ≤ (M : ℝ)
    · let m : ℕ := ⌊u⌋₊
      have hm1 : 1 ≤ m := by
        dsimp [m]
        exact Nat.floor_pos.mpr hu_one
      have hm_le_u : (m : ℝ) ≤ u := by
        dsimp [m]
        exact Nat.floor_le hu.le
      have hmM : m ≤ M := by
        exact_mod_cast hm_le_u.trans huM
      have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm1
      have hu_lt_m_one : u < (m : ℝ) + 1 := by
        simpa [m] using Nat.lt_floor_add_one u
      have hu_le_two_m : u ≤ 2 * (m : ℝ) := by
        have hmcast_one : 1 ≤ (m : ℝ) := by exact_mod_cast hm1
        linarith
      have htail : p ≤ L * (m : ℝ) ^ (1 - beta⁻¹) := by
        have hrpow :
            u ^ (1 - beta⁻¹) ≤ (m : ℝ) ^ (1 - beta⁻¹) :=
          Real.rpow_le_rpow_of_nonpos hmpos hm_le_u hexp.le
        rw [← happ]
        exact mul_le_mul_of_nonneg_left hrpow hLpos.le
      have hnoise : p / 2 ≤ (m : ℝ) * eta := by
        have hscaled : eta * u ≤ eta * (2 * (m : ℝ)) :=
          mul_le_mul_of_nonneg_left hu_le_two_m heta.le
        rw [hest] at hscaled
        nlinarith
      have hhalf_one : R / 2 ≤ 1 := by nlinarith
      have hhalf_tail :
          R / 2 ≤ L * (m : ℝ) ^ (1 - beta⁻¹) := by
        have : R / 2 ≤ p := by nlinarith
        exact this.trans htail
      have hhalf_noise : R / 2 ≤ (m : ℝ) * eta := by
        have : R / 2 ≤ p / 2 := by linarith
        exact this.trans hnoise
      refine ⟨m, hm1, hmM, ?_⟩
      exact le_min hhalf_one (le_min hhalf_tail hhalf_noise)
    · have hMu : (M : ℝ) < u := lt_of_not_ge huM
      have htail : p ≤ L * (M : ℝ) ^ (1 - beta⁻¹) := by
        have hrpow :
            u ^ (1 - beta⁻¹) ≤ (M : ℝ) ^ (1 - beta⁻¹) :=
          Real.rpow_le_rpow_of_nonpos hMpos hMu.le hexp.le
        rw [← happ]
        exact mul_le_mul_of_nonneg_left hrpow hLpos.le
      have hR_tail : R ≤ L * (M : ℝ) ^ (1 - beta⁻¹) :=
        hR_p.trans htail
      have hR_noise : R ≤ (M : ℝ) * eta := hR_endpoint
      have hR_value : R ≤ decayLowerValueBeta M L eta beta := by
        exact le_min hR_one (le_min hR_tail hR_noise)
      refine ⟨M, hM, le_rfl, ?_⟩
      have : R / 2 ≤ R := by nlinarith
      exact this.trans hR_value

/-- In `alpha > 1` notation, the maximum over admissible integer ranks is
sandwiched between one half and one times the advertised three-regime rate.
The statement is phrased through pointwise upper bounds and an explicit
witness, so it does not hide a choice of a finite maximum. -/
theorem discrete_decayLower_envelope_optimization
    (M : ℕ) (L eta alpha : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (heta : 0 < eta)
    (halpha : 1 < alpha) :
    (∀ m : ℕ, 1 ≤ m → m ≤ M →
      decayLowerValue m L eta alpha ≤ decayLowerRate M L eta alpha) ∧
    (∃ m : ℕ, 1 ≤ m ∧ m ≤ M ∧
      decayLowerRate M L eta alpha / 2 ≤
        decayLowerValue m L eta alpha) := by
  have halpha0 : 0 < alpha := lt_trans zero_lt_one halpha
  have hbeta0 : 0 < alpha⁻¹ := inv_pos.mpr halpha0
  have hbeta1 : alpha⁻¹ < 1 := (inv_lt_one₀ halpha0).mpr halpha
  constructor
  · intro m hm1 hmM
    have h := decayLowerValueBeta_le_rate m M L eta alpha⁻¹ hm1 hmM
      (lt_of_lt_of_le zero_lt_one hL) heta hbeta0 hbeta1
    simpa [decayLowerValueBeta, decayLowerRateBeta, decayLowerValue,
      decayLowerRate, polynomialRate_reciprocal L eta alpha halpha0.ne']
      using h
  · rcases exists_decayLowerValueBeta_ge_half_rate M L eta alpha⁻¹
      hM hL heta hbeta0 hbeta1 with ⟨m, hm1, hmM, hm⟩
    refine ⟨m, hm1, hmM, ?_⟩
    simpa [decayLowerValueBeta, decayLowerRateBeta, decayLowerValue,
      decayLowerRate, polynomialRate_reciprocal L eta alpha halpha0.ne']
      using hm

/-- If a scientific argument supplies a primitive lower bound at every
integer effective rank, the discrete optimization removes that rank and
loses only the explicit factor two. -/
theorem decayLowerRate_le_risk_of_primitive
    (risk lowerConstant : ℝ) (M : ℕ) (L eta alpha : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (heta : 0 < eta)
    (halpha : 1 < alpha) (hlowerConstant : 0 ≤ lowerConstant)
    (hprimitive : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      lowerConstant * decayLowerValue m L eta alpha ≤ risk) :
    (lowerConstant / 2) * decayLowerRate M L eta alpha ≤ risk := by
  rcases (discrete_decayLower_envelope_optimization M L eta alpha
    hM hL heta halpha).2 with ⟨m, hm1, hmM, hm⟩
  calc
    (lowerConstant / 2) * decayLowerRate M L eta alpha =
        lowerConstant * (decayLowerRate M L eta alpha / 2) := by ring
    _ ≤ lowerConstant * decayLowerValue m L eta alpha :=
      mul_le_mul_of_nonneg_left hm hlowerConstant
    _ ≤ risk := hprimitive m hm1 hmM

/-- Conditional minimax implication using the genuine unrestricted and
fixed-design infima.  Only the per-rank primitive lower bound and the chosen
fixed-design upper bound remain as premises; experiment inclusion, integer
optimization, endpoints, and the factor two are discharged in Lean. -/
theorem two_experiment_minimax_of_primitive_decay_lower
    {Design Estimator : Type*} [Nonempty Estimator]
    (risk : Design → Estimator → ℝ)
    (hrisk : ∀ design estimator, 0 ≤ risk design estimator)
    (design : Design) (M : ℕ) (L eta alpha : ℝ)
    (lowerConstant upperConstant : ℝ)
    (hM : 1 ≤ M) (hL : 1 ≤ L) (heta : 0 < eta)
    (halpha : 1 < alpha) (hlowerConstant : 0 ≤ lowerConstant)
    (hprimitive : ∀ m : ℕ, 1 ≤ m → m ≤ M →
      lowerConstant * decayLowerValue m L eta alpha ≤
        unrestrictedRisk risk)
    (hupper : fixedDesignRisk risk design ≤
      upperConstant * decayLowerRate M L eta alpha) :
    ((lowerConstant / 2) * decayLowerRate M L eta alpha ≤
        unrestrictedRisk risk ∧
      unrestrictedRisk risk ≤
        upperConstant * decayLowerRate M L eta alpha) ∧
    ((lowerConstant / 2) * decayLowerRate M L eta alpha ≤
        fixedDesignRisk risk design ∧
      fixedDesignRisk risk design ≤
        upperConstant * decayLowerRate M L eta alpha) := by
  have hlower := decayLowerRate_le_risk_of_primitive
    (unrestrictedRisk risk) lowerConstant M L eta alpha hM hL heta halpha
    hlowerConstant hprimitive
  exact two_experiment_minimax_of_infima risk hrisk design
    (decayLowerRate M L eta alpha) (lowerConstant / 2) upperConstant
    hlower hupper

end TomographyOracleCore
