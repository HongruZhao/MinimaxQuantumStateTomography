import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

/-! Deterministic scalar kernel for the tomography oracle argument. -/

/-- The Young inequality used to absorb the square-root error term. -/
theorem four_mul_sqrt_mul_sqrt_le (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) :
    4 * Real.sqrt z * Real.sqrt x ≤ x / 2 + 8 * z := by
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt hx
  have hsz : (Real.sqrt z) ^ 2 = z := Real.sq_sqrt hz
  have hsq : 0 ≤ (Real.sqrt x - 4 * Real.sqrt z) ^ 2 := sq_nonneg _
  nlinarith

/-- Scalar quadratic absorption behind curvature plus positivity. -/
theorem scalar_quadratic_absorption (x tail z : ℝ)
    (hx : 0 ≤ x) (hz : 0 ≤ z)
    (hred : x ≤ 2 * tail + 4 * Real.sqrt z * Real.sqrt x) :
    x ≤ 4 * tail + 16 * z := by
  have hy := four_mul_sqrt_mul_sqrt_le x z hx hz
  linarith

/-- Abstract oracle property: one inequality holds simultaneously at every
admissible truncation level. -/
def OracleBound (err : ℝ) (tail : ℕ → ℝ) (noise : ℝ) (D : ℕ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → s ≤ D → err ≤ 4 * tail s + noise * s

/-- An exact-rank state is the zero-tail specialization of the oracle bound. -/
theorem rank_specialization {err noise : ℝ} {tail : ℕ → ℝ} {D r : ℕ}
    (horacle : OracleBound err tail noise D)
    (hr1 : 1 ≤ r) (hrD : r ≤ D) (hrank : tail r = 0) :
    err ≤ noise * r := by
  simpa [hrank] using horacle r hr1 hrD

/-- The universal oracle bound specializes to any class envelope. -/
theorem class_envelope_specialization {err noise envelope : ℝ}
    {tail : ℕ → ℝ} {D s : ℕ}
    (horacle : OracleBound err tail noise D)
    (hs1 : 1 ≤ s) (hsD : s ≤ D)
    (htail : tail s ≤ envelope) :
    err ≤ 4 * envelope + noise * s := by
  have h := horacle s hs1 hsD
  nlinarith

/-- If a continuous truncation scale balances approximation and estimation,
the sum is twice the common rate.  This is the final algebraic optimization
step, separated from integer rounding. -/
theorem balanced_two_term_rate {err approximation estimation rate : ℝ}
    (hupper : err ≤ 4 * approximation + estimation)
    (happrox : approximation ≤ rate)
    (hest : estimation ≤ 4 * rate) :
    err ≤ 8 * rate := by
  linarith

/-- Continuous scale that balances a polynomial spectral tail and a linear
estimation term.  Here `beta = 1 / alpha`. -/
noncomputable def balancedScale (L eta beta : ℝ) : ℝ :=
  L ^ beta * eta ^ (-beta)

/-- Polynomial-decay rate in the reciprocal exponent `beta = 1 / alpha`. -/
noncomputable def polynomialRate (L eta beta : ℝ) : ℝ :=
  L ^ beta * eta ^ (1 - beta)

/-- At the balanced scale the linear estimation term is exactly the target
polynomial-decay rate. -/
theorem estimation_at_balanced_scale (L eta beta : ℝ) (heta : 0 < eta) :
    eta * balancedScale L eta beta = polynomialRate L eta beta := by
  have hp : eta ^ (1 - beta) = eta ^ (1 : ℝ) * eta ^ (-beta) := by
    rw [show 1 - beta = (1 : ℝ) + (-beta) by ring]
    exact Real.rpow_add heta 1 (-beta)
  rw [balancedScale, polynomialRate, hp, Real.rpow_one]
  ring

/-- At the same scale, `L s^(1-alpha)` equals the target rate.  Writing
`beta = 1/alpha` keeps the exponent algebra transparent. -/
theorem approximation_at_balanced_scale (L eta beta : ℝ)
    (hL : 0 < L) (heta : 0 < eta) (hbeta : beta ≠ 0) :
    L * (balancedScale L eta beta) ^ (1 - beta⁻¹) =
      polynomialRate L eta beta := by
  have hLb : 0 ≤ L ^ beta := Real.rpow_nonneg (le_of_lt hL) beta
  have heb : 0 ≤ eta ^ (-beta) := Real.rpow_nonneg (le_of_lt heta) (-beta)
  have hbe : beta * (1 - beta⁻¹) = beta - 1 := by
    field_simp
  have hnbe : (-beta) * (1 - beta⁻¹) = 1 - beta := by
    field_simp
    ring
  have hcombine : L * L ^ (beta - 1) = L ^ beta := by
    calc
      L * L ^ (beta - 1) = L ^ (1 : ℝ) * L ^ (beta - 1) := by
        rw [Real.rpow_one]
      _ = L ^ ((1 : ℝ) + (beta - 1)) := by
        rw [Real.rpow_add hL]
      _ = L ^ beta := by ring_nf
  rw [balancedScale, Real.mul_rpow hLb heb]
  rw [← Real.rpow_mul (le_of_lt hL) beta (1 - beta⁻¹)]
  rw [← Real.rpow_mul (le_of_lt heta) (-beta) (1 - beta⁻¹)]
  rw [hbe, hnbe, polynomialRate]
  rw [← mul_assoc, hcombine]

/-- The continuous two-term polynomial-tail objective evaluated at the
balanced scale has the claimed rate.  Integer rounding and endpoint
truncation are deliberately outside this scalar identity. -/
theorem polynomial_objective_at_balanced_scale
    (err L eta beta : ℝ)
    (hL : 0 < L) (heta : 0 < eta) (hbeta : beta ≠ 0)
    (hupper : err ≤
      4 * (L * (balancedScale L eta beta) ^ (1 - beta⁻¹)) +
      4 * (eta * balancedScale L eta beta)) :
    err ≤ 8 * polynomialRate L eta beta := by
  rw [approximation_at_balanced_scale L eta beta hL heta hbeta,
    estimation_at_balanced_scale L eta beta heta] at hupper
  linarith

/-- Rewriting `beta = 1/alpha` recovers the familiar exponent
`(alpha - 1) / alpha`. -/
theorem polynomialRate_reciprocal (L eta alpha : ℝ) (halpha : alpha ≠ 0) :
    polynomialRate L eta alpha⁻¹ =
      L ^ alpha⁻¹ * eta ^ ((alpha - 1) / alpha) := by
  have hexp : 1 - alpha⁻¹ = (alpha - 1) / alpha := by
    field_simp
  simp only [polynomialRate, hexp]

/-- Minimax sandwich: a class-specific lower bound and a universal upper
bound identify the rate up to constants. -/
theorem minimax_sandwich {risk rate c C : ℝ}
    (hlower : c * rate ≤ risk) (hupper : risk ≤ C * rate) :
    c * rate ≤ risk ∧ risk ≤ C * rate :=
  ⟨hlower, hupper⟩

/-- If unrestricted risk is no larger than fixed-design risk, a universal
lower bound plus a fixed-design upper bound sandwiches both risks. -/
theorem two_experiment_minimax_sandwich
    {unrestricted fixedDesign rate c C : ℝ}
    (hlower : c * rate ≤ unrestricted)
    (hdesign : unrestricted ≤ fixedDesign)
    (hupper : fixedDesign ≤ C * rate) :
    (c * rate ≤ unrestricted ∧ unrestricted ≤ C * rate) ∧
      (c * rate ≤ fixedDesign ∧ fixedDesign ≤ C * rate) := by
  constructor
  · exact ⟨hlower, hdesign.trans hupper⟩
  · exact ⟨hlower.trans hdesign, hupper⟩

end TomographyOracleCore
