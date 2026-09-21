import TomographyOracleCore.Revision.MWPLSObjective

/-! Deterministic MW-PLS trace-loss bounds, including first-order
gap-controlled feasible approximations. -/
namespace TomographyOracleCore.MWPLS
open MatrixReduction Revision.PhysicalMinimax
open scoped BigOperators Matrix.Norms.L2Operator
noncomputable section
set_option maxHeartbeats 1200000

theorem cone_absorption_with_gap (x tail v z w : ℝ)
    (hx : 0 ≤ x) (hv : 0 ≤ v) (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hcone : x ≤ 2*tail+2*v) (henergy : v^2 ≤ z*x+w) :
    x ≤ 4*tail+4*z+4*Real.sqrt w := by
  have hr : 0 ≤ x/2+2*z := by positivity
  have hc := mul_nonneg hr (Real.sqrt_nonneg w)
  have hs := Real.sq_sqrt hw
  have hsq : (2*v)^2 ≤ (x/2+2*z+2*Real.sqrt w)^2 := by
    nlinarith [sq_nonneg (x/2-2*z)]
  have hroot := (sq_le_sq₀ (by positivity : 0 ≤ 2*v)
    (by positivity : 0 ≤ x/2+2*z+2*Real.sqrt w)).mp hsq
  linarith

theorem density_trace_bound_with_gap {D : ℕ}
    (sigma rho : DensityOperator (Fin D)) (s : ℕ) (a e epsilon : ℝ)
    (ha : 0 < a) (he : 0 ≤ e) (hepsilon : 0 ≤ epsilon)
    (henergy : a * hermitianFrobeniusNorm (sigma.matrix-rho.matrix)
      (sigma.sub_isHermitian rho)^2 ≤
      hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho)*e+epsilon) :
    hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho) ≤
      4*orderedSpectralTail rho s + 4*((s : ℝ)*e/a) +
        4*Real.sqrt ((s : ℝ)*epsilon/a) := by
  let x := hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho)
  let f := hermitianFrobeniusNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho)
  let v := Real.sqrt (s : ℝ)*f
  let z := (s : ℝ)*e/a
  let w := (s : ℝ)*epsilon/a
  have hx : 0 ≤ x := hermitianTraceNorm_nonneg _ _
  have hf : 0 ≤ f := hermitianFrobeniusNorm_nonneg _ _
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hc : x ≤ 2*orderedSpectralTail rho s+2*v := by
    simpa only [v, mul_assoc] using density_orderedSpectralTail_cone_negative sigma rho s
  have heq : v^2 = ((s : ℝ)/a)*(a*f^2) := by
    dsimp [v]
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
    field_simp
  have hv2 : v^2 ≤ z*x+w := by
    rw [heq]
    calc
      _ ≤ ((s : ℝ)/a)*(x*e+epsilon) := mul_le_mul_of_nonneg_left henergy (by positivity)
      _ = _ := by dsimp [z,w]; ring
  exact cone_absorption_with_gap x (orderedSpectralTail rho s) v z w hx hv hz hw hc hv2

/-- Equivalent to bounding every feasible linearization by epsilon. With
an exact smallest eigenvalue, this is the paper's Frank-Wolfe gap test. -/
def HasFirstOrderCertificate {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) (sigma : DensityOperator (Fin D))
    (epsilon : ℝ) : Prop :=
  ∀ rho : DensityOperator (Fin D),
    pairing (finiteUnitaryFullCalibratedLinearChannel U sigma.matrix-Q)
      (sigma.matrix-rho.matrix) ≤ epsilon

theorem minimizer_certificate {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (hD : 0 < D) (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (Q : Matrix (Fin D) (Fin D) ℂ) :
    HasFirstOrderCertificate U Q (minimizer hD U Q) 0 :=
  minimizer_first_order hD U Q

theorem periodic_basic_inequality {n K : ℕ} (h : ChoKimBlockCondition n K)
    (Q : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (sigma rho : DensityOperator (Fin (2^n))) (epsilon : ℝ)
    (hfirst : pairing
      (finiteUnitaryFullCalibratedLinearChannel
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) sigma.matrix-Q)
      (sigma.matrix-rho.matrix) ≤ epsilon) :
    sharpPeriodicCurvature * hermitianFrobeniusNorm (sigma.matrix-rho.matrix)
      (sigma.sub_isHermitian rho)^2 ≤
      hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho)*
        matrixOperatorNorm (Q-finiteUnitaryFullCalibratedLinearChannel
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho.matrix)+epsilon := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let L := finiteUnitaryFullCalibratedLinearChannel U
  have hcurv := h.finiteUnitaryCalibratedDensityChannel_curvature_sharp sigma rho
  rw [← finiteUnitaryFullCalibratedLinearChannel_density_sub U sigma rho, map_sub] at hcurv
  have hdual := hermitianForwardEnergy_le_traceNorm_mul_operatorNorm sigma rho (Q-L rho.matrix)
  have hsplit : pairing (L sigma.matrix-L rho.matrix) (sigma.matrix-rho.matrix) =
      pairing (L sigma.matrix-Q) (sigma.matrix-rho.matrix)+
      pairing (Q-L rho.matrix) (sigma.matrix-rho.matrix) := by
    simp only [pairing_sub_left]
    ring
  change sharpPeriodicCurvature * hermitianFrobeniusNorm (sigma.matrix-rho.matrix)
    (sigma.sub_isHermitian rho)^2 ≤ pairing (L sigma.matrix-L rho.matrix)
    (sigma.matrix-rho.matrix) at hcurv
  change pairing (Q-L rho.matrix) (sigma.matrix-rho.matrix) ≤ _ at hdual
  rw [hsplit] at hcurv
  linarith

/-- Appendix I's deterministic oracle for a feasible first-order certificate. -/
theorem periodic_trace_oracle_with_gap {n K : ℕ} (h : ChoKimBlockCondition n K)
    (Q : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (sigma rho : DensityOperator (Fin (2^n))) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon)
    (hcert : HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q sigma epsilon) (s : ℕ) :
    hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho) ≤
      4*orderedSpectralTail rho s +
      4*((s : ℝ)*matrixOperatorNorm (Q-finiteUnitaryFullCalibratedLinearChannel
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho.matrix)/sharpPeriodicCurvature)+
      4*Real.sqrt ((s : ℝ)*epsilon/sharpPeriodicCurvature) :=
  density_trace_bound_with_gap sigma rho s sharpPeriodicCurvature _ epsilon
    sharpPeriodicCurvature_pos (matrixOperatorNorm_nonneg _) hepsilon
    (periodic_basic_inequality h Q sigma rho epsilon (hcert rho))

/-- Exact MW-PLS satisfies the sharp trace oracle without a solver premise. -/
theorem periodic_minimizer_trace_oracle {n K : ℕ} (h : ChoKimBlockCondition n K)
    (Q : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (rho : DensityOperator (Fin (2^n))) (s : ℕ) :
    let sigma := minimizer (by positivity : 0 < 2^n)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q
    hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho) ≤
      4*orderedSpectralTail rho s +
      4*((s : ℝ)*matrixOperatorNorm (Q-finiteUnitaryFullCalibratedLinearChannel
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho.matrix)/sharpPeriodicCurvature) := by
  dsimp only
  simpa only [mul_zero, zero_div, Real.sqrt_zero, add_zero] using
    periodic_trace_oracle_with_gap h Q _ rho 0 (by norm_num)
      (minimizer_certificate (by positivity) _ Q) s

theorem sqrt_scaled_gap_le (s gamma a : ℝ) (hs : 1 ≤ s) (hg : 0 ≤ gamma)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    Real.sqrt (s*gamma^2/a) ≤ s*gamma/a := by
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · apply (div_le_iff₀ ha).mpr
    have hid : (s*gamma/a)^2*a = s^2*gamma^2/a := by
      field_simp
    rw [hid]
    apply (le_div_iff₀ ha).mpr
    have hh := mul_nonneg (show 0 ≤ s*gamma^2 by positivity)
      (show 0 ≤ s-a by linarith)
    nlinarith

/-- A convenient common coefficient for the expectation/rate interface. -/
theorem periodic_certificate_oracle {n K : ℕ} (h : ChoKimBlockCondition n K)
    (Q : Matrix (Fin (2^n)) (Fin (2^n)) ℂ)
    (sigma rho : DensityOperator (Fin (2^n))) (gamma : ℝ) (hg : 0 ≤ gamma)
    (hcert : HasFirstOrderCertificate
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q sigma (gamma^2)) :
    OracleBound (hermitianTraceNorm (sigma.matrix-rho.matrix) (sigma.sub_isHermitian rho))
      (orderedSpectralTail rho)
      ((8/sharpPeriodicCurvature)*matrixOperatorNorm
        (Q-finiteUnitaryFullCalibratedLinearChannel
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho.matrix)+
        (4/sharpPeriodicCurvature)*gamma) (2^n) := by
  intro s hs1 hsD
  have ho := periodic_trace_oracle_with_gap h Q sigma rho (gamma^2) (sq_nonneg _) hcert s
  have hsreal : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
  have hroot := sqrt_scaled_gap_le (s : ℝ) gamma sharpPeriodicCurvature hsreal hg
    sharpPeriodicCurvature_pos (by norm_num [sharpPeriodicCurvature])
  have hx := matrixOperatorNorm_nonneg (Q-finiteUnitaryFullCalibratedLinearChannel
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho.matrix)
  have hp : 0 ≤ ((s : ℝ)/sharpPeriodicCurvature) * matrixOperatorNorm
      (Q-finiteUnitaryFullCalibratedLinearChannel
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho.matrix) := by
    exact mul_nonneg (div_nonneg (Nat.cast_nonneg _) sharpPeriodicCurvature_pos.le) hx
  simp only [div_eq_mul_inv] at ho hroot hp ⊢
  nlinarith

end
end TomographyOracleCore.MWPLS
