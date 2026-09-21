import TomographyOracleCore.Revision.PeakyUniformEnvelope
import TomographyOracleCore.Revision.IntegralCauchySchwarz

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.PeakyEnvelopeMoments

open MeasureTheory PeriodicForwardCovariance PeakyUniformEnvelope MaximumPairMoments
open SparseUniformEnergy SparseBadPartitionFraction IntegralCauchySchwarz
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E]
  {mu : Measure E} [IsProbabilityMeasure mu] {q : ℝ}

theorem integral_baseEnergy_le {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hkappa : 0 ≤ kappa) (hL6 : HasL6L2Marginals mu kappa) :
    (∫ X : Fin N → E, baseEnergy q X ∂Measure.pi (fun _ : Fin N => mu)) ≤
      q + 2 * kappa * Real.sqrt (‖populationCovariance mu‖ * q * (N : ℝ)) := by
  unfold baseEnergy
  rw [integral_add (integrable_const q)
    ((integrable_maximumPair hfixed hq).const_mul (SparseRecursionWeights.amplification N))]
  simpa using add_le_add (le_refl q) (integral_amplified_maximumPair_le hN hfixed hq hkappa hL6)

theorem integral_sqrt_baseEnergy_sq_le {N : ℕ}
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (∫ X : Fin N → E, Real.sqrt (lambda * baseEnergy q X) ∂Measure.pi (fun _ : Fin N => mu)) ^ 2 ≤
      lambda * ∫ X : Fin N → E, baseEnergy q X ∂Measure.pi (fun _ : Fin N => mu) := by
  have heq (X : Fin N → E) : Real.sqrt (lambda * baseEnergy q X) ^ 2 = lambda * baseEnergy q X :=
    Real.sq_sqrt (mul_nonneg hlambda (baseEnergy_nonneg hq X))
  have hfi : Integrable (fun X : Fin N → E => Real.sqrt (lambda * baseEnergy q X) ^ 2)
      (Measure.pi (fun _ : Fin N => mu)) := by
    simpa only [heq] using (integrable_baseEnergy hfixed hq).const_mul lambda
  have h := integral_mul_sq_le (Measure.pi (fun _ : Fin N => mu))
    (fun X : Fin N → E => Real.sqrt (lambda * baseEnergy q X)) (fun _ => (1 : ℝ)) hfi
    (by simpa using (integrable_const (1 : ℝ)))
    (by simpa using integrable_sqrt_lambda_baseEnergy hfixed hq hlambda (N := N))
  simpa [heq, integral_const_mul] using h

theorem integral_goodPeakyEnvelope_eq {N : ℕ}
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    (kappa s : ℝ) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (∫ X : Fin N → E, goodPeakyEnvelope q kappa s lambda X ∂Measure.pi (fun _ : Fin N => mu)) =
      uniformEnergyConstant ^ 2 *
      ((∫ X : Fin N → E, baseEnergy q X ∂Measure.pi (fun _ : Fin N => mu)) +
        2 * (kappa ^ 2 * s) * Real.sqrt (N : ℝ) *
          (∫ X : Fin N → E, Real.sqrt (lambda * baseEnergy q X) ∂Measure.pi (fun _ : Fin N => mu)) +
        lambda * (kappa ^ 2 * s) ^ 2 * (N : ℝ)) / (N : ℝ) := by
  have hb := integrable_baseEnergy hfixed hq (N := N)
  have hr := (integrable_sqrt_lambda_baseEnergy hfixed hq hlambda (N := N)).const_mul
    (2 * (kappa ^ 2 * s) * Real.sqrt (N : ℝ))
  unfold goodPeakyEnvelope
  have ha := integral_add (hb.add hr) (integrable_const (lambda * (kappa ^ 2 * s) ^ 2 * (N : ℝ)))
  simp only [Pi.add_apply] at ha
  rw [integral_div, integral_const_mul, ha, integral_add hb hr, integral_const_mul]
  simp

/-- Expected exceptional-event cost, with the actual event probability proved
by sparse nets and finite partition averaging. -/
theorem integral_peakyEnvelope_le_good_add_exception {N : ℕ} (hN : 0 < N)
    (hfixed : ∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) (hq : 0 ≤ q)
    {kappa : ℝ} (hkappa : 0 < kappa) (hL6 : HasL6L2Marginals mu kappa)
    (hs : 0 < ‖populationCovariance mu‖) {lambda : ℝ} (hlambda : 0 ≤ lambda) :
    (∫ X : Fin N → E, peakyEnvelope q kappa ‖populationCovariance mu‖ lambda X
      ∂Measure.pi (fun _ : Fin N => mu)) ≤
      (∫ X : Fin N → E, goodPeakyEnvelope q kappa ‖populationCovariance mu‖ lambda X
        ∂Measure.pi (fun _ : Fin N => mu)) + 16 * q / (N : ℝ) ^ 3 := by
  unfold peakyEnvelope
  rw [integral_add (integrable_goodPeakyEnvelope hfixed hq hlambda)
    ((integrable_const q).indicator (measurableSet_globalFailure _ _ _))]
  apply add_le_add le_rfl
  rw [integral_indicator (measurableSet_globalFailure _ _ _)]
  have h := mul_le_mul_of_nonneg_right (measureReal_globalFailure_le hN hfixed hkappa hL6 hs) hq
  simpa only [setIntegral_const, smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h

end
end TomographyOracleCore.Revision.PeakyEnvelopeMoments
