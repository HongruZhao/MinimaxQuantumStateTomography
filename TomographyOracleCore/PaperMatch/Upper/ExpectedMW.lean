import TomographyOracleCore.Revision.MWPLSEndpoints

/-! The sharpened expected MW oracle with the coefficient printed in Section IV.
Unlike the historical solver-only endpoint, the estimate below may depend on
its entire observed record; its first-order certificate need only hold a.s. -/
namespace TomographyOracleCore.PaperMatch.Upper
open MeasureTheory MatrixReduction MWPLS Revision.PhysicalMinimax Revision.ConstantCovariance
open scoped Matrix.Norms.L2Operator
noncomputable section

/-- The square-root tolerance term is rank-adaptive for every s >= 1. -/
theorem sqrt_tolerance_le (s : ℕ) (hs : 1≤s) (a q : ℝ) (ha : 0<a) (hq : 0≤q) :
    Real.sqrt ((s : ℝ)*q/a) ≤ (s : ℝ)*Real.sqrt q/Real.sqrt a := by
  have hsR : (1 : ℝ)≤s := by exact_mod_cast hs
  have hss : Real.sqrt (s : ℝ) ≤ (s : ℝ) := by
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  rw [Real.sqrt_div (by positivity), Real.sqrt_mul (Nat.cast_nonneg s)]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hss (Real.sqrt_nonneg q)) (Real.sqrt_nonneg a)

def mwExpectedOracleConstant : ℝ :=
  4*sharpForwardCovarianceConstant/sharpPeriodicCurvature+4/Real.sqrt sharpPeriodicCurvature

/-- Equation (24) for an arbitrary feasible approximate MW fit on the record space. -/
theorem mw_expected_oracle
    {n K T : ℕ} (h : ChoKimBlockCondition n K) (hn : 0<n) (hT : 0<T)
    (hsize : 2*((2^n : ℕ) : ℝ)≤(T : ℝ))
    (estimate : (Fin T → Matrix (Fin (2^n)) (Fin (2^n)) ℂ) → DensityOperator (Fin (2^n)))
    (rho : DensityOperator (Fin (2^n)))
    (hcert : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      HasFirstOrderCertificate (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
        (empiricalForwardMatrix sample) (estimate sample) (((2^n : ℕ) : ℝ)/(T : ℝ)))
    (s : ℕ) (hs : 1≤s) :
    (∫ sample, hermitianTraceNorm ((estimate sample).matrix-rho.matrix)
      ((estimate sample).sub_isHermitian rho) ∂periodicSampleLaw h T rho) ≤
      4*orderedSpectralTail rho s+mwExpectedOracleConstant*(s : ℝ)*
        Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ)) := by
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let q := Real.sqrt (((2^n : ℕ) : ℝ)/(T : ℝ))
  let a := sharpPeriodicCurvature
  have ha : 0<a := sharpPeriodicCurvature_pos
  have hierr := integrable_productBorn_real (by positivity) U T rho
    (fun sample => hermitianTraceNorm ((estimate sample).matrix-rho.matrix)
      ((estimate sample).sub_isHermitian rho))
  have hieta := integrable_productBorn_real (by positivity) U T rho (periodicForwardError h rho)
  have hirhs := integrable_productBorn_real (by positivity) U T rho
    (fun sample => (4*orderedSpectralTail rho s+4*(s : ℝ)*q/Real.sqrt a)+
      (4*(s : ℝ)/a)*periodicForwardError h rho sample)
  change Integrable _ (periodicSampleLaw h T rho) at hierr hieta hirhs
  have hpoint : ∀ᵐ sample ∂periodicSampleLaw h T rho,
      hermitianTraceNorm ((estimate sample).matrix-rho.matrix)
        ((estimate sample).sub_isHermitian rho) ≤
      (4*orderedSpectralTail rho s+4*(s : ℝ)*q/Real.sqrt a)+
        (4*(s : ℝ)/a)*periodicForwardError h rho sample := by
    filter_upwards [hcert] with sample hc
    have ho := periodic_trace_oracle_with_gap h (empiricalForwardMatrix sample)
      (estimate sample) rho (((2^n : ℕ) : ℝ)/(T : ℝ)) (by positivity) hc s
    have ht := sqrt_tolerance_le s hs a (((2^n : ℕ) : ℝ)/(T : ℝ)) ha (by positivity)
    change Real.sqrt ((s : ℝ)*(((2^n : ℕ) : ℝ)/(T : ℝ))/a) ≤
      (s : ℝ)*q/Real.sqrt a at ht
    change _ ≤ 4*orderedSpectralTail rho s+
      4*((s : ℝ)*periodicForwardError h rho sample/a)+
      4*Real.sqrt ((s : ℝ)*(((2^n : ℕ) : ℝ)/(T : ℝ))/a) at ho
    calc
      _ ≤ _ := ho
      _ ≤ 4*orderedSpectralTail rho s+
          4*((s : ℝ)*periodicForwardError h rho sample/a)+
          4*((s : ℝ)*q/Real.sqrt a) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ)≤4))
      _ = _ := by ring
  have hle := integral_mono_ae hierr hirhs hpoint
  rw [integral_add (integrable_const _) (hieta.const_mul _)] at hle
  simp only [integral_const_mul, integral_const, Measure.real, measure_univ,
    ENNReal.toReal_one, one_smul] at hle
  have hm := periodic_expected_forward_covariance_sharp h hn hT hsize rho
  have hb := mul_le_mul_of_nonneg_left hm
    (show 0≤4*(s : ℝ)/a by positivity)
  change _ ≤ 4*orderedSpectralTail rho s+
    (4*sharpForwardCovarianceConstant/a+4/Real.sqrt a)*(s : ℝ)*q
  change (4*(s : ℝ)/a)*(∫ sample, periodicForwardError h rho sample
    ∂periodicSampleLaw h T rho) ≤ (4*(s : ℝ)/a)*(sharpForwardCovarianceConstant*q) at hb
  calc
    _ ≤ _ := hle
    _ ≤ (4*orderedSpectralTail rho s+4*(s : ℝ)*q/Real.sqrt a)+
        (4*(s : ℝ)/a)*(sharpForwardCovarianceConstant*q) := add_le_add le_rfl hb
    _ = _ := by ring
end
end TomographyOracleCore.PaperMatch.Upper
