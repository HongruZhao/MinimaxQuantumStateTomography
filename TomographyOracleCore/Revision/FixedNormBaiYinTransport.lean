import TomographyOracleCore.Revision.CovarianceIsometryTransport
import TomographyOracleCore.Revision.PublishedBaiYin
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace TomographyOracleCore.Revision.FixedNormBaiYinTransport

open MeasureTheory ProbabilityTheory PeriodicForwardCovariance CovarianceIsometryTransport
open scoped RealInnerProductSpace
noncomputable section

/-- Coordinate transport of the currently named sharp covariance input.
This theorem still depends on `abdallaZhivotovskiy_fixedNorm_p6`; it does not
claim to prove that concentration theorem. The constants are uniform over
all finite-dimensional real Hilbert spaces. -/
theorem fixedNorm_baiYin_finiteDimensional (kappa : ℝ) (hkappa : 1 ≤ kappa) :
    ∃ c C : ℝ, 1 ≤ c ∧ 0 < C ∧
      ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
        [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
        (T : ℕ) (hT : 0 < T) (mu : Measure E) [IsProbabilityMeasure mu] (q : ℝ),
        0 < q → (∫ x, x ∂mu) = 0 → (∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) →
        HasL6L2Marginals mu kappa →
        c * (q / ‖populationCovariance mu‖) ≤ (T : ℝ) →
        q ≤ (T : ℝ) * ‖populationCovariance mu‖ →
        (∫ X : Fin T → E, ‖sampleCovariance X - populationCovariance mu‖
          ∂Measure.pi (fun _ : Fin T => mu)) ≤
          C * ‖populationCovariance mu‖ * Real.sqrt ((q / ‖populationCovariance mu‖) / (T : ℝ)) := by
  obtain ⟨c, C, hc, hC, hmain⟩ := PublishedInputs.abdallaZhivotovskiy_fixedNorm_p6 kappa hkappa
  refine ⟨c, C, hc, hC, ?_⟩
  intro E _ _ _ _ _ _ T hT mu _ q hq hmean hfixed hL6 hsize htrunc
  let e := (stdOrthonormalBasis ℝ E).repr
  let nu := mu.map e
  letI : IsProbabilityMeasure nu := Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  have hmu := fixedNorm_memLp hfixed 2
  have hnorm : ‖populationCovariance nu‖ = ‖populationCovariance mu‖ := by
    rw [show nu = mu.map e from rfl, populationCovariance_map e hmu, norm_conjugate]
  have hnumean : (∫ x, x ∂nu) = 0 := by
    rw [show nu = mu.map e from rfl, integral_id_map, hmean, e.map_zero]
  have hdim : 0 < Module.finrank ℝ E := Module.finrank_pos
  have hbound := hmain (Module.finrank ℝ E) T hdim hT nu q hq hnumean
    (fixedNorm_map e hfixed) (hasL6L2_map e hL6)
    (by simpa only [hnorm] using hsize) (by simpa only [hnorm] using htrunc)
  rw [hnorm] at hbound
  change (∫ X : Fin T → EuclideanSpace ℝ (Fin (Module.finrank ℝ E)),
    ‖sampleCovariance X - populationCovariance (mu.map e)‖
      ∂Measure.pi (fun _ : Fin T => mu.map e)) ≤ _ at hbound
  rwa [expected_covariance_error_map e mu hmu T] at hbound

end
end TomographyOracleCore.Revision.FixedNormBaiYinTransport
