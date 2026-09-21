import TomographyOracleCore.Revision.FixedNormBaiYinProof

/-!
The fixed-norm covariance theorem, proved from standard Lean foundations.

SOURCE: P. Abdalla and N. Zhivotovskiy, arXiv:2205.08494v3,
Theorem 2 (p = 6), together with its stated norm-equivalence hypotheses.

This is the fixed-norm finite-dimensional specialization of that theorem.
The explicit second sample-size condition makes its radial truncation
inactive. Fixed squared norm q implies trace(covariance) = q. That trace
identity is a specialization lemma. The constants depend only on kappa.

The proof in `FixedNormBaiYinProof` combines actual Gaussian smoothing and
change of measure, elementary sparse-coordinate selection, finite nets,
conditional sixth-moment bounds, partition averaging, and expectation bounds.
It does not assume the published theorem or any intermediate concentration
inequality. The original declaration's statement is preserved exactly.

The general auxiliary smoothing inequality printed in the source is repaired
with larger constants; see `ClippingLogSmoothing` and
`PrintedSmoothingCounterexample`. The covariance conclusion remains unchanged.
-/
open MeasureTheory ProbabilityTheory InnerProductSpace
open scoped RealInnerProductSpace BigOperators

namespace TomographyOracleCore.Revision.PublishedInputs

open TomographyOracleCore.PeriodicForwardCovariance

noncomputable section

theorem abdallaZhivotovskiy_fixedNorm_p6
    (kappa : ℝ) (hkappa : 1 ≤ kappa) :
    ∃ c C : ℝ, 1 ≤ c ∧ 0 < C ∧
      ∀ (D T : ℕ) (hD : 0 < D) (hT : 0 < T)
        (mu : Measure (EuclideanSpace ℝ (Fin D))) [IsProbabilityMeasure mu]
        (q : ℝ),
        0 < q →
        (∫ x, x ∂mu) = 0 →
        (∀ᵐ x ∂mu, ‖x‖ ^ 2 = q) →
        HasL6L2Marginals mu kappa →
        c * (q / ‖populationCovariance mu‖) ≤ (T : ℝ) →
        q ≤ (T : ℝ) * ‖populationCovariance mu‖ →
        (∫ omega : Fin T → EuclideanSpace ℝ (Fin D),
          ‖sampleCovariance omega - populationCovariance mu‖
          ∂(Measure.pi (fun _ : Fin T => mu))) ≤
        C * ‖populationCovariance mu‖ *
          Real.sqrt ((q / ‖populationCovariance mu‖) / (T : ℝ)) := by
  refine ⟨1, FixedNormBaiYinProof.covarianceConstant kappa, le_rfl,
    FixedNormBaiYinProof.covarianceConstant_pos hkappa, ?_⟩
  intro D T hD hT mu inst q hq _hmean hfixed hL6 _hsamples hregime
  letI : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  exact FixedNormBaiYinProof.expected_covariance_error_le hT hfixed hq hkappa hL6 hregime

end
end TomographyOracleCore.Revision.PublishedInputs
