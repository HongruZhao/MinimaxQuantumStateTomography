import TomographyOracleCore.Revision.NoncomputationalInputs
import TomographyOracleCore.Revision.PhysicalMinimaxAlgorithmRates
import TomographyOracleCore.ChoKimBlockDimensionOptimization

/-!
# Closed Candidate 2 statistical chain using the proved covariance theorem

All fitting-existence, physical-experiment, expected-risk, truncation-rank,
and minimax-ordering steps below are proved. The physical covariance theorem
`periodicBorn_expected_forward_covariance` is proved from standard foundations.

The exact fit is selected noncomputably by compactness. It establishes a
statistical Candidate 2 estimator, not a polynomial implementation. The
separate algorithm interface below permits a verified implementation to
replace that selector without changing the statistical proof.
-/

namespace TomographyOracleCore.Revision.PhysicalMinimax

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open scoped BigOperators Matrix.Norms.L2Operator ENNReal

noncomputable section

/-- All-sample expected trace-risk guarantee of the actual exact forward
fit, uniformly in all periodic experiments and all spectral-tail classes.
The physical covariance theorem is discharged internally. -/
theorem candidate2_exactFit_physicalUpper :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T →
        ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
          classWorstCaseRisk (2 ^ n) T alpha L
            (constantMatrixPOVMPhysicalDesign
              (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
            (physicalEstimator (by positivity)
              (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T) ≤
          ENNReal.ofReal (algorithmUpperConstant c A *
            spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  obtain ⟨c, A, hc, hA, hcov⟩ :=
    NoncomputationalInputs.periodicBorn_expected_forward_covariance
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT alpha L halpha hL
  let U := choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd
  let solve := forwardMinimizer (by positivity : 0 < 2 ^ n) U
  unfold classWorstCaseRisk
  apply iSup_le
  intro rho
  have hfit : ∀ Q truth, forwardObjective U Q (solve Q) ≤ forwardObjective U Q truth + 0 := by
    intro Q truth
    simpa using forwardMinimizer_le (by positivity) U Q truth
  exact periodicAlgorithm_physicalRisk_rate h hT solve 0 (by norm_num)
    (Real.sqrt_nonneg _) hfit c A hc hA
    (fun hsize => hcov h hn hT hsize) rho.1 alpha L halpha hL rho.2

/-- The actual exact forward fit supplies a simultaneous physical upper
bound, and the inherited unrestricted lower bound completes minimax. -/
theorem candidate2_exactFit_physicalMinimax :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T →
        ExplicitPhysicalMinimaxTarget (2 ^ n) T
          (constantMatrixPOVMPhysicalDesign
            (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (fun _ => algorithmUpperConstant c A) := by
  obtain ⟨c, A, hc, hA, hupper⟩ := candidate2_exactFit_physicalUpper
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT
  apply physicalMinimaxSandwich_of_lower_and_simultaneousUpper
  · intro alpha L halpha hL
    have hlarge := h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn
    exact explicitSpectralDecayRateENNReal_le_unrestrictedRisk
      (2 ^ n) T L alpha (by omega) hT hL halpha
  · refine ⟨physicalEstimator (by positivity)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T, ?_⟩
    exact hupper h hn hT

/-- Once an actual matrix algorithm's fitting theorem is verified, the same
explicit covariance input proves its physical simultaneous minimax upper
rate. This interface exposes the computational obligation; it is not an
unconditional solver theorem. -/
theorem candidate2_algorithm_physicalUpper :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T →
        ∀ (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
          (gamma : ℝ),
          0 ≤ gamma → gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) →
          (∀ Q rho,
            forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
              forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma) →
          SimultaneousPhysicalUpper (2 ^ n) T
            (constantMatrixPOVMPhysicalDesign
              (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
            (fun _ => algorithmUpperConstant c A) := by
  obtain ⟨c, A, hc, hA, hcov⟩ :=
    NoncomputationalInputs.periodicBorn_expected_forward_covariance
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT solve gamma hgamma hgammaScale hfit
  exact periodicAlgorithm_simultaneousPhysicalUpper h hT solve gamma hgamma hgammaScale
    hfit c A hc hA (fun hsize => hcov h hn hT hsize)

/-- Stronger selected-estimator form: the risk bound is for the supplied
algorithm itself, rather than only an existential upper target. -/
theorem candidate2_algorithm_selectedPhysicalUpper :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T →
        ∀ (solve : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ → DensityOperator (Fin (2 ^ n)))
          (gamma : ℝ),
          0 ≤ gamma → gamma ≤ Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ)) →
          (∀ Q rho,
            forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q (solve Q) ≤
              forwardObjective (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) Q rho + gamma) →
          ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
            classWorstCaseRisk (2 ^ n) T alpha L
              (constantMatrixPOVMPhysicalDesign
                (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
              (algorithmPhysicalEstimator (by positivity)
                (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T solve) ≤
            ENNReal.ofReal (algorithmUpperConstant c A *
              spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  obtain ⟨c, A, hc, hA, hcov⟩ :=
    NoncomputationalInputs.periodicBorn_expected_forward_covariance
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT solve gamma hgamma hgammaScale hfit alpha L halpha hL
  unfold classWorstCaseRisk
  apply iSup_le
  intro rho
  exact periodicAlgorithm_physicalRisk_rate h hT solve gamma hgamma hgammaScale
    hfit c A hc hA (fun hsize => hcov h hn hT hsize) rho.1 alpha L halpha hL rho.2

end
end TomographyOracleCore.Revision.PhysicalMinimax
