import TomographyOracleCore.Revision.MatrixSolverInexactPeriodic
import TomographyOracleCore.Revision.AlgorithmResourcesPeriodicProjector
import TomographyOracleCore.Revision.PhysicalMinimaxClosure

/-! Physical interpretation and risk of the complete rational algorithm.
Every possible Born transcript has rational input, so the mathematical
extension takes its actual rational-solver branch. The selected risk and
minimax endpoints use the proved physical covariance theorem E.1 and
depend only on Lean's standard foundations.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM PhysicalRisk
open AlgorithmResources FinitePrecision PhysicalMinimax
open scoped BigOperators ENNReal

noncomputable section

set_option maxHeartbeats 1000000

/-- Every possible physical transcript selects the executable branch.
The rational encoding is mathematically unique; this statement does not
assert a decoder for arbitrary classically represented complex matrices. -/
theorem guardedRationalPeriodicSolve_eq_on_possibleSamples (n K T : ℕ)
    (hdiv : K ∣ n) (hT : 0 < T)
    (sample : Fin T → Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (hsample : sample ∈ possibleSamples (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) T) :
    ∃ Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
      castQMatrix Q = empiricalForwardMatrix sample ∧
      (guardedRationalPeriodicSolve n K T hdiv hT (empiricalForwardMatrix sample)).matrix =
        castQMatrix (rationalPeriodicSolve n K hdiv Q (rationalSampleTolerance T)) := by
  have hencoding : ∀ t, ∃ A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
      castQMatrix A = sample t := by
    rcases hsample with ⟨labels, rfl⟩
    intro t
    exact choKim_projector_has_rational_encoding hdiv (labels t).1 (labels t).2
  obtain ⟨Q, hQ⟩ := empiricalForwardMatrix_has_rational_encoding sample hencoding
  have hHerm := empiricalForwardMatrix_isHermitian_of_mem_possibleSamples
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) sample hsample
  refine ⟨Q, hQ, ?_⟩
  rw [← hQ]
  exact guardedRationalPeriodicSolve_eq_encoded n K T hdiv hT Q (by rw [hQ]; exact hHerm)

theorem ae_guardedRationalPeriodicSolve_computed {n K T : ℕ}
    (h : ChoKimBlockCondition n K) (hT : 0 < T) (rho : DensityOperator (Fin (2 ^ n))) :
    ∀ᵐ sample ∂periodicSampleLaw h T rho,
      ∃ Q : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex,
        castQMatrix Q = empiricalForwardMatrix sample ∧
        (guardedRationalPeriodicSolve n K T h.block_dvd hT (empiricalForwardMatrix sample)).matrix =
          castQMatrix (rationalPeriodicSolve n K h.block_dvd Q (rationalSampleTolerance T)) := by
  have hs := ae_mem_possibleSamples (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T rho
  exact hs.mono fun sample hsample =>
    guardedRationalPeriodicSolve_eq_on_possibleSamples n K T h.block_dvd hT sample hsample

def rationalPhysicalEstimator {n K T : ℕ} (h : ChoKimBlockCondition n K) (hT : 0 < T) :
    Estimator (2 ^ n) T :=
  algorithmPhysicalEstimator (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
    (guardedRationalPeriodicSolve n K T h.block_dvd hT)

/-- Selected-estimator physical upper rate. All computational inputs are
proved internally, as is the physical covariance theorem E.1. -/
theorem candidate2_rational_selectedPhysicalUpper :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → ∀ hT : 0 < T,
        ∀ alpha L : ℝ, 1 < alpha → 1 ≤ L →
          classWorstCaseRisk (2 ^ n) T alpha L
            (constantMatrixPOVMPhysicalDesign
              (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
            (rationalPhysicalEstimator h hT) ≤
          ENNReal.ofReal (algorithmUpperConstant c A *
            spectralDecayMinimaxRate (2 ^ n) (T : ℝ) L alpha) := by
  obtain ⟨c, A, hc, hA, hupper⟩ := candidate2_algorithm_selectedPhysicalUpper
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT alpha L halpha hL
  exact hupper h hn hT (guardedRationalPeriodicSolve n K T h.block_dvd hT)
    (Real.sqrt (((2 ^ n : ℕ) : ℝ) / (T : ℝ))) (Real.sqrt_nonneg _) le_rfl
    (fun Q rho => guardedRationalPeriodicSolve_fit n K T h.block_dvd h.block_pos hT Q rho)
    alpha L halpha hL

/-- The complete rational algorithm supplies the upper side of the actual
physical unrestricted/fixed-design minimax sandwich using the proved E.1. -/
theorem candidate2_rational_physicalMinimax :
    ∃ c A : ℝ, 1 ≤ c ∧ 0 < A ∧
      ∀ {n K T : ℕ} (h : ChoKimBlockCondition n K),
        0 < n → 0 < T →
        ExplicitPhysicalMinimaxTarget (2 ^ n) T
          (constantMatrixPOVMPhysicalDesign
            (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T)
          (fun _ => algorithmUpperConstant c A) := by
  obtain ⟨c, A, hc, hA, hupper⟩ := candidate2_rational_selectedPhysicalUpper
  refine ⟨c, A, hc, hA, ?_⟩
  intro n K T h hn hT
  apply physicalMinimaxSandwich_of_lower_and_simultaneousUpper
  · intro alpha L halpha hL
    have hlarge := h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn
    exact explicitSpectralDecayRateENNReal_le_unrestrictedRisk
      (2 ^ n) T L alpha (by omega) hT hL halpha
  · exact ⟨rationalPhysicalEstimator h hT, hupper h hn hT⟩

#print axioms guardedRationalPeriodicSolve_eq_on_possibleSamples
#print axioms ae_guardedRationalPeriodicSolve_computed
#print axioms candidate2_rational_selectedPhysicalUpper
#print axioms candidate2_rational_physicalMinimax

end
end TomographyOracleCore.Revision.MatrixSolver
