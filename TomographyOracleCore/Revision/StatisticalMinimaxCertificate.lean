import TomographyOracleCore.Revision.ConstantEndpoints

/-!
Standalone minimax certificate for the calibrated forward estimator in the
periodic experiment. The lower bound ranges over all permitted nonadaptive
single-copy designs; the upper bound uses the exact calibrated forward fit.
-/

namespace TomographyOracleCore.Verification

open PhysicalRisk PhysicalPOVM Revision.ConstantEndpoints

/-- Under only the paper's arithmetic/model conditions, one estimator chosen
before alpha and L achieves the same rate as the unrestricted physical lower
bound. The positive lower constant is included explicitly. -/
theorem periodic_statistical_minimax_unconditional
    {n K T : ℕ} (h : ChoKimBlockCondition n K)
    (hn : 0 < n) (hT : 0 < T) :
    let D := 2 ^ n
    let design := constantMatrixPOVMPhysicalDesign
      (choKimPeriodicFiniteUnitaryProjectivePOVM h.block_dvd) T
    ∃ estimator : Estimator D T, ∀ alpha L : ℝ,
      1 < alpha → 1 ≤ L →
      0 < explicitDecayLowerConstant alpha ∧
      ENNReal.ofReal
          (explicitDecayLowerConstant alpha *
            spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
        PhysicalRisk.unrestrictedRisk D T alpha L ∧
      PhysicalRisk.unrestrictedRisk D T alpha L ≤
        PhysicalRisk.fixedDesignRisk D T alpha L design ∧
      PhysicalRisk.fixedDesignRisk D T alpha L design ≤
        classWorstCaseRisk D T alpha L design estimator ∧
      classWorstCaseRisk D T alpha L design estimator ≤
        ENNReal.ofReal
          (certifiedUpperConstant * spectralDecayMinimaxRate D (T : ℝ) L alpha) := by
  dsimp only
  let estimator := Revision.PhysicalMinimax.physicalEstimator
    (by positivity : 0 < 2 ^ n)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) T
  refine ⟨estimator, ?_⟩
  intro alpha L halpha hL
  have hD : 514 ≤ 2 ^ n :=
    (by decide : 514 ≤ 65536).trans
      (h.sixtyFiveThousandFiveHundredThirtySix_le_dimension hn)
  exact ⟨explicitDecayLowerConstant_pos alpha,
    explicitSpectralDecayRateENNReal_le_unrestrictedRisk
      (2 ^ n) T L alpha hD hT hL halpha,
    PhysicalRisk.unrestrictedRisk_le_fixedDesignRisk _,
    PhysicalRisk.fixedDesignRisk_le_estimator _ estimator,
    exactFit_selectedPhysicalUpper_sharp h hn hT alpha L halpha hL⟩

#print axioms periodic_statistical_minimax_unconditional

end TomographyOracleCore.Verification
