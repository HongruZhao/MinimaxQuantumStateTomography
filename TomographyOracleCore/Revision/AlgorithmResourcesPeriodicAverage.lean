import TomographyOracleCore.Revision.AlgorithmResourcesPeriodicOrbit

/-! Exact physical two-layer multiplier as an average over a polynomial-size orbit. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1000000

theorem pauli_coset_family_average (m K : ℕ)
    (f : (Fin m → binaryTransvectionGroup K) → ℝ) :
    (∑ e : Fin m → PauliCosetCliffordEnsemble K, f (fun j => (e j).2)) /
      Fintype.card (Fin m → PauliCosetCliffordEnsemble K) =
      (∑ g : Fin m → binaryTransvectionGroup K, f g) /
        Fintype.card (Fin m → binaryTransvectionGroup K) := by
  classical
  have hs := Equiv.sum_comp (pauliCosetBlockFamilyEquiv m K)
    (fun ag : (Fin m → PauliLabel K) × (Fin m → binaryTransvectionGroup K) => f ag.2)
  change (∑ e : Fin m → PauliCosetCliffordEnsemble K, f (fun j => (e j).2)) =
    ∑ ag : (Fin m → PauliLabel K) × (Fin m → binaryTransvectionGroup K), f ag.2 at hs
  rw [hs, Fintype.card_congr (pauliCosetBlockFamilyEquiv m K), Fintype.card_prod]
  simp only [Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Nat.cast_mul]
  have hc : (Fintype.card (Fin m → PauliLabel K) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hg : (Fintype.card (Fin m → binaryTransvectionGroup K) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- This identity removes all Clifford-group enumeration. The remaining
orbit is a subset of the d² global Pauli labels. -/
theorem periodic_hit_as_orbit_average
    (m K : ℕ) (hK : 0 < K) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) :
    periodicTwoLayerHitProbability m K σ p =
      (∑ q : GlobalSupportOrbit m K (permutePauliLabel σ.symm p),
        (1 / ((2 : ℝ) ^ K + 1)) ^
          activeBlockCount (globalPauliOptionalBlocks (permutePauliLabel σ q.1))) /
        Fintype.card (GlobalSupportOrbit m K (permutePauliLabel σ.symm p)) := by
  classical
  rw [periodicTwoLayerHitProbability_eq_averagedGlobal,
    averagedGlobalBinaryTransvectionHitProbability]
  simp_rw [independentBinaryTransvectionBlock_z_probability hK]
  rw [pauli_coset_family_average m K (fun g =>
    (1 / ((2 : ℝ) ^ K + 1)) ^
      activeBlockCount (globalPauliOptionalBlocks (shiftedBlockPauliAction m K σ g p)))]
  exact global_block_action_uniform_average m K (permutePauliLabel σ.symm p)
    (fun q => (1 / ((2 : ℝ) ^ K + 1)) ^
      activeBlockCount (globalPauliOptionalBlocks (permutePauliLabel σ q)))

#print axioms periodic_hit_as_orbit_average

end
end TomographyOracleCore.Revision.AlgorithmResources
