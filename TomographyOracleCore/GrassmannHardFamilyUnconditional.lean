import TomographyOracleCore.GrassmannInducedStateBridge
import TomographyOracleCore.GrassmannHardFamily

namespace TomographyOracleCore

open MatrixReduction

/-!
# Premise-free Grassmann hard family

This module closes the former metric-exclusion consumer boundary by feeding
the unconditional Grassmann packing into the existing hard-family
constructor.  The quantifier order matches the earlier conditional endpoint.
-/

/-- The exact-card Grassmann hard density family exists without a geometric
premise.  The common unitary orientation remains explicit for the downstream
minimax argument. -/
theorem exists_grassmannHardFamilyWitness_card_eq
    (k m : ℕ) (_hk : 3 ≤ k) (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    ∃ F : GrassmannHardFamilyWitness k m alpha L b,
      F.card = grassmannPackingCard k m := by
  obtain ⟨W, hWcard⟩ :=
    exists_complexGrassmannPackingWitness_card_eq hm hkm
  exact ⟨grassmannHardFamilyOfPacking W U alpha L b hm halpha hL hb0
    hbquarter hbscaled, by simpa using hWcard⟩

end TomographyOracleCore
