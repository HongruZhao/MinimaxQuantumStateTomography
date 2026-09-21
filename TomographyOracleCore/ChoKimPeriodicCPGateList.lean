import TomographyOracleCore.ChoKimPeriodicAlternatingCPPrefix
import TomographyOracleCore.ChoKimGluingArithmetic

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance choKimGateListSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimGateListStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-- Matrix algebra carrying the literal periodic circuit third moment. -/
abbrev ChoKimPeriodicThirdSpace (n : ℕ) :=
  CStarMatrix (TripleIndex (Fin (2 ^ n)))
    (TripleIndex (Fin (2 ^ n))) ℂ

/-- The fixed literal alternating gate list, named once for the base,
one-step, closing, and final induction statements. -/
def choKimAlternatingThirdTwirlCPGates
    {n K : ℕ} (hdiv : K ∣ n) :
    List (Bool ×
      (ChoKimPeriodicThirdSpace n →CP ChoKimPeriodicThirdSpace n)) :=
  alternatingCPGateList
    (fun j ↦ finiteUnitaryThirdTwirlCP
      (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j))
    (fun j ↦ finiteUnitaryThirdTwirlCP
      (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j))

@[simp]
theorem length_choKimAlternatingThirdTwirlCPGates
    {n K : ℕ} (hdiv : K ∣ n) :
    (choKimAlternatingThirdTwirlCPGates hdiv).length =
      choKimGateVertices n K := by
  simp [choKimAlternatingThirdTwirlCPGates, choKimGateVertices]

end

end TomographyOracleCore
