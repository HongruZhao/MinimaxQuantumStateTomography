import TomographyOracleCore.PeriodicCliffordFourthSectorProjectionUniqueness

namespace TomographyOracleCore

noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-!
# A natural averaging criterion for the physical fourth-copy map

The finite-sector uniqueness theorem asks directly for Hilbert--Schmidt
orthogonality of the residual.  A physical finite-group twirl supplies that
orthogonality in a more natural form: the twirl is self-adjoint for the
Hilbert--Schmidt pairing and it fixes every invariant sector.

This file proves that exact contraction and then combines it with the
verified thirty-sector inverse.  Thus the remaining physical Clifford
argument no longer has to prove residual orthogonality separately.
-/

/-- A Hilbert--Schmidt self-adjoint map that fixes every explicit sector has
residual orthogonal to all thirty sectors.  This is the exact contraction
needed by the sector-projection uniqueness theorem. -/
theorem qubitFourthSector_residual_orthogonal_of_selfAdjoint_fixed
    {r : ℕ}
    (physicalAverage : QubitFourthComplexSuperoperator r)
    (hselfAdjoint : ∀ A B,
      qubitFourthComplexHilbertSchmidt A (physicalAverage B) =
        qubitFourthComplexHilbertSchmidt (physicalAverage A) B)
    (hfixed : ∀ l : Fin 30,
      physicalAverage (qubitFourthSectorR r l) =
        qubitFourthSectorR r l)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (l : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (X - physicalAverage X) = 0 := by
  rw [qubitFourthComplexHilbertSchmidt_sub_right,
    hselfAdjoint (qubitFourthSectorR r l) X, hfixed l, sub_self]

/-- Natural finite-group-average criterion for the physical fourth-copy
identification.  In the nonsingular block regime, a sector-valued,
Hilbert--Schmidt self-adjoint map fixing every sector is exactly the explicit
Weingarten synthesis projector. -/
theorem qubitFourthSectorAverage_eq_synthesis_of_selfAdjoint_fixed_range
    {r : ℕ} (hr : 3 ≤ r)
    (physicalAverage : QubitFourthComplexSuperoperator r)
    (hselfAdjoint : ∀ A B,
      qubitFourthComplexHilbertSchmidt A (physicalAverage B) =
        qubitFourthComplexHilbertSchmidt (physicalAverage A) B)
    (hfixed : ∀ l : Fin 30,
      physicalAverage (qubitFourthSectorR r l) =
        qubitFourthSectorR r l)
    (hrange : ∀ X, ∃ c : Fin 30 → ℂ,
      physicalAverage X = qubitFourthSectorCombination r c) :
    physicalAverage = qubitFourthSectorSynthesisCandidate r := by
  apply LinearMap.ext
  intro X
  obtain ⟨c, hc⟩ := hrange X
  exact qubitFourthSectorProjection_unique hr X (physicalAverage X) c hc
    (qubitFourthSector_residual_orthogonal_of_selfAdjoint_fixed
      physicalAverage hselfAdjoint hfixed X)

end

end TomographyOracleCore
