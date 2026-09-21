import TomographyOracleCore.RelativeDesignLocalHaarReferenceCP
import TomographyOracleCore.RelativeDesignGlobalHaarReferenceCP
import TomographyOracleCore.RelativeDesignPairwiseActualHaarInactive

namespace TomographyOracleCore

universe u

open scoped CStarAlgebra

noncomputable section

local instance concretePairwiseInactiveSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance concretePairwiseInactiveStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Concrete actual-Haar inputs for one inactive Cho--Kim gluing step

The local `AB` support, the new `BC` gate, and their `ABC` union may have
different qubit counts.  This is essential for the growing active-prefix
induction.  The genuine global Haar Choi matrix uses the uniform global
permutation representation; the crossed B.26 representation is used only
inside the already-proved reference-composition comparison.  The two meet
on the diagonal global reference, never by an off-diagonal identification.
-/

theorem choKimLocalB21Error_le_d
    {D q : ℝ} (hq : 18 ≤ q) (hD : 2 * q ≤ D) :
    9 / (2 * D - 9) ≤
      (9 / (4 * q)) / (1 - 9 / (4 * q)) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hdenD : 0 < 2 * D - 9 := by nlinarith
  have hdenQ : 0 < 4 * q - 9 := by nlinarith
  have hd :
      (9 / (4 * q)) / (1 - 9 / (4 * q)) =
        9 / (4 * q - 9) := by
    field_simp
  rw [hd, div_le_div_iff₀ hdenD hdenQ]
  nlinarith

theorem choKimGlobalB22Error_le_b
    {D q : ℝ} (hq : 18 ≤ q) (hD : q + 9 ≤ D) :
    9 / (2 * D - 18) ≤ 9 / (2 * q) := by
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hdenD : 0 < 2 * D - 18 := by nlinarith
  have hdenQ : 0 < 2 * q := by positivity
  rw [div_le_div_iff₀ hdenD hdenQ]
  nlinarith

/-- One pairwise actual-Haar gluing step with all B.21/B.22 inputs
instantiated by concrete finite Pauli/Clifford exact third twirls.  The three
qubit counts are independent and are tied to the subsystem types by the
three supplied basis equivalences. -/
theorem relativeCPApproximation_concretePairwiseActualHaar_inactive
    (KAB KBC KABC : ℕ) (A B C R I : Type u)
    [Fintype A] [Fintype B] [Fintype C] [Fintype R] [Fintype I]
    [Nonempty A] [Nonempty B] [Nonempty C] [Nonempty R]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    [DecidableEq R] [DecidableEq I]
    (e : I ≃ ThreeReplicaABC A B C × ThreeReplica R)
    (idxAB : PauliBinaryWord KAB ≃ A × B)
    (idxBC : PauliBinaryWord KBC ≃ B × C)
    (idxABC : PauliBinaryWord KABC ≃ (A × B) × C)
    (q : ℝ) (hq : 18 ≤ q)
    (hqOverlap : q ≤ (Fintype.card B : ℝ))
    (hABDimension : 2 * q ≤ ((2 ^ KAB : ℕ) : ℝ))
    (hBCDimension : 2 * q ≤ ((2 ^ KBC : ℕ) : ℝ))
    (hABCDimension : q + 9 ≤ ((2 ^ KABC : ℕ) : ℝ)) :
    RelativeCPApproximation (choKimFThree q)
      (CompletelyPositiveMap.comp
        (CompletelyPositiveMap.finiteChoiTensorId e
          (finiteThreeMomentABHaarCP KAB A B C idxAB))
        (CompletelyPositiveMap.finiteChoiTensorId e
          (finiteThreeMomentBCHaarCP KBC A B C idxBC))).toLinearMap
      (CompletelyPositiveMap.finiteChoiTensorId e
        (finiteThreeMomentABCHaarCP KABC A B C idxABC)).toLinearMap := by
  have hKABreal : (18 : ℝ) ≤ ((2 ^ KAB : ℕ) : ℝ) := by
    nlinarith
  have hKBCreal : (18 : ℝ) ≤ ((2 ^ KBC : ℕ) : ℝ) := by
    nlinarith
  have hKAB : 18 ≤ 2 ^ KAB := by exact_mod_cast hKABreal
  have hKBC : 18 ≤ 2 ^ KBC := by exact_mod_cast hKBCreal
  have hABcard := card_AB_eq_two_pow_of_pauliEquiv KAB A B idxAB
  have hBCcard := card_BC_eq_two_pow_of_pauliEquiv KBC B C idxBC
  have hABCcard := card_ABC_eq_two_pow_of_pauliEquiv
    KABC A B C idxABC
  have hABDimension' :
      2 * q ≤ ((Fintype.card A * Fintype.card B : ℕ) : ℝ) := by
    rw [hABcard]
    exact hABDimension
  have hBCDimension' :
      2 * q ≤ ((Fintype.card B * Fintype.card C : ℕ) : ℝ) := by
    rw [hBCcard]
    exact hBCDimension
  have hAB :=
    (relativeCPApproximation_finiteThreeMomentABHaar_reference
      KAB A B C idxAB hKAB).mono_error
        (choKimLocalB21Error_le_d hq hABDimension')
  have hBC :=
    (relativeCPApproximation_finiteThreeMomentBCHaar_reference
      KBC A B C idxBC hKBC).mono_error
        (choKimLocalB21Error_le_d hq hBCDimension')
  have hglobalDimension' :
      q + 9 ≤
        ((Fintype.card A * Fintype.card B * Fintype.card C : ℕ) : ℝ) := by
    rw [hABCcard]
    exact hABCDimension
  have hDglobal :
      18 ≤ Fintype.card A * Fintype.card B * Fintype.card C := by
    have : (18 : ℝ) ≤
        ((Fintype.card A * Fintype.card B * Fintype.card C : ℕ) : ℝ) := by
      nlinarith [hglobalDimension']
    exact_mod_cast this
  have hglobal :=
    (relativeCPApproximation_finiteThreeMomentGlobalReference_haar
      KABC A B C idxABC hDglobal).mono_error
        (choKimGlobalB22Error_le_b hq hglobalDimension')
  exact relativeCPApproximation_pairwiseActualHaar_inactive_of_base
    A B C R I e q hq hqOverlap
    (finiteThreeMomentABHaarCP KAB A B C idxAB)
    (finiteThreeMomentBCHaarCP KBC A B C idxBC)
    (finiteThreeMomentABCHaarCP KABC A B C idxABC)
    hAB hBC hglobal

end

end TomographyOracleCore
