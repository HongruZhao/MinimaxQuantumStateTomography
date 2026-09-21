import TomographyOracleCore.ChoKimPeriodicActiveSupportGeometry
import TomographyOracleCore.FiniteUnitaryThirdTwirlReindex

namespace TomographyOracleCore

open MeasureTheory
open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance choKimFullHaarSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimFullHaarStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Arbitrary-coordinate Haar transport

The literal Cho--Kim binary-word enumeration is chosen from a cardinality
equality and need not be definitionally the earlier standard enumeration.
Haar invariance is therefore proved for an arbitrary basis equivalence and
only then specialized to the literal circuit basis.
-/

/-- A finite Clifford third twirl commutes with any binary-word-to-standard
finite basis equivalence of the correct cardinality. -/
theorem finiteUnitaryThirdTwirl_reindexPauliCoset_equiv
    (K : ℕ) (idx : PauliBinaryWord K ≃ Fin (2 ^ K)) (X : ThirdM K) :
    finiteUnitaryThirdTwirlLinearMap
        (fun a : PauliCosetCliffordEnsemble K ↦
          reindexUnitary idx (pauliCosetCliffordUnitary K a))
        (Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx) X) =
      Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx)
        (finitePauliCosetThirdTwirl K X) := by
  classical
  change
    ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
        ∑ a : PauliCosetCliffordEnsemble K,
          unitaryThirdConjugationGeneral
            (reindexUnitary idx (pauliCosetCliffordUnitary K a))
            (Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx) X) =
      Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx)
        (((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
          ∑ a : PauliCosetCliffordEnsemble K,
            unitaryThirdConjugation K
              (pauliCosetCliffordUnitary K a) X)
  rw [map_smul, map_sum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro a ha
  exact unitaryThirdConjugationGeneral_reindexUnitary idx
    (pauliCosetCliffordUnitary K a) X

/-- Normalized Haar probability is preserved by any finite coordinate
equivalence, not only by the originally chosen enumeration. -/
theorem map_reindexUnitary_pauliUnitaryHaarProbability_equiv
    (K : ℕ) (idx : PauliBinaryWord K ≃ Fin (2 ^ K)) :
    Measure.map (reindexUnitary idx) (pauliUnitaryHaarProbability K) =
      unitaryHaarProbability (2 ^ K) := by
  letI : Measure.IsHaarMeasure (pauliUnitaryHaarProbability K) := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
      (pauliUnitaryHaarProbability K) Set.univ isCompact_univ
    · simp
    · simp
    · simp
  letI : Measure.IsHaarMeasure (unitaryHaarProbability (2 ^ K)) := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
      (unitaryHaarProbability (2 ^ K)) Set.univ isCompact_univ
    · simp
    · simp
    · simp
  let phi := reindexUnitaryContinuousMulEquiv idx
  let nu := Measure.map phi (pauliUnitaryHaarProbability K)
  letI : IsProbabilityMeasure nu :=
    Measure.isProbabilityMeasure_map phi.continuous.aemeasurable
  letI : Measure.IsHaarMeasure nu := by
    dsimp only [nu]
    infer_instance
  have hnu : nu = unitaryHaarProbability (2 ^ K) := by
    apply Measure.isHaarMeasure_eq_of_isProbabilityMeasure
  change Measure.map phi (pauliUnitaryHaarProbability K) =
    unitaryHaarProbability (2 ^ K)
  exact hnu

/-- The literal Haar third twirl is natural under every finite basis
equivalence of the correct cardinality. -/
theorem unitaryHaarThirdTwirl_reindexPauli_equiv
    (K : ℕ) (idx : PauliBinaryWord K ≃ Fin (2 ^ K)) (X : ThirdM K) :
    unitaryHaarThirdTwirlLinearMap (2 ^ K)
        (Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx) X) =
      Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx)
        (pauliHaarThirdTwirl K X) := by
  let phi := reindexUnitaryContinuousMulEquiv idx
  let R := Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx)
  change
    (∫ V, unitaryThirdConjugationGeneral V (R X)
      ∂unitaryHaarProbability (2 ^ K)) =
      R (∫ U, unitaryThirdConjugation K U X
        ∂pauliUnitaryHaarProbability K)
  rw [← map_reindexUnitary_pauliUnitaryHaarProbability_equiv K idx]
  change
    (∫ V, unitaryThirdConjugationGeneral V (R X)
      ∂Measure.map phi (pauliUnitaryHaarProbability K)) = _
  have hphi : AEMeasurable phi (pauliUnitaryHaarProbability K) :=
    phi.continuous.aemeasurable
  have hg : AEStronglyMeasurable
      (fun V : Matrix.unitaryGroup (Fin (2 ^ K)) ℂ ↦
        unitaryThirdConjugationGeneral V (R X))
      (Measure.map phi (pauliUnitaryHaarProbability K)) :=
    (continuous_unitaryThirdConjugationGeneral
      (2 ^ K) (R X)).aestronglyMeasurable
  rw [integral_map hphi hg]
  simp_rw [show ∀ U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ,
      unitaryThirdConjugationGeneral (phi U) (R X) =
        R (unitaryThirdConjugation K U X) by
    intro U
    exact unitaryThirdConjugationGeneral_reindexUnitary idx U X]
  let Rc := R.toLinearEquiv.toContinuousLinearEquiv
  change
    (∫ U, Rc (unitaryThirdConjugation K U X)
      ∂pauliUnitaryHaarProbability K) =
      Rc (∫ U, unitaryThirdConjugation K U X
        ∂pauliUnitaryHaarProbability K)
  exact Rc.integral_comp_comm _

/-- The exact finite Clifford third design equals Haar after any correct
finite coordinate enumeration. -/
theorem finiteUnitaryThirdTwirlLinearMap_reindexedPauliCoset_eq_haar_equiv
    (K : ℕ) (idx : PauliBinaryWord K ≃ Fin (2 ^ K)) :
    finiteUnitaryThirdTwirlLinearMap
        (fun a : PauliCosetCliffordEnsemble K ↦
          reindexUnitary idx (pauliCosetCliffordUnitary K a)) =
      unitaryHaarThirdTwirlLinearMap (2 ^ K) := by
  apply LinearMap.ext
  intro Y
  let R := Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr idx)
  let X : ThirdM K := R.symm Y
  have hY : R X = Y := R.apply_symm_apply Y
  rw [← hY]
  rw [finiteUnitaryThirdTwirl_reindexPauliCoset_equiv,
    unitaryHaarThirdTwirl_reindexPauli_equiv]
  exact congrArg R
    (finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl K X)

/-- CP-map version, stated with an arbitrary target dimension and the exact
cardinality equality made explicit. -/
theorem pauliHaarThirdTwirlCP_reindexEquiv_toLinearMap_eq_haar
    (K D : ℕ) (idx : PauliBinaryWord K ≃ Fin D)
    (hD : D = 2 ^ K) :
    (CompletelyPositiveMap.reindexEquiv (tripleIndexCongr idx)
      (pauliHaarThirdTwirlCP K)).toLinearMap =
        unitaryHaarThirdTwirlLinearMap D := by
  subst D
  unfold pauliHaarThirdTwirlCP finitePauliCosetThirdTwirlCP
  rw [
    finiteUnitaryThirdTwirlCP_reindexEquiv,
    finiteUnitaryThirdTwirlCP_toLiteralLinearMap]
  apply LinearMap.ext
  intro X
  simp_rw [factorizationReindexUnitary_eq_reindexUnitary]
  exact LinearMap.congr_fun
    (finiteUnitaryThirdTwirlLinearMap_reindexedPauliCoset_eq_haar_equiv
      K idx) X

/-- The standard full-system CP representative in the literal Cho--Kim
basis has exactly the standard `Fin (2^n)` Haar third-twirl linear map. -/
theorem choKimFullHaarCP_toLinearMap
    {n K : ℕ} (hdiv : K ∣ n) :
    (choKimFullHaarCP hdiv).toLinearMap =
      unitaryHaarThirdTwirlLinearMap (2 ^ n) := by
  unfold choKimFullHaarCP
  apply pauliHaarThirdTwirlCP_reindexEquiv_toLinearMap_eq_haar
  exact (congrArg (fun q : ℕ ↦ 2 ^ q)
    (Nat.div_mul_cancel hdiv)).symm

end

end TomographyOracleCore
