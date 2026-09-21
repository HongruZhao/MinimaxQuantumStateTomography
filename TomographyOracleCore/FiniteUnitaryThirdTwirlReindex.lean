import TomographyOracleCore.BinaryCliffordExactThirdDesign
import TomographyOracleCore.BinaryCliffordPeriodicFinEnsemble
import TomographyOracleCore.FiniteUnitaryProjectiveRelativeThirdMoment

namespace TomographyOracleCore

open MeasureTheory Set
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

/-!
# Reindexing finite and Haar third twirls

The finite Clifford theorem is naturally stated on binary computational
words, whereas the tomography consumer uses the standard index `Fin (2^K)`.
This file proves that simultaneous row/column reindexing intertwines both the
finite third twirl and normalized Haar third twirl.  In particular, no
coordinate-invariance assertion is left as a premise.
-/

/-- Apply a coordinate equivalence independently to all three replicas. -/
def tripleIndexCongr {alpha beta : Type*} (e : alpha ≃ beta) :
    TripleIndex alpha ≃ TripleIndex beta :=
  e.prodCongr (e.prodCongr e)

@[simp] theorem tripleIndexCongr_apply {alpha beta : Type*}
    (e : alpha ≃ beta) (x : TripleIndex alpha) :
    tripleIndexCongr e x = (e x.1, e x.2.1, e x.2.2) := rfl

/-- Triple Kronecker products commute with simultaneous coordinate
reindexing. -/
theorem reindexAlgEquiv_matrixTensorThree
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (e : alpha ≃ beta) (A B C : Matrix alpha alpha ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr e)
        (matrixTensorThree A B C) =
      matrixTensorThree
        (Matrix.reindexAlgEquiv ℂ ℂ e A)
        (Matrix.reindexAlgEquiv ℂ ℂ e B)
        (Matrix.reindexAlgEquiv ℂ ℂ e C) := by
  ext x y
  rfl

/-- Reindexing a unitary and then taking its tensor cube is the same as
reindexing its tensor cube. -/
theorem unitaryTensorCubeGeneral_reindexUnitary
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {D : ℕ} (e : alpha ≃ Fin D)
    (U : Matrix.unitaryGroup alpha ℂ) :
    unitaryTensorCubeGeneral (reindexUnitary e U) =
      Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr e)
        (matrixTensorThree U.1 U.1 U.1) := by
  rw [reindexAlgEquiv_matrixTensorThree]
  rfl

/-- Ordinary third conjugation commutes with coordinate reindexing. -/
theorem unitaryThirdConjugationGeneral_reindexUnitary
    {alpha : Type*} [Fintype alpha] [DecidableEq alpha]
    {D : ℕ} (e : alpha ≃ Fin D)
    (U : Matrix.unitaryGroup alpha ℂ)
    (X : Matrix (TripleIndex alpha) (TripleIndex alpha) ℂ) :
    unitaryThirdConjugationGeneral (reindexUnitary e U)
        (Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr e) X) =
      Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr e)
        ((matrixTensorThree U.1 U.1 U.1 * X) *
          (matrixTensorThree U.1 U.1 U.1).conjTranspose) := by
  unfold unitaryThirdConjugationGeneral
  rw [unitaryTensorCubeGeneral_reindexUnitary]
  rw [← reindexAlgEquiv_conjTranspose (tripleIndexCongr e)]
  rw [← map_mul, ← map_mul]

/-- The reindexed general conjugation agrees with the binary-word
conjugation used in the Clifford third-design theorem. -/
theorem unitaryThirdConjugationGeneral_reindexPauli
    (K : ℕ)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    (X : ThirdM K) :
    unitaryThirdConjugationGeneral
        (reindexUnitary (pauliBinaryWordEquivFin K) U)
        (Matrix.reindexAlgEquiv ℂ ℂ
          (tripleIndexCongr (pauliBinaryWordEquivFin K)) X) =
      Matrix.reindexAlgEquiv ℂ ℂ
        (tripleIndexCongr (pauliBinaryWordEquivFin K))
        (unitaryThirdConjugation K U X) := by
  exact unitaryThirdConjugationGeneral_reindexUnitary
    (pauliBinaryWordEquivFin K) U X

/-- Reindexing intertwines the literal normalized finite Clifford third
twirl with the general finite-unitary third twirl. -/
theorem finiteUnitaryThirdTwirl_reindexPauliCoset
    (K : ℕ) (X : ThirdM K) :
    finiteUnitaryThirdTwirlLinearMap
        (fun e : PauliCosetCliffordEnsemble K ↦
          reindexUnitary (pauliBinaryWordEquivFin K)
            (pauliCosetCliffordUnitary K e))
        (Matrix.reindexAlgEquiv ℂ ℂ
          (tripleIndexCongr (pauliBinaryWordEquivFin K)) X) =
      Matrix.reindexAlgEquiv ℂ ℂ
        (tripleIndexCongr (pauliBinaryWordEquivFin K))
        (finitePauliCosetThirdTwirl K X) := by
  classical
  change
    ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
        ∑ e : PauliCosetCliffordEnsemble K,
          unitaryThirdConjugationGeneral
            (reindexUnitary (pauliBinaryWordEquivFin K)
              (pauliCosetCliffordUnitary K e))
            (Matrix.reindexAlgEquiv ℂ ℂ
              (tripleIndexCongr (pauliBinaryWordEquivFin K)) X) =
      Matrix.reindexAlgEquiv ℂ ℂ
        (tripleIndexCongr (pauliBinaryWordEquivFin K))
        (((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
          ∑ e : PauliCosetCliffordEnsemble K,
            unitaryThirdConjugation K
              (pauliCosetCliffordUnitary K e) X)
  rw [map_smul, map_sum]
  apply congrArg
  apply Finset.sum_congr rfl
  intro e he
  exact unitaryThirdConjugationGeneral_reindexPauli K
    (pauliCosetCliffordUnitary K e) X

/-- Simultaneous row/column reindexing is a multiplicative equivalence of
the two unitary groups. -/
noncomputable def reindexUnitaryContinuousMulEquiv
    {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (e : alpha ≃ beta) :
    Matrix.unitaryGroup alpha ℂ ≃ₜ* Matrix.unitaryGroup beta ℂ where
  toFun := reindexUnitary e
  invFun := reindexUnitary e.symm
  left_inv U := by
    apply Subtype.ext
    simp [reindexUnitary]
  right_inv U := by
    apply Subtype.ext
    simp [reindexUnitary]
  map_mul' U V := by
    apply Subtype.ext
    simp [reindexUnitary]
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    apply continuous_matrix
    intro i j
    change Continuous (fun U : Matrix.unitaryGroup alpha ℂ ↦
      U.1 (e.symm i) (e.symm j))
    exact (continuous_apply_apply _ _).comp continuous_subtype_val
  continuous_invFun := by
    apply continuous_induced_rng.mpr
    apply continuous_matrix
    intro i j
    change Continuous (fun U : Matrix.unitaryGroup beta ℂ ↦
      U.1 (e i) (e j))
    exact (continuous_apply_apply _ _).comp continuous_subtype_val

/-- Normalized Haar probability is preserved by simultaneous coordinate
reindexing. -/
theorem map_reindexUnitary_pauliUnitaryHaarProbability (K : ℕ) :
    Measure.map
        (reindexUnitary (pauliBinaryWordEquivFin K))
        (pauliUnitaryHaarProbability K) =
      unitaryHaarProbability (2 ^ K) := by
  letI : Measure.IsHaarMeasure (pauliUnitaryHaarProbability K) := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
      (pauliUnitaryHaarProbability K) univ isCompact_univ
    · simp
    · simp
    · simp
  letI : Measure.IsHaarMeasure (unitaryHaarProbability (2 ^ K)) := by
    apply Measure.isHaarMeasure_of_isCompact_nonempty_interior
      (unitaryHaarProbability (2 ^ K)) univ isCompact_univ
    · simp
    · simp
    · simp
  let phi := reindexUnitaryContinuousMulEquiv
    (pauliBinaryWordEquivFin K)
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

/-- The literal Haar third twirl is likewise intertwined by the coordinate
equivalence. -/
theorem unitaryHaarThirdTwirl_reindexPauli
    (K : ℕ) (X : ThirdM K) :
    unitaryHaarThirdTwirlLinearMap (2 ^ K)
        (Matrix.reindexAlgEquiv ℂ ℂ
          (tripleIndexCongr (pauliBinaryWordEquivFin K)) X) =
      Matrix.reindexAlgEquiv ℂ ℂ
        (tripleIndexCongr (pauliBinaryWordEquivFin K))
        (pauliHaarThirdTwirl K X) := by
  let phi := reindexUnitaryContinuousMulEquiv
    (pauliBinaryWordEquivFin K)
  let R := Matrix.reindexAlgEquiv ℂ ℂ
    (tripleIndexCongr (pauliBinaryWordEquivFin K))
  change
    (∫ V, unitaryThirdConjugationGeneral V (R X)
      ∂unitaryHaarProbability (2 ^ K)) =
      R (∫ U, unitaryThirdConjugation K U X
        ∂pauliUnitaryHaarProbability K)
  rw [← map_reindexUnitary_pauliUnitaryHaarProbability K]
  change
    (∫ V, unitaryThirdConjugationGeneral V (R X)
      ∂Measure.map phi (pauliUnitaryHaarProbability K)) = _
  have hphi : AEMeasurable phi (pauliUnitaryHaarProbability K) :=
    phi.continuous.aemeasurable
  have hg : AEStronglyMeasurable
      (fun V : Matrix.unitaryGroup (Fin (2 ^ K)) ℂ ↦
        unitaryThirdConjugationGeneral V (R X))
      (Measure.map phi (pauliUnitaryHaarProbability K)) :=
    (continuous_unitaryThirdConjugationGeneral (2 ^ K) (R X)).aestronglyMeasurable
  rw [integral_map hphi hg]
  simp_rw [show ∀ U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ,
      unitaryThirdConjugationGeneral (phi U) (R X) =
        R (unitaryThirdConjugation K U X) by
    intro U
    exact unitaryThirdConjugationGeneral_reindexPauli K U X]
  let Rc := R.toLinearEquiv.toContinuousLinearEquiv
  change
    (∫ U, Rc (unitaryThirdConjugation K U X)
      ∂pauliUnitaryHaarProbability K) =
      Rc (∫ U, unitaryThirdConjugation K U X
        ∂pauliUnitaryHaarProbability K)
  exact Rc.integral_comp_comm _

/-- Coordinate transport turns the already-proved binary Clifford theorem
into the exact finite-unitary-versus-Haar identity expected by the tomography
consumer. -/
theorem finiteUnitaryThirdTwirlLinearMap_reindexedPauliCoset_eq_haar
    (K : ℕ) :
    finiteUnitaryThirdTwirlLinearMap
        (fun e : PauliCosetCliffordEnsemble K ↦
          reindexUnitary (pauliBinaryWordEquivFin K)
            (pauliCosetCliffordUnitary K e)) =
      unitaryHaarThirdTwirlLinearMap (2 ^ K) := by
  apply LinearMap.ext
  intro Y
  let R := Matrix.reindexAlgEquiv ℂ ℂ
    (tripleIndexCongr (pauliBinaryWordEquivFin K))
  let X : ThirdM K := R.symm Y
  have hY : R X = Y := R.apply_symm_apply Y
  rw [← hY]
  rw [finiteUnitaryThirdTwirl_reindexPauliCoset,
    unitaryHaarThirdTwirl_reindexPauli]
  exact congrArg R
    (finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl K X)

end

end TomographyOracleCore
