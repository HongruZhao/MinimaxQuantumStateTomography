import TomographyOracleCore.BinarySymplecticPauli
import TomographyOracleCore.IndependentBlockPauliCounting

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Independent binary-symplectic block channel

This module specializes the generic independent-block counting theorem to
the concrete binary symplectic group.  It proves the exact conditional
second-layer Pauli hit probability and the uniform lower bound after
averaging over an arbitrary first layer.
-/

/-- The concrete diagonal subset has the exact fraction
`1 / (2^K + 1)` among nonidentity Pauli labels. -/
theorem nonidentityZPauliFinset_ratio
    {K : ℕ} (hK : 0 < K) :
    (((nonidentityZPauliFinset K).card : ℕ) : ℝ) /
        Fintype.card (NonidentityPauliLabel K) =
      1 / ((2 : ℝ) ^ K + 1) := by
  have hA : ((nonidentityZPauliFinset K).card : ℝ) =
      (2 : ℝ) ^ K - 1 := by
    rw [card_nonidentityZPauliFinset]
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_num
  have htotal : (Fintype.card (NonidentityPauliLabel K) : ℝ) =
      (4 : ℝ) ^ K - 1 := by
    rw [card_nonidentityPauliLabel]
    rw [Nat.cast_sub (Nat.one_le_pow K 4 (by norm_num))]
    norm_num
  rw [hA, htotal]
  exact nonidentityZPauli_ratio hK

/-- The number of active labels is at most the number of blocks. -/
theorem activeBlockCount_le
    {Ω : Type*} {m : ℕ} (Q : Fin m → Option Ω) :
    activeBlockCount Q ≤ m := by
  classical
  rw [activeBlockCount]
  calc
    (Finset.univ.filter fun i ↦ Q i ≠ none).card ≤
        (Finset.univ : Finset (Fin m)).card := Finset.card_filter_le _ _
    _ = m := Fintype.card_fin m

/-! ## Exact decomposition of a global Pauli label into blocks -/

/-- Reindex a Pauli label on `m*K` qubits as `m` consecutive labels on
`K` qubits. -/
noncomputable def pauliLabelBlockEquiv (m K : ℕ) :
    PauliLabel (m * K) ≃ (Fin m → PauliLabel K) where
  toFun p j :=
    (fun i ↦ p.1 (finProdFinEquiv (j, i)),
      fun i ↦ p.2 (finProdFinEquiv (j, i)))
  invFun Q :=
    (fun a ↦
      let ji := finProdFinEquiv.symm a
      (Q ji.1).1 ji.2,
    fun a ↦
      let ji := finProdFinEquiv.symm a
      (Q ji.1).2 ji.2)
  left_inv p := by
    apply Prod.ext <;> funext a
    · exact congrArg p.1 (by
        simpa [finProdFinEquiv_symm_apply] using
          (finProdFinEquiv.apply_symm_apply a))
    · exact congrArg p.2 (by
        simpa [finProdFinEquiv_symm_apply] using
          (finProdFinEquiv.apply_symm_apply a))
  right_inv Q := by
    funext j
    apply Prod.ext <;> funext i <;> simp

/-- Encode a local block label as inactive when it is the identity and as a
nonidentity subtype otherwise. -/
noncomputable def optionalNonidentityPauliBlock
    {K : ℕ} (q : PauliLabel K) : Option (NonidentityPauliLabel K) :=
  if hq : q = 0 then none else some ⟨q, hq⟩

@[simp] theorem optionalNonidentityPauliBlock_eq_none_iff
    {K : ℕ} (q : PauliLabel K) :
    optionalNonidentityPauliBlock q = none ↔ q = 0 := by
  classical
  by_cases hq : q = 0 <;> simp [optionalNonidentityPauliBlock, hq]

/-- Optional nonidentity block labels extracted from one global Pauli. -/
noncomputable def globalPauliOptionalBlocks
    {m K : ℕ} (p : PauliLabel (m * K)) :
    Fin m → Option (NonidentityPauliLabel K) :=
  fun j ↦ optionalNonidentityPauliBlock (pauliLabelBlockEquiv m K p j)

/-- A global Pauli activates at most all `m` blocks. -/
theorem activeBlockCount_globalPauliOptionalBlocks_le
    {m K : ℕ} (p : PauliLabel (m * K)) :
    activeBlockCount (globalPauliOptionalBlocks p) ≤ m :=
  activeBlockCount_le _

/-- Exact second-layer conditional probability for independent uniform
binary symplectic block actions. -/
theorem independentBinarySymplecticBlock_z_probability
    {K m : ℕ} (hK : 0 < K)
    (Q : Fin m → Option (NonidentityPauliLabel K)) :
    ((Fintype.card
        (IndependentBlockActionEvent
          (C := binarySymplecticGroup K) Q
          (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
        Fintype.card (Fin m → binarySymplecticGroup K) =
      (1 / ((2 : ℝ) ^ K + 1)) ^ activeBlockCount Q := by
  classical
  rw [independentBlockActionEvent_ratio,
    nonidentityZPauliFinset_ratio hK]

/-- Conditional probability floor obtained by replacing the actual number
of active second-layer blocks by the total block count. -/
theorem independentBinarySymplecticBlock_z_probability_floor
    {K m : ℕ} (hK : 0 < K)
    (Q : Fin m → Option (NonidentityPauliLabel K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      ((Fintype.card
          (IndependentBlockActionEvent
            (C := binarySymplecticGroup K) Q
            (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
        Fintype.card (Fin m → binarySymplecticGroup K) := by
  rw [independentBinarySymplecticBlock_z_probability hK Q]
  simpa [one_div] using
    (localCliffordHitFactor_pow_floor
      (K := K) (activeBlockCount_le Q))

/-- Averaging the exact conditional probabilities over an arbitrary finite,
nonempty first-layer choice preserves the same uniform floor. -/
theorem averagedIndependentBinarySymplecticBlock_z_probability_floor
    {K m : ℕ} (hK : 0 < K)
    {U : Type*} [Fintype U] [Nonempty U]
    (Q : U → Fin m → Option (NonidentityPauliLabel K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      (∑ u : U,
        ((Fintype.card
            (IndependentBlockActionEvent
              (C := binarySymplecticGroup K) (Q u)
              (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
          Fintype.card (Fin m → binarySymplecticGroup K)) /
        Fintype.card U := by
  apply finite_average_ge_of_forall
  intro u
  exact independentBinarySymplecticBlock_z_probability_floor hK (Q u)

/-- Fully specialized finite probability statement after an arbitrary first
layer has mapped the Pauli label to a global `m*K`-qubit label. -/
theorem averagedGlobalPauliBlocks_z_probability_floor
    {K m : ℕ} (hK : 0 < K)
    {U : Type*} [Fintype U] [Nonempty U]
    (afterFirstLayer : U → PauliLabel (m * K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      (∑ u : U,
        ((Fintype.card
            (IndependentBlockActionEvent
              (C := binarySymplecticGroup K)
              (globalPauliOptionalBlocks (afterFirstLayer u))
              (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
          Fintype.card (Fin m → binarySymplecticGroup K)) /
        Fintype.card U :=
  averagedIndependentBinarySymplecticBlock_z_probability_floor hK
    (fun u ↦ globalPauliOptionalBlocks (afterFirstLayer u))

end TomographyOracleCore
