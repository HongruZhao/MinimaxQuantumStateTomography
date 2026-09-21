import TomographyOracleCore.BinaryCliffordPhysicalChannel
import TomographyOracleCore.BinarySymplecticBlockChannel
import TomographyOracleCore.ChoKimGluingArithmetic

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Independent blocks from the concrete generated Clifford ensemble

The local ensemble in `BinaryCliffordPhysicalChannel` consists of actual
finite-dimensional unitary matrices and has the exact nonidentity-Pauli
eigenvalue `1 / (2^K + 1)`.  This module applies the independent-product
counting theorem to that same generated group.  It proves the exact block
probability, its uniform floor, and the calibrated Cho--Kim lower bound.

The theorem here is a second-moment/channel calculation.  It does not assert
the separate order-three relative-design statement.
-/

/-- A family of independently chosen generated-group elements comes with a
concrete unitary lift on every block. -/
noncomputable def independentBinaryTransvectionUnitaryLifts
    (K m : ℕ) (c : Fin m → binaryTransvectionGroup K) :
    Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
  fun j ↦ binaryTransvectionUnitaryLift K (c j)

/-- Every block of the chosen independent family implements its advertised
binary symplectic action on all local Pauli matrices. -/
theorem independentBinaryTransvectionUnitaryLifts_spec
    (K m : ℕ) (c : Fin m → binaryTransvectionGroup K) (j : Fin m) :
    IsUnitaryPauliLift K (c j).1
      (independentBinaryTransvectionUnitaryLifts K m c j) :=
  binaryTransvectionUnitaryLift_spec K (c j)

/-- Exact conditional Z-hit probability for independent blocks of the
concretely liftable transvection-generated Clifford ensemble. -/
theorem independentBinaryTransvectionBlock_z_probability
    {K m : ℕ} (hK : 0 < K)
    (Q : Fin m → Option (NonidentityPauliLabel K)) :
    ((Fintype.card
        (IndependentBlockActionEvent
          (C := binaryTransvectionGroup K) Q
          (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
        Fintype.card (Fin m → binaryTransvectionGroup K) =
      (1 / ((2 : ℝ) ^ K + 1)) ^ activeBlockCount Q := by
  classical
  rw [independentBlockActionEvent_ratio,
    nonidentityZPauliFinset_ratio hK]

/-- Replacing the actual number of active blocks by the total block count
gives a label-independent probability floor. -/
theorem independentBinaryTransvectionBlock_z_probability_floor
    {K m : ℕ} (hK : 0 < K)
    (Q : Fin m → Option (NonidentityPauliLabel K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      ((Fintype.card
          (IndependentBlockActionEvent
            (C := binaryTransvectionGroup K) Q
            (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
        Fintype.card (Fin m → binaryTransvectionGroup K) := by
  rw [independentBinaryTransvectionBlock_z_probability hK Q]
  simpa [one_div] using
    (localCliffordHitFactor_pow_floor
      (K := K) (activeBlockCount_le Q))

/-- Averaging over any finite nonempty first layer preserves the generated
Clifford block floor. -/
theorem averagedIndependentBinaryTransvectionBlock_z_probability_floor
    {K m : ℕ} (hK : 0 < K)
    {U : Type*} [Fintype U] [Nonempty U]
    (Q : U → Fin m → Option (NonidentityPauliLabel K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      (∑ u : U,
        ((Fintype.card
            (IndependentBlockActionEvent
              (C := binaryTransvectionGroup K) (Q u)
              (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
          Fintype.card (Fin m → binaryTransvectionGroup K)) /
        Fintype.card U := by
  apply finite_average_ge_of_forall
  intro u
  exact independentBinaryTransvectionBlock_z_probability_floor hK (Q u)

/-- The literal finite average of global block-hit probabilities for the
concretely liftable generated ensemble. -/
noncomputable def averagedGlobalBinaryTransvectionHitProbability
    {K m : ℕ} {U : Type*} [Fintype U]
    (afterFirstLayer : U → PauliLabel (m * K)) : ℝ :=
  (∑ u : U,
    ((Fintype.card
        (IndependentBlockActionEvent
          (C := binaryTransvectionGroup K)
          (globalPauliOptionalBlocks (afterFirstLayer u))
          (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
      Fintype.card (Fin m → binaryTransvectionGroup K)) /
    Fintype.card U

/-- Exact global Pauli-block probability floor after an arbitrary first
layer, now using only the concretely liftable generated subgroup. -/
theorem averagedGlobalBinaryTransvectionHitProbability_floor
    {K m : ℕ} (hK : 0 < K)
    {U : Type*} [Fintype U] [Nonempty U]
    (afterFirstLayer : U → PauliLabel (m * K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      averagedGlobalBinaryTransvectionHitProbability afterFirstLayer := by
  unfold averagedGlobalBinaryTransvectionHitProbability
  exact averagedIndependentBinaryTransvectionBlock_z_probability_floor hK
    (fun u ↦ globalPauliOptionalBlocks (afterFirstLayer u))

/-- The Cho--Kim growth condition turns the literal finite generated-Clifford
block probability into the universal calibrated lower bound `1/2`.

This is the complete scalar curvature floor.  The input `afterFirstLayer`
may be any finite first-layer action on Pauli labels; no design property of
that layer is used in this second-moment calculation. -/
theorem ChoKimBlockCondition.half_le_calibrated_generated_block_probability
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    {U : Type*} [Fintype U] [Nonempty U]
    (afterFirstLayer : U → PauliLabel ((n / K) * K)) :
    (1 : ℝ) / 2 ≤
      ((2 : ℝ) ^ n + 1) *
        averagedGlobalBinaryTransvectionHitProbability afterFirstLayer := by
  calc
    (1 : ℝ) / 2 ≤ choKimCalibratedEigenvalueFloor n K :=
      h.half_le_calibratedEigenvalueFloor
    _ ≤ ((2 : ℝ) ^ n + 1) *
        averagedGlobalBinaryTransvectionHitProbability afterFirstLayer := by
      unfold choKimCalibratedEigenvalueFloor
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa [one_div] using
        (averagedGlobalBinaryTransvectionHitProbability_floor
          h.block_pos afterFirstLayer)

end TomographyOracleCore
