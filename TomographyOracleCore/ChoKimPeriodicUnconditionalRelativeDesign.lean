import TomographyOracleCore.BinaryCliffordPeriodicPOVMCurvature
import TomographyOracleCore.FiniteUnitaryProjectiveRelativeThirdMoment
import TomographyOracleCore.ChoKimPeriodicActiveSupportGeometry
import TomographyOracleCore.ChoKimPeriodicAlternatingCPPrefix
import TomographyOracleCore.ChoKimPeriodicCPGateList
import TomographyOracleCore.ChoKimFullHaarLinearMap
import TomographyOracleCore.ChoKimPeriodicBaseClosingGeometry
import TomographyOracleCore.ChoKimPeriodicNonclosingStepGeometry
import TomographyOracleCore.FiniteUnitaryProjectiveCStarRelativeThirdMoment
import TomographyOracleCore.RelativeDesignApproximationCalculus
import TomographyOracleCore.RelativeDesignConcretePairwiseActualHaarInactive

namespace TomographyOracleCore

open scoped CStarAlgebra ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

local instance choKimUnconditionalSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimUnconditionalStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

local instance choKimUnconditionalQubitFinNonempty (n : ℕ) :
    Nonempty (Fin (2 ^ n)) :=
  Fin.pos_iff_nonempty.mp (by positivity)

/-!
# Unconditional periodic Cho--Kim relative third design

This module is the final consumer of the literal alternating-prefix circuit,
the active-support Haar family, and the concrete Schuster--Haferkamp--Huang
pairwise gluing theorem.  The scalar error schedule below is unconditional
and is deliberately stated separately from the geometric specialization.

The final map theorem will use

* `globalReference i := choKimActiveHaarCP h.block_dvd i`;
* the literal gate at `i + 1` itself as `localReference i`, hence local error
  zero by `relativeCPApproximation_zero_refl`;
* reference error `choKimFThree (choKimOverlapDimension K)` at every step;
* the exact multiplicative schedule defined below.

No approximate reference is identified with Haar.  The one-step reference
comparison is the actual-Haar-to-actual-Haar B.21--B.27 consequence, and the
last active reference is rewritten to the standard full Haar CP map.

In that one-step consequence the B.26 composition calculation uses the
crossed mixed permutation representation, whereas genuine global Haar uses
`finiteThreeMomentGlobalHaarChoiQ`.  They are connected only through their
proved equality on the diagonal global reference.  No off-diagonal mixed-Q
Haar identity is used.
-/

/-- Error after `i` pairwise actual-Haar gluings. -/
def choKimPeriodicThirdDesignErrorAt (K i : ℕ) : ℝ :=
  (1 + choKimFThree (choKimOverlapDimension K)) ^ i - 1

/-- Error after all edges of the alternating Cho--Kim spanning path. -/
def choKimPeriodicThirdDesignError (n K : ℕ) : ℝ :=
  choKimPeriodicThirdDesignErrorAt K (choKimGateVertices n K - 1)

@[simp]
theorem choKimPeriodicThirdDesignErrorAt_final (n K : ℕ) :
    choKimPeriodicThirdDesignErrorAt K (choKimGateVertices n K - 1) =
      choKimPeriodicThirdDesignError n K := by
  rfl

@[simp]
theorem choKimPeriodicThirdDesignErrorAt_zero (K : ℕ) :
    choKimPeriodicThirdDesignErrorAt K 0 = 0 := by
  simp [choKimPeriodicThirdDesignErrorAt]

theorem choKimPeriodicThirdDesignError_eq (n K : ℕ) :
    choKimPeriodicThirdDesignError n K =
      (1 + choKimFThree (choKimOverlapDimension K)) ^
          (2 * (n / K) - 1) - 1 := by
  rfl

/-- The chosen schedule satisfies exactly the three-factor recurrence used by
the constructive alternating-prefix theorem when the literal local gate has
zero approximation error. -/
theorem choKimPeriodicThirdDesignErrorAt_succ (K i : ℕ) :
    choKimPeriodicThirdDesignErrorAt K (i + 1) =
      (1 + choKimPeriodicThirdDesignErrorAt K i) * (1 + 0) *
          (1 + choKimFThree (choKimOverlapDimension K)) - 1 := by
  rw [choKimPeriodicThirdDesignErrorAt, choKimPeriodicThirdDesignErrorAt,
    pow_succ]
  ring

theorem choKimPeriodicThirdDesignErrorAt_nonneg
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    0 ≤ choKimPeriodicThirdDesignErrorAt K i := by
  have hF : 0 ≤ choKimFThree (choKimOverlapDimension K) :=
    choKimFThree_nonneg (h.eighteen_le_overlap hn)
  exact sub_nonneg.mpr (one_le_pow₀ (by linarith))

theorem choKimPeriodicThirdDesignErrorAt_mono
    {n K i j : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hij : i ≤ j) :
    choKimPeriodicThirdDesignErrorAt K i ≤
      choKimPeriodicThirdDesignErrorAt K j := by
  have hF : 0 ≤ choKimFThree (choKimOverlapDimension K) :=
    choKimFThree_nonneg (h.eighteen_le_overlap hn)
  unfold choKimPeriodicThirdDesignErrorAt
  exact sub_le_sub_right (pow_le_pow_right₀ (by linarith) hij) 1

theorem ChoKimBlockCondition.choKimPeriodicThirdDesignError_le_one
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimPeriodicThirdDesignError n K ≤ 1 := by
  apply h.relativeDesignError_le_one_of_raw_gluing hn
  rfl

/-- Uniform bounds needed by the constructive prefix induction. -/
theorem ChoKimBlockCondition.choKimPeriodicThirdDesignErrorAt_bounds
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i ≤ choKimGateVertices n K - 1) :
    0 ≤ choKimPeriodicThirdDesignErrorAt K i ∧
      choKimPeriodicThirdDesignErrorAt K i ≤ 1 := by
  constructor
  · exact choKimPeriodicThirdDesignErrorAt_nonneg h hn
  · exact (choKimPeriodicThirdDesignErrorAt_mono h hn hi).trans
      (h.choKimPeriodicThirdDesignError_le_one hn)

/-- The literal next gate is used as its own local reference, so its local
relative error has the required uniform bounds. -/
theorem choKimPeriodicZeroLocalError_bounds (i : ℕ) :
    (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 := by
  norm_num

/-- Every reference-gluing step uses the same nonnegative pairwise loss. -/
theorem ChoKimBlockCondition.choKimPeriodicReferenceError_nonneg
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    0 ≤ choKimFThree (choKimOverlapDimension K) :=
  choKimFThree_nonneg (h.eighteen_le_overlap hn)

/-- Named-gate-list form of the exact-absorption closing step. -/
theorem ChoKimBlockCondition.choKimPeriodicClosingReferenceStep
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    let closing := 2 * (n / K) - 1
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (if (alternatingCPGateAt
          (choKimAlternatingThirdTwirlCPGates h.block_dvd) closing).1 then
        CompletelyPositiveMap.comp
          (alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) closing).2
          (choKimActiveHaarCP h.block_dvd (2 * (n / K) - 2))
       else CompletelyPositiveMap.comp
          (choKimActiveHaarCP h.block_dvd (2 * (n / K) - 2))
          (alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) closing).2
      ).toLinearMap
      (choKimActiveHaarCP h.block_dvd closing).toLinearMap := by
  dsimp only [choKimAlternatingThirdTwirlCPGates]
  exact h.alternatingActiveHaar_closing_relativeCP hn

/-! ## Literal periodic relative third design -/

/-- The literal two-layer periodic Clifford ensemble is a relative third
design with the exact accumulated Cho--Kim error.  All reference maps in the
proof are actual Haar twirls on their active supports. -/
theorem ChoKimBlockCondition.relativeCPApproximation_periodicThirdDesign
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ)
      (choKimPeriodicThirdDesignError n K)
      (finiteUnitaryThirdTwirlLinearMap
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd))
      (unitaryHaarThirdTwirlLinearMap (2 ^ n)) := by
  have hm : 0 < n / K := h.blockQuotient_pos hn
  have hiter := relativeCPApproximation_choKim_of_alternating_prefix
    (hdiv := h.block_dvd) (hm := hm)
    (globalReference := fun i ↦ choKimActiveHaarCP h.block_dvd i)
    (localReference := fun i ↦
      (alternatingCPGateAt
        (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1)).2)
    (error := fun i ↦ choKimPeriodicThirdDesignErrorAt K i)
    (localError := fun _ ↦ 0)
    (referenceError := fun _ ↦
      choKimFThree (choKimOverlapDimension K))
    (Haar := choKimFullHaarCP h.block_dvd)
    (herrorBounds := by
      intro i hi
      exact h.choKimPeriodicThirdDesignErrorAt_bounds hn hi)
    (hlocalBounds := by
      intro i hi
      exact choKimPeriodicZeroLocalError_bounds i)
    (hreferenceError := by
      intro i hi
      exact h.choKimPeriodicReferenceError_nonneg hn)
    (hbase := by
      rw [choKimPeriodicThirdDesignErrorAt_zero]
      rw [h.alternatingCPPrefix_zero_eq_activeHaar hn]
      exact relativeCPApproximation_zero_refl
        (choKimActiveHaarCP h.block_dvd 0))
    (hlocal := by
      intro i hi
      simpa [choKimAlternatingThirdTwirlCPGates] using
        (relativeCPApproximation_zero_refl
          (alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1)).2))
    (hreference := by
      intro i hi
      have hgateAlias :
          alternatingCPGateAt
              (alternatingCPGateList
                (fun j ↦ finiteUnitaryThirdTwirlCP
                  (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin
                    h.block_dvd j))
                (fun j ↦ finiteUnitaryThirdTwirlCP
                  (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
                    h.block_dvd j)))
              (i + 1) =
            alternatingCPGateAt
              (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1) := by
        rfl
      rw [hgateAlias]
      by_cases hclosing : i = 2 * (n / K) - 2
      · subst i
        have hsucc : 2 * (n / K) - 2 + 1 = 2 * (n / K) - 1 := by
          omega
        simpa only [hsucc] using
          h.choKimPeriodicClosingReferenceStep hn
      · have hnonclosing : i < 2 * (n / K) - 2 := by
          omega
        exact
          h.relativeCPApproximation_nonclosingActiveHaarStep hn hnonclosing)
    (hrecurrence := by
      intro i hi
      exact choKimPeriodicThirdDesignErrorAt_succ K i)
    (hfinalReference :=
      TomographyOracleCore.choKimActiveHaarCP_closing_eq_full h hn)
  rw [finiteUnitaryThirdTwirlCP_toLiteralLinearMap,
    choKimFullHaarCP_toLinearMap] at hiter
  simpa [choKimPeriodicThirdDesignError, choKimGateVertices] using hiter

end
end TomographyOracleCore
