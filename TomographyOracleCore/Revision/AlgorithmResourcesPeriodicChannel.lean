import TomographyOracleCore.Revision.AlgorithmResourcesPeriodicRational
import TomographyOracleCore.BinaryComputableIndex

/-! Literal Fin(d)-indexed executable periodic forward channel. -/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix MatrixSolver
open scoped BigOperators

def qReindexMatrix {ι κ : Type*} (e : ι ≃ κ) (A : Matrix ι ι QComplex) :
    Matrix κ κ QComplex := fun i j => A (e.symm i) (e.symm j)

/-- Compute the multiplier table from the periodic block geometry and apply
it in the explicit binary basis. No channel or multiplier table is supplied. -/
def qPeriodicCalibratedChannel (n K : ℕ) (hdiv : K ∣ n)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex :=
  let index := computableChoKimBlockIndex hdiv
  qReindexMatrix index
    (rationalPauliChannel ((n / K) * K) (qPeriodicFullMultiplier n K)
      (qReindexMatrix index.symm A))

noncomputable section
set_option maxHeartbeats 1000000

theorem cast_qReindexMatrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (A : Matrix ι ι QComplex) :
    castQMatrix (qReindexMatrix e A) = Matrix.reindexAlgEquiv ℂ ℂ e (castQMatrix A) := rfl

theorem periodic_full_channel_reindex {n K : ℕ} (hdiv : K ∣ n)
    (A : Matrix (PauliBinaryWord ((n / K) * K)) (PauliBinaryWord ((n / K) * K)) ℂ) :
    finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
      (Matrix.reindexAlgEquiv ℂ ℂ (computableChoKimBlockIndex hdiv) A) =
      Matrix.reindexAlgEquiv ℂ ℂ (computableChoKimBlockIndex hdiv)
        (choKimPeriodicFullCalibratedBinaryLinearChannel hdiv A) := by
  change finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
      (Matrix.reindexAlgEquiv ℂ ℂ (choKimBlockWordEquivFin hdiv) A) =
      Matrix.reindexAlgEquiv ℂ ℂ (choKimBlockWordEquivFin hdiv)
        (choKimPeriodicFullCalibratedBinaryLinearChannel hdiv A)
  rw [finiteUnitaryFullCalibratedLinearChannel_apply,
    finiteUnitaryProjectiveLinearChannel_choKim_reindex,
    choKimPeriodicFullCalibratedBinaryLinearChannel_apply,
    choKimPeriodicBinaryMeasurementLinearChannel_apply]
  simp only [map_sub, map_smul, map_one, trace_reindexAlgEquiv,
    Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

/-- The efficient rational evaluator equals the exact physical channel
used by the statistical theorem, with no channel-interpretation premise. -/
theorem qPeriodicCalibratedChannel_correct (n K : ℕ) (hdiv : K ∣ n) (hK : 0 < K)
    (A : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) QComplex) :
    castQMatrix (qPeriodicCalibratedChannel n K hdiv A) =
      finiteUnitaryFullCalibratedLinearChannel (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (castQMatrix A) := by
  unfold qPeriodicCalibratedChannel
  rw [cast_qReindexMatrix, rationalPeriodicPauliChannel_correct hdiv hK,
    cast_qReindexMatrix, ← periodic_full_channel_reindex hdiv]
  congr 1
  ext i j
  simp [Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]

#print axioms qPeriodicCalibratedChannel_correct

end
end TomographyOracleCore.Revision.AlgorithmResources
