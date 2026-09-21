import TomographyOracleCore.BinaryCliffordPeriodicPhysicalChannel
import TomographyOracleCore.FiniteUnitaryProjectivePOVM
import TomographyOracleCore.BinaryComputableIndex

namespace TomographyOracleCore

noncomputable section

/-- Binary computational words, enumerated by the standard finite type of
their exact cardinality. -/
noncomputable def pauliBinaryWordEquivFin (n : ℕ) :
    PauliBinaryWord n ≃ Fin (2 ^ n) :=
  Fintype.equivOfCardEq (by simp [PauliBinaryWord])

theorem reindexAlgEquiv_conjTranspose
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ e A.conjTranspose =
      (Matrix.reindexAlgEquiv ℂ ℂ e A).conjTranspose := by
  ext i j
  simp [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.conjTranspose_apply]

/-- Reindexing both coordinates of a unitary matrix preserves unitarity. -/
noncomputable def reindexUnitary
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (U : Matrix.unitaryGroup α ℂ) :
    Matrix.unitaryGroup β ℂ := by
  refine ⟨Matrix.reindexAlgEquiv ℂ ℂ e U.1, ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose]
  rw [← reindexAlgEquiv_conjTranspose]
  rw [← map_mul]
  have hU : U.1 * U.1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.2)
  rw [hU]
  simp

/-- Reindex the concrete periodic two-layer ensemble to the exact standard
Hilbert-space index `Fin (2^(m*K))`. -/
noncomputable def periodicTwoLayerCliffordUnitaryFin
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K) :
    Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  reindexUnitary (pauliBinaryWordEquivFin (m * K))
    (periodicTwoLayerCliffordUnitary m K σ e)

/-- Under the exact divisor condition, the periodic ensemble acts on the
paper's literal `n`-qubit type `Fin (2^n)`. -/
noncomputable def choKimPeriodicTwoLayerCliffordUnitaryFin
    {n K : ℕ} (hdiv : K ∣ n)
    (e : PeriodicTwoLayerCliffordEnsemble (n / K) K) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  reindexUnitary
    (computableChoKimBlockIndex hdiv)
    (choKimPeriodicTwoLayerCliffordUnitary (n / K) K e)

/-- The genuine finite projective POVM defined by the concrete periodic
two-layer circuit ensemble. -/
noncomputable def choKimPeriodicFiniteUnitaryProjectivePOVM
    {n K : ℕ} (hdiv : K ∣ n) :
    PhysicalPOVM.DominatedPOVM (2 ^ n)
      (Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) :=
  finiteUnitaryProjectivePOVM (2 ^ n) (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)

end
end TomographyOracleCore
