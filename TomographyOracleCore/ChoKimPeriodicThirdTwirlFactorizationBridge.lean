import TomographyOracleCore.FiniteUnitaryThirdTwirlIndependentBlocks
import TomographyOracleCore.BinaryCliffordPeriodicFinEnsemble

namespace TomographyOracleCore

noncomputable section

theorem factorizationReindexUnitary_trans
    {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (e₁ : α ≃ β) (e₂ : β ≃ γ)
    (U : Matrix.unitaryGroup α ℂ) :
    factorizationReindexUnitary e₂
        (factorizationReindexUnitary e₁ U) =
      factorizationReindexUnitary (e₁.trans e₂) U := by
  apply Subtype.ext
  rfl

theorem factorizationReindexUnitary_eq_reindexUnitary
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (idx : α ≃ β) (U : Matrix.unitaryGroup α ℂ) :
    factorizationReindexUnitary idx U = reindexUnitary idx U := by
  apply Subtype.ext
  rfl

/-- The exact binary-word enumeration used by the literal Cho--Kim
standard-index circuit under `K ∣ n`. -/
noncomputable def choKimLiteralBinaryWordEquivFin
    {n K : ℕ} (hdiv : K ∣ n) :
    PauliBinaryWord ((n / K) * K) ≃ Fin (2 ^ n) :=
  computableChoKimBlockIndex hdiv

/-- The coordinate comparison from the factorization module's standard
enumeration to the literal Cho--Kim enumeration. -/
noncomputable def choKimFactorizedToLiteralIndexEquiv
    {n K : ℕ} (hdiv : K ∣ n) :
    Fin (2 ^ ((n / K) * K)) ≃ Fin (2 ^ n) :=
  (factorizationPauliBinaryWordEquivFin ((n / K) * K)).symm.trans
    (choKimLiteralBinaryWordEquivFin hdiv)

/-- Transport the factorized periodic unitary to the literal Cho--Kim
standard coordinate type. -/
noncomputable def choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin
    {n K : ℕ} (hdiv : K ∣ n)
    (e : PeriodicTwoLayerCliffordEnsemble (n / K) K) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  factorizationReindexUnitary
    (choKimFactorizedToLiteralIndexEquiv hdiv)
    (periodicTwoLayerCliffordUnitaryFactorizedFin
      (n / K) K
      (cyclicQubitShift ((n / K) * K) (K / 2)) e)

/-- After the explicit coordinate comparison, the factorized periodic
circuit is exactly the literal Cho--Kim finite unitary. -/
theorem choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin_eq_literal
    {n K : ℕ} (hdiv : K ∣ n)
    (e : PeriodicTwoLayerCliffordEnsemble (n / K) K) :
    choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin hdiv e =
      choKimPeriodicTwoLayerCliffordUnitaryFin hdiv e := by
  let a := factorizationPauliBinaryWordEquivFin ((n / K) * K)
  let b := choKimLiteralBinaryWordEquivFin hdiv
  have hab : a.trans (a.symm.trans b) = b := by
    ext x
    simp
  unfold choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin
  unfold periodicTwoLayerCliffordUnitaryFactorizedFin
  change factorizationReindexUnitary (a.symm.trans b)
      (factorizationReindexUnitary a
        (periodicTwoLayerCliffordUnitary (n / K) K
          (cyclicQubitShift ((n / K) * K) (K / 2)) e)) = _
  rw [factorizationReindexUnitary_trans, hab]
  rw [factorizationReindexUnitary_eq_reindexUnitary]
  rfl

/-- The literal Cho--Kim third twirl is therefore exactly the transported
third twirl of the factorized periodic circuit. -/
theorem finiteUnitaryThirdTwirlLinearMap_choKimFactorized_eq_literal
    {n K : ℕ} (hdiv : K ∣ n) :
    finiteUnitaryThirdTwirlLinearMap
        (choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin hdiv) =
      finiteUnitaryThirdTwirlLinearMap
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) := by
  apply congrArg finiteUnitaryThirdTwirlLinearMap
  funext e
  exact
    choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin_eq_literal hdiv e

/-- Transport the unshifted factorized block layer to the literal Cho--Kim
standard coordinates. -/
noncomputable def choKimFactorizedBlockLayerFin
    {n K : ℕ} (hdiv : K ∣ n)
    (e : Fin (n / K) → PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  factorizationReindexUnitary
    (choKimFactorizedToLiteralIndexEquiv hdiv)
    (blockPauliCosetCliffordUnitaryFin (n / K) K e)

/-- Transport the shifted factorized block layer to the literal Cho--Kim
standard coordinates. -/
noncomputable def choKimFactorizedShiftedBlockLayerFin
    {n K : ℕ} (hdiv : K ∣ n)
    (e : Fin (n / K) → PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  factorizationReindexUnitary
    (choKimFactorizedToLiteralIndexEquiv hdiv)
    (shiftedBlockPauliCosetCliffordUnitaryFin (n / K) K
      (cyclicQubitShift ((n / K) * K) (K / 2)) e)

theorem choKimPeriodicTwoLayerCliffordUnitaryFin_eq_factorizedLayers
    {n K : ℕ} (hdiv : K ∣ n)
    (e : PeriodicTwoLayerCliffordEnsemble (n / K) K) :
    choKimPeriodicTwoLayerCliffordUnitaryFin hdiv e =
      choKimFactorizedBlockLayerFin hdiv e.2 *
        choKimFactorizedShiftedBlockLayerFin hdiv e.1 := by
  rw [←
    choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin_eq_literal
      hdiv e]
  unfold choKimPeriodicTwoLayerCliffordUnitaryFromFactorizationFin
  rw [periodicTwoLayerCliffordUnitaryFactorizedFin_eq_mul,
    factorizationReindexUnitary_mul]
  rfl

/-- The literal Cho--Kim third twirl is the exact composition of its two
transported independent block-layer twirls. -/
theorem finiteUnitaryThirdTwirlLinearMap_choKim_eq_factorizedLayer_comp
    {n K : ℕ} (hdiv : K ∣ n) :
    finiteUnitaryThirdTwirlLinearMap
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) =
      (finiteUnitaryThirdTwirlLinearMap
        (choKimFactorizedBlockLayerFin hdiv)).comp
      (finiteUnitaryThirdTwirlLinearMap
        (choKimFactorizedShiftedBlockLayerFin hdiv)) := by
  have hunitary : choKimPeriodicTwoLayerCliffordUnitaryFin hdiv =
      fun e => choKimFactorizedBlockLayerFin hdiv e.2 *
        choKimFactorizedShiftedBlockLayerFin hdiv e.1 := by
    funext e
    exact choKimPeriodicTwoLayerCliffordUnitaryFin_eq_factorizedLayers hdiv e
  rw [hunitary]
  exact finiteUnitaryThirdTwirlLinearMap_product
    (U₁ := choKimFactorizedShiftedBlockLayerFin hdiv)
    (U₂ := choKimFactorizedBlockLayerFin hdiv)

/-- One transported unshifted single-block Clifford unitary. -/
noncomputable def choKimEmbeddedBlockPauliCosetCliffordUnitaryFin
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K))
    (a : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  factorizationReindexUnitary
    (choKimFactorizedToLiteralIndexEquiv hdiv)
    (embeddedBlockPauliCosetCliffordUnitaryFin (n / K) K j a)

/-- One transported shifted single-block Clifford unitary. -/
noncomputable def choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K))
    (a : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℂ :=
  factorizationReindexUnitary
    (choKimFactorizedToLiteralIndexEquiv hdiv)
    (embeddedShiftedBlockPauliCosetCliffordUnitaryFin (n / K) K
      (cyclicQubitShift ((n / K) * K) (K / 2)) j a)

theorem reverseFinUnitaryProduct_choKimEmbeddedBlock_eq_layer
    {n K : ℕ} (hdiv : K ∣ n)
    (e : Fin (n / K) → PauliCosetCliffordEnsemble K) :
    reverseFinUnitaryProduct (n / K)
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv) e =
      choKimFactorizedBlockLayerFin hdiv e := by
  let phi := factorizationReindexUnitaryMonoidHom
    (choKimFactorizedToLiteralIndexEquiv hdiv)
  calc
    reverseFinUnitaryProduct (n / K)
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv) e =
      reverseFinProduct (n / K) (fun j => phi
        (embeddedBlockPauliCosetCliffordUnitaryFin
          (n / K) K j (e j))) := rfl
    _ = phi (reverseFinProduct (n / K) (fun j =>
        embeddedBlockPauliCosetCliffordUnitaryFin
          (n / K) K j (e j))) := by
      rw [map_reverseFinProduct phi]
    _ = phi (blockPauliCosetCliffordUnitaryFin (n / K) K e) := by
      exact congrArg phi
        (reverseFinUnitaryProduct_embeddedBlock_eq_layer (n / K) K e)
    _ = choKimFactorizedBlockLayerFin hdiv e := rfl

theorem reverseFinUnitaryProduct_choKimEmbeddedShiftedBlock_eq_layer
    {n K : ℕ} (hdiv : K ∣ n)
    (e : Fin (n / K) → PauliCosetCliffordEnsemble K) :
    reverseFinUnitaryProduct (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv) e =
      choKimFactorizedShiftedBlockLayerFin hdiv e := by
  let sigma := cyclicQubitShift ((n / K) * K) (K / 2)
  let phi := factorizationReindexUnitaryMonoidHom
    (choKimFactorizedToLiteralIndexEquiv hdiv)
  calc
    reverseFinUnitaryProduct (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv) e =
      reverseFinProduct (n / K) (fun j => phi
        (embeddedShiftedBlockPauliCosetCliffordUnitaryFin
          (n / K) K sigma j (e j))) := rfl
    _ = phi (reverseFinProduct (n / K) (fun j =>
        embeddedShiftedBlockPauliCosetCliffordUnitaryFin
          (n / K) K sigma j (e j))) := by
      rw [map_reverseFinProduct phi]
    _ = phi (shiftedBlockPauliCosetCliffordUnitaryFin
        (n / K) K sigma e) := by
      exact congrArg phi
        (reverseFinUnitaryProduct_embeddedShiftedBlock_eq_layer
          (n / K) K sigma e)
    _ = choKimFactorizedShiftedBlockLayerFin hdiv e := rfl

theorem finiteUnitaryThirdTwirlLinearMap_choKimBlockLayer_eq_fold
    {n K : ℕ} (hdiv : K ∣ n) :
    finiteUnitaryThirdTwirlLinearMap
        (choKimFactorizedBlockLayerFin hdiv) =
      reverseFinThirdTwirlFold (n / K)
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv) := by
  have hsample : choKimFactorizedBlockLayerFin hdiv =
      reverseFinUnitaryProduct (n / K)
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv) := by
    funext e
    exact (reverseFinUnitaryProduct_choKimEmbeddedBlock_eq_layer
      hdiv e).symm
  rw [hsample]
  exact finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_eq_fold
    (n / K) (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv)

theorem finiteUnitaryThirdTwirlLinearMap_choKimShiftedBlockLayer_eq_fold
    {n K : ℕ} (hdiv : K ∣ n) :
    finiteUnitaryThirdTwirlLinearMap
        (choKimFactorizedShiftedBlockLayerFin hdiv) =
      reverseFinThirdTwirlFold (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv) := by
  have hsample : choKimFactorizedShiftedBlockLayerFin hdiv =
      reverseFinUnitaryProduct (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv) := by
    funext e
    exact (reverseFinUnitaryProduct_choKimEmbeddedShiftedBlock_eq_layer
      hdiv e).symm
  rw [hsample]
  exact finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_eq_fold
    (n / K) (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv)

/-- Final exact circuit identity: the literal Cho--Kim third twirl is the
composition of the explicit unshifted and shifted single-block twirl folds. -/
theorem finiteUnitaryThirdTwirlLinearMap_choKim_eq_localFolds
    {n K : ℕ} (hdiv : K ∣ n) :
    finiteUnitaryThirdTwirlLinearMap
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) =
      (reverseFinThirdTwirlFold (n / K)
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv)).comp
      (reverseFinThirdTwirlFold (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv)) := by
  rw [finiteUnitaryThirdTwirlLinearMap_choKim_eq_factorizedLayer_comp]
  rw [finiteUnitaryThirdTwirlLinearMap_choKimBlockLayer_eq_fold,
    finiteUnitaryThirdTwirlLinearMap_choKimShiftedBlockLayer_eq_fold]

end
end TomographyOracleCore
