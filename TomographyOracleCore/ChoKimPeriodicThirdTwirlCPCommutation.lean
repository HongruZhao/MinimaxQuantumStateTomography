import TomographyOracleCore.ChoKimPeriodicThirdTwirlCPFold

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

set_option maxHeartbeats 800000

local instance choKimCPCommSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimCPCommStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Commutation and order-independence inside one block layer -/

theorem CompletelyPositiveMap.comp_assoc
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (Phi Psi Theta : A →CP A) :
    CompletelyPositiveMap.comp (CompletelyPositiveMap.comp Phi Psi) Theta =
      CompletelyPositiveMap.comp Phi (CompletelyPositiveMap.comp Psi Theta) := by
  apply DFunLike.coe_injective
  funext X
  rfl

@[simp] theorem CompletelyPositiveMap.comp_identity
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (Phi : A →CP A) :
    CompletelyPositiveMap.comp Phi CompletelyPositiveMap.identity = Phi := by
  apply DFunLike.coe_injective
  funext X
  rfl

@[simp] theorem CompletelyPositiveMap.identity_comp
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (Phi : A →CP A) :
    CompletelyPositiveMap.comp CompletelyPositiveMap.identity Phi = Phi := by
  apply DFunLike.coe_injective
  funext X
  rfl

/-- Finite third-twirl CP maps commute when every unitary in one ensemble
commutes with every unitary in the other. -/
theorem finiteUnitaryThirdTwirlCP_comm_of_pointwise_commute
    {D : ℕ} {E F : Type*}
    [Fintype E] [Nonempty E] [Fintype F] [Nonempty F]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (V : F → Matrix.unitaryGroup (Fin D) ℂ)
    (hcomm : ∀ e f, Commute (U e) (V f)) :
    CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP U) (finiteUnitaryThirdTwirlCP V) =
      CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP V) (finiteUnitaryThirdTwirlCP U) := by
  rw [← finiteUnitaryThirdTwirlCP_product V U,
    ← finiteUnitaryThirdTwirlCP_product U V]
  apply DFunLike.coe_injective
  funext X
  apply LinearMap.congr_fun _ X
  rw [finiteUnitaryThirdTwirlCP_toLiteralLinearMap,
    finiteUnitaryThirdTwirlCP_toLiteralLinearMap]
  calc
    finiteUnitaryThirdTwirlLinearMap
        (fun e : F × E ↦ U e.2 * V e.1) =
      finiteUnitaryThirdTwirlLinearMap
        (fun e : F × E ↦ V e.1 * U e.2) := by
          congr 1
          funext e
          exact (hcomm e.2 e.1).eq
    _ = finiteUnitaryThirdTwirlLinearMap
        (fun e : E × F ↦ V e.2 * U e.1) := by
          exact finiteUnitaryThirdTwirlLinearMap_equiv
            (Equiv.prodComm F E)
            (fun e : E × F ↦ V e.2 * U e.1)

/-- Forward-order CP fold `U₀ ∘ U₁ ∘ ...`; the already defined
reverse fold is `... ∘ U₁ ∘ U₀`. -/
def forwardFinThirdTwirlCPFold
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E] :
    (m : ℕ) →
      (Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) →
      CStarMatrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ →CP
        CStarMatrix (TripleIndex (Fin D)) (TripleIndex (Fin D)) ℂ
  | 0, _ => CompletelyPositiveMap.identity
  | m + 1, U =>
      CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP (U 0))
        (forwardFinThirdTwirlCPFold m (fun j ↦ U j.succ))

/-- A twirl commuting pointwise with every member of a family commutes with
the family's reverse CP fold. -/
theorem finiteUnitaryThirdTwirlCP_comm_reverseFold
    {D : ℕ} {E F : Type*}
    [Fintype E] [Nonempty E] [Fintype F] [Nonempty F]
    (V : F → Matrix.unitaryGroup (Fin D) ℂ)
    (m : ℕ) (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ)
    (hcomm : ∀ j f e, Commute (V f) (U j e)) :
    CompletelyPositiveMap.comp (finiteUnitaryThirdTwirlCP V)
        (reverseFinThirdTwirlCPFold m U) =
      CompletelyPositiveMap.comp (reverseFinThirdTwirlCPFold m U)
        (finiteUnitaryThirdTwirlCP V) := by
  induction m with
  | zero => simp [reverseFinThirdTwirlCPFold]
  | succ m ih =>
      rw [reverseFinThirdTwirlCPFold]
      rw [← CompletelyPositiveMap.comp_assoc]
      rw [ih (fun j ↦ U j.succ) (fun j f e ↦ hcomm j.succ f e)]
      rw [CompletelyPositiveMap.comp_assoc]
      rw [finiteUnitaryThirdTwirlCP_comm_of_pointwise_commute
        V (U 0) (fun f e ↦ hcomm 0 f e)]
      rw [← CompletelyPositiveMap.comp_assoc]

/-- Pairwise commuting embedded unitary families have order-independent
forward and reverse CP folds. -/
theorem forwardFinThirdTwirlCPFold_eq_reverse
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (m : ℕ) (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ)
    (hcomm : ∀ i j, i ≠ j → ∀ e f, Commute (U i e) (U j f)) :
    forwardFinThirdTwirlCPFold m U = reverseFinThirdTwirlCPFold m U := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [forwardFinThirdTwirlCPFold, reverseFinThirdTwirlCPFold]
      rw [ih (fun j ↦ U j.succ) (by
        intro i j hij e f
        exact hcomm i.succ j.succ (fun h ↦ hij (Fin.succ_injective _ h)) e f)]
      exact finiteUnitaryThirdTwirlCP_comm_reverseFold
        (U 0) m (fun j ↦ U j.succ)
        (fun j e f ↦ hcomm 0 j.succ (by
          intro h
          have hv := congrArg Fin.val h
          simp at hv) e f)

theorem choKimEmbeddedBlockPauliCosetCliffordUnitaryFin_commute
    {n K : ℕ} (hdiv : K ∣ n) {i j : Fin (n / K)} (hij : i ≠ j)
    (a b : PauliCosetCliffordEnsemble K) :
    Commute (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv i a)
      (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j b) := by
  let W : Fin (n / K) → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
    Function.update
      (Function.update (fun _ ↦ 1) i (pauliCosetCliffordUnitary K a))
      j (pauliCosetCliffordUnitary K b)
  have hWi : W i = pauliCosetCliffordUnitary K a := by
    simp [W, hij]
  have hWj : W j = pauliCosetCliffordUnitary K b := by
    simp [W]
  have hword := singleBlockEmbeddedUnitary_commute (n / K) K W i j
  have hinner : Commute
      (embeddedBlockPauliCosetCliffordUnitaryFin (n / K) K i a)
      (embeddedBlockPauliCosetCliffordUnitaryFin (n / K) K j b) := by
    simpa only [embeddedBlockPauliCosetCliffordUnitaryFin,
      blockTensorUnitaryFinMonoidHom, MonoidHom.comp_apply,
      singleBlockEmbeddedUnitary, hWi, hWj] using
        hword.map (factorizationReindexUnitaryMonoidHom
          (factorizationPauliBinaryWordEquivFin ((n / K) * K)))
  change Commute
    (factorizationReindexUnitary (choKimFactorizedToLiteralIndexEquiv hdiv)
      (embeddedBlockPauliCosetCliffordUnitaryFin (n / K) K i a))
    (factorizationReindexUnitary (choKimFactorizedToLiteralIndexEquiv hdiv)
      (embeddedBlockPauliCosetCliffordUnitaryFin (n / K) K j b))
  exact hinner.map (factorizationReindexUnitaryMonoidHom
    (choKimFactorizedToLiteralIndexEquiv hdiv))

theorem choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin_commute
    {n K : ℕ} (hdiv : K ∣ n) {i j : Fin (n / K)} (hij : i ≠ j)
    (a b : PauliCosetCliffordEnsemble K) :
    Commute (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv i a)
      (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j b) := by
  let sigma := cyclicQubitShift ((n / K) * K) (K / 2)
  let W : Fin (n / K) → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
    Function.update
      (Function.update (fun _ ↦ 1) i (pauliCosetCliffordUnitary K a))
      j (pauliCosetCliffordUnitary K b)
  have hWi : W i = pauliCosetCliffordUnitary K a := by
    simp [W, hij]
  have hWj : W j = pauliCosetCliffordUnitary K b := by
    simp [W]
  have hword := shiftedSingleBlockEmbeddedUnitary_commute
    (n / K) K sigma W i j
  have hinner : Commute
      (embeddedShiftedBlockPauliCosetCliffordUnitaryFin
        (n / K) K sigma i a)
      (embeddedShiftedBlockPauliCosetCliffordUnitaryFin
        (n / K) K sigma j b) := by
    change Commute
      (factorizationReindexUnitary
        (factorizationPauliBinaryWordEquivFin ((n / K) * K))
        (shiftedSingleBlockEmbeddedUnitary (n / K) K sigma i
          (pauliCosetCliffordUnitary K a)))
      (factorizationReindexUnitary
        (factorizationPauliBinaryWordEquivFin ((n / K) * K))
        (shiftedSingleBlockEmbeddedUnitary (n / K) K sigma j
          (pauliCosetCliffordUnitary K b)))
    rw [← hWi, ← hWj]
    exact hword.map (factorizationReindexUnitaryMonoidHom
      (factorizationPauliBinaryWordEquivFin ((n / K) * K)))
  change Commute
    (factorizationReindexUnitary (choKimFactorizedToLiteralIndexEquiv hdiv)
      (embeddedShiftedBlockPauliCosetCliffordUnitaryFin
        (n / K) K sigma i a))
    (factorizationReindexUnitary (choKimFactorizedToLiteralIndexEquiv hdiv)
      (embeddedShiftedBlockPauliCosetCliffordUnitaryFin
        (n / K) K sigma j b))
  exact hinner.map (factorizationReindexUnitaryMonoidHom
    (choKimFactorizedToLiteralIndexEquiv hdiv))

/-- In particular, the shifted layer can be traversed in forward block order
while remaining exactly the reverse fold used by the physical circuit. -/
theorem forwardFinThirdTwirlCPFold_choKimShifted_eq_reverse
    {n K : ℕ} (hdiv : K ∣ n) :
    forwardFinThirdTwirlCPFold (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv) =
      reverseFinThirdTwirlCPFold (n / K)
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv) := by
  apply forwardFinThirdTwirlCPFold_eq_reverse
  intro i j hij a b
  exact choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin_commute
    hdiv hij a b

end

end TomographyOracleCore
