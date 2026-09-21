import TomographyOracleCore.BinaryCliffordPeriodicThirdTwirlFactorization

namespace TomographyOracleCore

open scoped BigOperators
noncomputable section

/-- Normalized finite third twirls are unchanged by an equivalence of the
finite ensemble index. -/
theorem finiteUnitaryThirdTwirlLinearMap_equiv
    {D : ℕ} {E F : Type*}
    [Fintype E] [Fintype F] [Nonempty E] [Nonempty F]
    (idx : E ≃ F) (U : F → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlLinearMap (fun e : E => U (idx e)) =
      finiteUnitaryThirdTwirlLinearMap U := by
  apply LinearMap.ext
  intro X
  change ((Fintype.card E : ℂ)⁻¹) •
      (∑ e : E, unitaryThirdConjugationGeneral (U (idx e)) X) =
    ((Fintype.card F : ℂ)⁻¹) •
      (∑ f : F, unitaryThirdConjugationGeneral (U f) X)
  rw [Fintype.card_congr idx]
  congr 1
  exact idx.sum_comp
    (fun f => unitaryThirdConjugationGeneral (U f) X)

/-- Reverse-order product of a finite family in an arbitrary monoid. -/
def reverseFinProduct {G : Type*} [Monoid G] :
    (m : ℕ) → (Fin m → G) → G
  | 0, _ => 1
  | m + 1, f => reverseFinProduct m (fun j => f j.succ) * f 0

theorem reverseFinProduct_eq_reverse_ofFn_prod
    {G : Type*} [Monoid G] (m : ℕ) (f : Fin m → G) :
    reverseFinProduct m f = (List.ofFn f).reverse.prod := by
  induction m with
  | zero => simp [reverseFinProduct]
  | succ m ih =>
      rw [reverseFinProduct, List.ofFn_succ, List.reverse_cons,
        List.prod_append, List.prod_singleton]
      exact congrArg (fun z => z * f 0) (ih (fun j => f j.succ))

theorem map_reverseFinProduct
    {G H : Type*} [Monoid G] [Monoid H]
    (phi : G →* H) (m : ℕ) (f : Fin m → G) :
    phi (reverseFinProduct m f) =
      reverseFinProduct m (fun j => phi (f j)) := by
  induction m with
  | zero => simp [reverseFinProduct]
  | succ m ih =>
      rw [reverseFinProduct, map_mul, reverseFinProduct]
      rw [ih (fun j => f j.succ)]

/-- Reverse multiplication of all coordinate singles reconstructs the
original function, without assuming that the coordinate monoids commute. -/
theorem reverseFinProduct_pi_mulSingle
    {m : ℕ} {M : Fin m → Type*} [∀ j, Monoid (M j)]
    (x : ∀ j, M j) :
    reverseFinProduct m (fun j => Pi.mulSingle j (x j)) = x := by
  rw [reverseFinProduct_eq_reverse_ofFn_prod]
  let l : List (Fin m) := (List.ofFn (fun j : Fin m => j)).reverse
  have hl : l.Nodup := by
    dsimp [l]
    exact List.nodup_reverse.mpr
      (List.nodup_ofFn_ofInjective Function.injective_id)
  have hset : l.toFinset = Finset.univ := by
    ext j
    simp [l]
  have hcomm : (↑l.toFinset : Set (Fin m)).Pairwise
      (Function.onFun Commute (fun j => Pi.mulSingle j (x j))) := by
    intro i hi j hj hij
    exact Pi.mulSingle_apply_commute x i j
  have hprod := Finset.noncommProd_toFinset l
    (fun j => Pi.mulSingle j (x j)) hcomm hl
  calc
    (List.ofFn fun j => Pi.mulSingle j (x j)).reverse.prod =
        (l.map fun j => Pi.mulSingle j (x j)).prod := by
      dsimp [l]
      rw [List.map_reverse, List.map_ofFn]
      apply congrArg List.prod
      apply congrArg List.reverse
      apply congrArg List.ofFn
      funext j
      rfl
    _ = l.toFinset.noncommProd
        (fun j => Pi.mulSingle j (x j)) hcomm := hprod.symm
    _ = Finset.univ.noncommProd
        (fun j => Pi.mulSingle j (x j))
        (fun i _ j _ _ => Pi.mulSingle_apply_commute x i j) := by
      congr
    _ = x := Finset.noncommProd_mulSingle x

/-- Reverse-order product of one independently selected unitary from each
position.  The reverse convention makes the normalized twirl recursion have
the usual `later.comp earlier` orientation. -/
noncomputable def reverseFinUnitaryProduct
    {D : ℕ} {E : Type*} (m : ℕ)
    (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ)
    (e : Fin m → E) : Matrix.unitaryGroup (Fin D) ℂ :=
  reverseFinProduct m (fun j => U j (e j))

@[simp] theorem reverseFinUnitaryProduct_cons
    {D : ℕ} {E : Type*} (m : ℕ)
    (U : Fin (m + 1) → E → Matrix.unitaryGroup (Fin D) ℂ)
    (a : E) (e : Fin m → E) :
    reverseFinUnitaryProduct (m + 1) U (Fin.cons a e) =
      reverseFinUnitaryProduct m (fun j => U j.succ) e * U 0 a := by
  unfold reverseFinUnitaryProduct
  rw [reverseFinProduct]
  congr 1

/-- One-step factorization of the normalized twirl of an independent
reverse product. -/
theorem finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_succ
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (m : ℕ)
    (U : Fin (m + 1) → E → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlLinearMap
        (reverseFinUnitaryProduct (m + 1) U) =
      (finiteUnitaryThirdTwirlLinearMap
          (reverseFinUnitaryProduct m (fun j => U j.succ))).comp
        (finiteUnitaryThirdTwirlLinearMap (U 0)) := by
  let split : E × (Fin m → E) ≃ (Fin (m + 1) → E) :=
    Fin.consEquiv (fun _ : Fin (m + 1) => E)
  rw [← finiteUnitaryThirdTwirlLinearMap_equiv split
    (reverseFinUnitaryProduct (m + 1) U)]
  have hsample :
      (fun e : E × (Fin m → E) =>
        reverseFinUnitaryProduct (m + 1) U (split e)) =
      (fun e : E × (Fin m → E) =>
        reverseFinUnitaryProduct m (fun j => U j.succ) e.2 *
          U 0 e.1) := by
    funext e
    rcases e with ⟨a, v⟩
    change reverseFinUnitaryProduct (m + 1) U (Fin.cons a v) = _
    exact reverseFinUnitaryProduct_cons m U a v
  rw [hsample]
  exact finiteUnitaryThirdTwirlLinearMap_product
      (U₁ := U 0)
      (U₂ := reverseFinUnitaryProduct m (fun j => U j.succ))

/-- Explicit recursive composition of the independently sampled local
third twirls. -/
noncomputable def reverseFinThirdTwirlFold
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E] :
    (m : ℕ) →
      (Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) →
      FiniteUnitaryThirdSpace D →ₗ[ℂ] FiniteUnitaryThirdSpace D
  | 0, _ => LinearMap.id
  | m + 1, U =>
      (reverseFinThirdTwirlFold m (fun j => U j.succ)).comp
        (finiteUnitaryThirdTwirlLinearMap (U 0))

theorem unitaryThirdConjugationGeneral_one
    {D : ℕ} (X : FiniteUnitaryThirdSpace D) :
    unitaryThirdConjugationGeneral
        (1 : Matrix.unitaryGroup (Fin D) ℂ) X = X := by
  unfold unitaryThirdConjugationGeneral unitaryTensorCubeGeneral
  rw [show ((1 : Matrix.unitaryGroup (Fin D) ℂ).1) =
      (1 : Matrix (Fin D) (Fin D) ℂ) by rfl]
  rw [matrixTensorThree_one]
  simp

theorem finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_zero
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : Fin 0 → E → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlLinearMap
        (reverseFinUnitaryProduct 0 U) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  change ((Fintype.card (Fin 0 → E) : ℂ)⁻¹) •
      (∑ _e : Fin 0 → E,
        unitaryThirdConjugationGeneral
          (1 : Matrix.unitaryGroup (Fin D) ℂ) X) = X
  simp [unitaryThirdConjugationGeneral_one]

/-- The normalized third twirl of an independent finite product is exactly
the explicit recursive composition of its single-position twirls. -/
theorem finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_eq_fold
    {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (m : ℕ) (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryThirdTwirlLinearMap
        (reverseFinUnitaryProduct m U) =
      reverseFinThirdTwirlFold m U := by
  induction m with
  | zero =>
      exact finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_zero U
  | succ m ih =>
      rw [finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_succ]
      rw [ih (fun j => U j.succ)]
      rfl

/-- Coordinate reindexing as a monoid homomorphism on unitary groups. -/
noncomputable def factorizationReindexUnitaryMonoidHom
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (idx : α ≃ β) :
    Matrix.unitaryGroup α ℂ →* Matrix.unitaryGroup β ℂ where
  toFun := factorizationReindexUnitary idx
  map_one' := by
    apply Subtype.ext
    simp [factorizationReindexUnitary]
  map_mul' := factorizationReindexUnitary_mul idx

/-- Reindexed block tensor as one monoid homomorphism. -/
noncomputable def blockTensorUnitaryFinMonoidHom (m K : ℕ) :
    (Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) →*
      Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  (factorizationReindexUnitaryMonoidHom
    (factorizationPauliBinaryWordEquivFin (m * K))).comp
      (blockTensorUnitaryMonoidHom m K)

/-- One Pauli-coset Clifford choice embedded into the `j`th consecutive
block and reindexed to the standard Hilbert-space coordinates. -/
noncomputable def embeddedBlockPauliCosetCliffordUnitaryFin
    (m K : ℕ) (j : Fin m) (a : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  blockTensorUnitaryFinMonoidHom m K
    (Pi.mulSingle j (pauliCosetCliffordUnitary K a))

theorem reverseFinUnitaryProduct_embeddedBlock_eq_layer
    (m K : ℕ) (e : Fin m → PauliCosetCliffordEnsemble K) :
    reverseFinUnitaryProduct m
        (embeddedBlockPauliCosetCliffordUnitaryFin m K) e =
      blockPauliCosetCliffordUnitaryFin m K e := by
  let x : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
    fun j => pauliCosetCliffordUnitary K (e j)
  let phi := blockTensorUnitaryFinMonoidHom m K
  change reverseFinProduct m (fun j => phi (Pi.mulSingle j (x j))) = phi x
  rw [← map_reverseFinProduct phi]
  rw [reverseFinProduct_pi_mulSingle]

/-- The finite third twirl of one independent unshifted block layer is the
explicit reverse fold of its embedded single-block finite twirls. -/
theorem finiteUnitaryThirdTwirlLinearMap_blockLayer_eq_fold
    (m K : ℕ) :
    finiteUnitaryThirdTwirlLinearMap
        (blockPauliCosetCliffordUnitaryFin m K) =
      reverseFinThirdTwirlFold m
        (embeddedBlockPauliCosetCliffordUnitaryFin m K) := by
  have hsample : blockPauliCosetCliffordUnitaryFin m K =
      reverseFinUnitaryProduct m
        (embeddedBlockPauliCosetCliffordUnitaryFin m K) := by
    funext e
    exact (reverseFinUnitaryProduct_embeddedBlock_eq_layer m K e).symm
  rw [hsample]
  exact finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_eq_fold
    m (embeddedBlockPauliCosetCliffordUnitaryFin m K)

/-- Shifted, reindexed block tensor as one monoid homomorphism. -/
noncomputable def shiftedBlockTensorUnitaryFinMonoidHom
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) :
    (Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) →*
      Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  (factorizationReindexUnitaryMonoidHom
    (factorizationPauliBinaryWordEquivFin (m * K))).comp
      ((MulAut.conj (binaryWordPermutationUnitary σ)).toMonoidHom.comp
        (blockTensorUnitaryMonoidHom m K))

/-- One Pauli-coset Clifford choice embedded into the `j`th shifted block
and reindexed to standard Hilbert-space coordinates. -/
noncomputable def embeddedShiftedBlockPauliCosetCliffordUnitaryFin
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (j : Fin m) (a : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (Fin (2 ^ (m * K))) ℂ :=
  shiftedBlockTensorUnitaryFinMonoidHom m K σ
    (Pi.mulSingle j (pauliCosetCliffordUnitary K a))

theorem reverseFinUnitaryProduct_embeddedShiftedBlock_eq_layer
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : Fin m → PauliCosetCliffordEnsemble K) :
    reverseFinUnitaryProduct m
        (embeddedShiftedBlockPauliCosetCliffordUnitaryFin m K σ) e =
      shiftedBlockPauliCosetCliffordUnitaryFin m K σ e := by
  let x : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
    fun j => pauliCosetCliffordUnitary K (e j)
  let phi := shiftedBlockTensorUnitaryFinMonoidHom m K σ
  calc
    reverseFinUnitaryProduct m
        (embeddedShiftedBlockPauliCosetCliffordUnitaryFin m K σ) e =
        reverseFinProduct m (fun j => phi (Pi.mulSingle j (x j))) := rfl
    _ = phi (reverseFinProduct m (fun j => Pi.mulSingle j (x j))) := by
      rw [map_reverseFinProduct phi]
    _ = phi x := by rw [reverseFinProduct_pi_mulSingle]
    _ = shiftedBlockPauliCosetCliffordUnitaryFin m K σ e := by
      unfold phi shiftedBlockTensorUnitaryFinMonoidHom
      unfold shiftedBlockPauliCosetCliffordUnitaryFin
      rw [shiftedBlockPauliCosetCliffordUnitary_eq_conj]
      rfl

/-- The finite third twirl of one independent shifted block layer is the
explicit reverse fold of its embedded single-block finite twirls. -/
theorem finiteUnitaryThirdTwirlLinearMap_shiftedBlockLayer_eq_fold
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) :
    finiteUnitaryThirdTwirlLinearMap
        (shiftedBlockPauliCosetCliffordUnitaryFin m K σ) =
      reverseFinThirdTwirlFold m
        (embeddedShiftedBlockPauliCosetCliffordUnitaryFin m K σ) := by
  have hsample : shiftedBlockPauliCosetCliffordUnitaryFin m K σ =
      reverseFinUnitaryProduct m
        (embeddedShiftedBlockPauliCosetCliffordUnitaryFin m K σ) := by
    funext e
    exact (reverseFinUnitaryProduct_embeddedShiftedBlock_eq_layer
      m K σ e).symm
  rw [hsample]
  exact finiteUnitaryThirdTwirlLinearMap_reverseFinUnitaryProduct_eq_fold
    m (embeddedShiftedBlockPauliCosetCliffordUnitaryFin m K σ)

end
end TomographyOracleCore
