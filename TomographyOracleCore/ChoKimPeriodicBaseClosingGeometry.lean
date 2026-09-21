import TomographyOracleCore.ChoKimPeriodicActiveSupportGeometry
import TomographyOracleCore.ChoKimFullHaarLinearMap
import TomographyOracleCore.FiniteChoiTensorIdThirdTwirlReindex
import TomographyOracleCore.PauliHaarThirdTwirlAbsorption
import TomographyOracleCore.RelativeDesignApproximationCalculus

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance choKimBaseClosingSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimBaseClosingStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Initial support and closing-edge geometry -/

/-- Removing block zero from `Fin (r+1)` leaves the consecutive block
coordinates `Fin r`. -/
def blockZeroComplementIndexEquiv (r : ℕ) :
    Fin r ≃ {j : Fin (r + 1) // j ≠ 0} :=
  finSuccAboveEquiv 0

/-- The complement of block zero is exactly the binary word on the
remaining `r*K` consecutive qubits. -/
def blockZeroComplementTailEquiv (r K : ℕ) :
    ({j : Fin (r + 1) // j ≠ 0} → PauliBinaryWord K) ≃
      PauliBinaryWord (r * K) :=
  (Equiv.piCongrLeft
      (fun _ : {j : Fin (r + 1) // j ≠ 0} ↦ PauliBinaryWord K)
      (blockZeroComplementIndexEquiv r)).symm.trans
    (binaryWordBlockEquiv r K).symm

/-- Split off the first `K` qubits from `(r+1)*K` qubits, with the tail
written at its simplified size `r*K`. -/
def headBlockBinaryWordEquiv (r K : ℕ) :
    PauliBinaryWord ((r + 1) * K) ≃
      PauliBinaryWord K × PauliBinaryWord (r * K) :=
  let eFin : Fin K ⊕ Fin (r * K) ≃ Fin ((r + 1) * K) :=
    finSumFinEquiv.trans (finCongr (by
      simp [Nat.add_mul, Nat.add_comm]))
  (Equiv.piCongrLeft
      (fun _ : Fin ((r + 1) * K) ↦ ZMod 2) eFin).symm.trans
    (Equiv.sumArrowEquivProdArrow
      (Fin K) (Fin (r * K)) (ZMod 2))

/-- Arithmetic normalization from the simplified tail size `r*K` to the
tail size appearing literally in the active-prefix definition. -/
def headBlockTailCastEquiv (r K : ℕ) :
    PauliBinaryWord (r * K) ≃
      PauliBinaryWord (((r + 1) * K) - K) :=
  Equiv.piCongrLeft
    (fun _ : Fin (((r + 1) * K) - K) ↦ ZMod 2)
    (finCongr (by simp [Nat.add_mul]))

/-- After the harmless arithmetic tail cast, the explicit head-block split
is exactly the active-prefix split at `K` qubits. -/
theorem headBlockBinaryWordEquiv_trans_tailCast
    (r K : ℕ) :
    (headBlockBinaryWordEquiv r K).trans
        ((Equiv.refl (PauliBinaryWord K)).prodCongr
          (headBlockTailCastEquiv r K)) =
      binaryWordPrefixEquiv ((r + 1) * K) K (by
        simp [Nat.add_mul]) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · funext i
    apply congrArg x
    apply Fin.ext
    simp [headBlockBinaryWordEquiv, headBlockTailCastEquiv,
      binaryWordPrefixEquiv, finPrefixSumEquiv]
  · funext i
    apply congrArg x
    apply Fin.ext
    simp [headBlockBinaryWordEquiv, headBlockTailCastEquiv,
      binaryWordPrefixEquiv, finPrefixSumEquiv]

/-- The block-tensor complement coordinates and the literal first-block
prefix coordinates are the same physical split. -/
theorem singleBlockBinaryWordEquiv_zero_trans_tail
    (r K : ℕ) :
    (singleBlockBinaryWordEquiv (r + 1) K (0 : Fin (r + 1))).trans
        ((Equiv.refl (PauliBinaryWord K)).prodCongr
          (blockZeroComplementTailEquiv r K)) =
      headBlockBinaryWordEquiv r K := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · funext i
    apply congrArg x
    apply Fin.ext
    simp [singleBlockBinaryWordEquiv, blockZeroComplementTailEquiv,
      blockZeroComplementIndexEquiv, headBlockBinaryWordEquiv,
      binaryWordBlockEquiv, finProdFinEquiv]
  · funext i
    apply congrArg x
    apply Fin.ext
    simp [singleBlockBinaryWordEquiv, blockZeroComplementTailEquiv,
      blockZeroComplementIndexEquiv, headBlockBinaryWordEquiv,
      binaryWordBlockEquiv, finProdFinEquiv]
    change i.1 % K + K * (i.1 / K + 1) = K + i.1
    rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, Nat.mod_add_div,
      Nat.add_comm]

/-- Reindexing only the inactive factor of a tensor-identity unitary changes
only that factor's coordinate type. -/
theorem factorizationReindexUnitary_finiteUnitaryTensorId_inactive
    {I J J' : Type*} [Fintype I] [Fintype J] [Fintype J']
    [DecidableEq I] [DecidableEq J] [DecidableEq J']
    (e : J ≃ J') (U : Matrix.unitaryGroup I ℂ) :
    factorizationReindexUnitary
        ((Equiv.refl I).prodCongr e)
        (finiteUnitaryTensorId (J := J) U) =
      finiteUnitaryTensorId (J := J') U := by
  apply Subtype.ext
  ext x y
  rcases x with ⟨xi, xj⟩
  rcases y with ⟨yi, yj⟩
  change U.1 xi yi * (if e.symm xj = e.symm yj then 1 else 0) =
    U.1 xi yi * (if xj = yj then 1 else 0)
  simp

/-- After the literal first-block split, block zero is exactly the local
unitary tensored with identity on the consecutive tail. -/
theorem factorizationReindexUnitary_blockZero_head
    (r K : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    factorizationReindexUnitary (headBlockBinaryWordEquiv r K)
        (singleBlockEmbeddedUnitary (r + 1) K (0 : Fin (r + 1)) U) =
      finiteUnitaryTensorId (J := PauliBinaryWord (r * K)) U := by
  rw [← singleBlockBinaryWordEquiv_zero_trans_tail]
  rw [← factorizationReindexUnitary_trans]
  rw [factorizationReindexUnitary_singleBlockEmbeddedUnitary]
  exact factorizationReindexUnitary_finiteUnitaryTensorId_inactive
    (blockZeroComplementTailEquiv r K) U

/-- Two successive CP-map basis transports collapse to transport along the
composite equivalence.  This local version keeps the base geometry module
independent of the later nonclosing-step module. -/
private theorem reindexEquiv_trans_base
    {I J L : Type*}
    [Fintype I] [Fintype J] [Fintype L]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    (e : I ≃ J) (f : J ≃ L)
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CompletelyPositiveMap.reindexEquiv f
        (CompletelyPositiveMap.reindexEquiv e Phi) =
      CompletelyPositiveMap.reindexEquiv (e.trans f) Phi := by
  apply DFunLike.coe_injective
  funext X
  apply CStarMatrix.ext
  intro i j
  rfl

private theorem reindexEquiv_refl_base
    {I : Type*} [Fintype I] [DecidableEq I]
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CompletelyPositiveMap.reindexEquiv (Equiv.refl I) Phi = Phi := by
  apply DFunLike.coe_injective
  funext X
  rfl

private theorem reindexEquiv_symm_cancel_base
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CompletelyPositiveMap.reindexEquiv e.symm
        (CompletelyPositiveMap.reindexEquiv e Phi) = Phi := by
  rw [reindexEquiv_trans_base, Equiv.self_trans_symm,
    reindexEquiv_refl_base]

/-- Reindexing the untouched register of a finite tensor-identity twirl
changes only its coordinate type. -/
theorem finiteUnitaryThirdTwirlTensorIdCP_reindex_inactive_base
    {I J L E : Type*}
    [Fintype I] [Fintype J] [Fintype L] [Fintype E]
    [DecidableEq I] [DecidableEq J] [DecidableEq L]
    [Nonempty E]
    (e : J ≃ L) (U : E → Matrix.unitaryGroup I ℂ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr ((Equiv.refl I).prodCongr e))
        (finiteUnitaryThirdTwirlTensorIdCP (J := J) U) =
      finiteUnitaryThirdTwirlTensorIdCP (J := L) U := by
  unfold finiteUnitaryThirdTwirlTensorIdCP
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  exact factorizationReindexUnitary_finiteUnitaryTensorId_inactive e (U a)

/-- In the explicit head/tail coordinates, the block-zero finite Clifford
twirl is exactly Haar on the head block tensored with identity on the tail. -/
theorem finiteUnitaryThirdTwirlCP_blockZero_reindex_head
    (r K : ℕ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (headBlockBinaryWordEquiv r K))
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            singleBlockEmbeddedUnitary (r + 1) K (0 : Fin (r + 1))
              (pauliCosetCliffordUnitary K a))) =
      pauliHaarThirdTwirlTensorIdCP K (PauliBinaryWord (r * K)) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold pauliHaarThirdTwirlTensorIdCP
    finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  exact factorizationReindexUnitary_blockZero_head r K
    (pauliCosetCliffordUnitary K a)

/-- Canonical arithmetic cast from a one-block global binary word back to
the local `K`-qubit word. -/
def oneBlockBinaryWordEquiv (K : ℕ) :
    PauliBinaryWord (1 * K) ≃ PauliBinaryWord K :=
  Equiv.piCongrLeft (fun _ : Fin K ↦ ZMod 2)
    (finCongr (Nat.one_mul K))

/-- With only one block, reindexing the block-zero embedding by the
canonical arithmetic cast gives the original unitary. -/
theorem factorizationReindexUnitary_singleBlock_one_zero
    (K : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    factorizationReindexUnitary (oneBlockBinaryWordEquiv K)
        (singleBlockEmbeddedUnitary 1 K (0 : Fin 1) U) = U := by
  apply Subtype.ext
  ext x y
  change (∏ j : Fin 1,
      ((Pi.mulSingle (0 : Fin 1) U :
        Fin 1 → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) j).1
        (binaryWordBlockEquiv 1 K
          ((oneBlockBinaryWordEquiv K).symm x) j)
        (binaryWordBlockEquiv 1 K
          ((oneBlockBinaryWordEquiv K).symm y) j)) = U.1 x y
  simp [binaryWordBlockEquiv, oneBlockBinaryWordEquiv,
    finProdFinEquiv]

/-- The same arithmetic cast transports the concrete one-block Haar CP map
to the ordinary `K`-qubit representative. -/
theorem pauliHaarThirdTwirlCP_reindex_oneBlock
    (K : ℕ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (oneBlockBinaryWordEquiv K))
        (pauliHaarThirdTwirlCP (1 * K)) =
      pauliHaarThirdTwirlCP K := by
  let e := oneBlockBinaryWordEquiv K
  let idx := factorizationPauliBinaryWordEquivFin K
  let A := CompletelyPositiveMap.reindexEquiv
    (tripleIndexCongr e) (pauliHaarThirdTwirlCP (1 * K))
  let B := pauliHaarThirdTwirlCP K
  have hleft :
      (CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr idx) A).toLinearMap =
        unitaryHaarThirdTwirlLinearMap (2 ^ K) := by
    rw [reindexEquiv_trans_base]
    exact pauliHaarThirdTwirlCP_reindexEquiv_toLinearMap_eq_haar
      (1 * K) (2 ^ K) (e.trans idx) (by simp)
  have hright :
      (CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr idx) B).toLinearMap =
        unitaryHaarThirdTwirlLinearMap (2 ^ K) := by
    exact pauliHaarThirdTwirlCP_reindexEquiv_toLinearMap_eq_haar
      K (2 ^ K) idx rfl
  have hreindexed :
      CompletelyPositiveMap.reindexEquiv (tripleIndexCongr idx) A =
        CompletelyPositiveMap.reindexEquiv (tripleIndexCongr idx) B := by
    apply DFunLike.coe_injective
    funext X
    exact DFunLike.congr_fun (hleft.trans hright.symm) X
  change A = B
  calc
    A = CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr idx).symm
        (CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr idx) A) :=
      (reindexEquiv_symm_cancel_base (tripleIndexCongr idx) A).symm
    _ = CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr idx).symm
        (CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr idx) B) := by rw [hreindexed]
    _ = B := reindexEquiv_symm_cancel_base (tripleIndexCongr idx) B

/-- In the quotient-one case, the first block already has full support and
is exactly the full active Haar representative. -/
theorem finiteUnitaryThirdTwirlCP_blockZero_eq_activePrefix_one
    (K : ℕ) :
    finiteUnitaryThirdTwirlCP
        (fun a : PauliCosetCliffordEnsemble K ↦
          singleBlockEmbeddedUnitary 1 K (0 : Fin 1)
            (pauliCosetCliffordUnitary K a)) =
      pauliActivePrefixHaarCP (1 * K) K 0 := by
  let e := oneBlockBinaryWordEquiv K
  let Phi := finiteUnitaryThirdTwirlCP
    (fun a : PauliCosetCliffordEnsemble K ↦
      singleBlockEmbeddedUnitary 1 K (0 : Fin 1)
        (pauliCosetCliffordUnitary K a))
  have hPhi : CompletelyPositiveMap.reindexEquiv
      (tripleIndexCongr e) Phi = pauliHaarThirdTwirlCP K := by
    rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
    unfold pauliHaarThirdTwirlCP finitePauliCosetThirdTwirlCP
    congr 1
    funext a
    exact factorizationReindexUnitary_singleBlock_one_zero K
      (pauliCosetCliffordUnitary K a)
  have hfull : choKimActiveQubitCount (1 * K) K 0 = 1 * K := by
    simp [choKimActiveQubitCount]
  rw [pauliActivePrefixHaarCP_eq_full hfull]
  change Phi = pauliHaarThirdTwirlCP (1 * K)
  calc
    Phi = CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr e).symm
        (CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr e) Phi) :=
      (reindexEquiv_symm_cancel_base (tripleIndexCongr e) Phi).symm
    _ = CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr e).symm
        (CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr e) (pauliHaarThirdTwirlCP (1 * K))) := by
      rw [hPhi, pauliHaarThirdTwirlCP_reindex_oneBlock]
    _ = pauliHaarThirdTwirlCP (1 * K) :=
      reindexEquiv_symm_cancel_base (tripleIndexCongr e)
        (pauliHaarThirdTwirlCP (1 * K))

/-- When there is a nonempty tail, the canonical first block gate is exactly
the Haar reference on the initial active prefix. -/
theorem finiteUnitaryThirdTwirlCP_blockZero_eq_activePrefix_of_tail
    (r K : ℕ) (hr : 0 < r) (hK : 0 < K) :
    finiteUnitaryThirdTwirlCP
        (fun a : PauliCosetCliffordEnsemble K ↦
          singleBlockEmbeddedUnitary (r + 1) K (0 : Fin (r + 1))
            (pauliCosetCliffordUnitary K a)) =
      pauliActivePrefixHaarCP ((r + 1) * K) K 0 := by
  let N := (r + 1) * K
  let head := headBlockBinaryWordEquiv r K
  let tail := headBlockTailCastEquiv r K
  let activeSplit := binaryWordPrefixEquiv N K (by
    dsimp only [N]
    simp [Nat.add_mul])
  let Phi := finiteUnitaryThirdTwirlCP
    (fun a : PauliCosetCliffordEnsemble K ↦
      singleBlockEmbeddedUnitary (r + 1) K (0 : Fin (r + 1))
        (pauliCosetCliffordUnitary K a))
  have hcount : choKimActiveQubitCount N K 0 = K := by
    apply choKimActiveQubitCount_zero
    dsimp only [N]
    simp [Nat.add_mul]
  have hnotFull : choKimActiveQubitCount N K 0 ≠ N := by
    rw [hcount]
    dsimp only [N]
    have hrK : 0 < r * K := Nat.mul_pos hr hK
    simp only [Nat.add_mul, one_mul]
    omega
  have hactive : pauliActivePrefixHaarCP N K 0 =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr activeSplit.symm)
        (pauliHaarThirdTwirlTensorIdCP K
          (PauliBinaryWord (N - K))) := by
    have hKN : K ≤ N := by
      dsimp only [N]
      simp [Nat.add_mul]
    let qActive : {q : ℕ // q ≤ N} :=
      ⟨choKimActiveQubitCount N K 0,
        choKimActiveQubitCount_le N K 0⟩
    let qHead : {q : ℕ // q ≤ N} := ⟨K, hKN⟩
    have hq : qActive = qHead := by
      apply Subtype.ext
      exact hcount
    have htransport := congrArg
      (fun q : {q : ℕ // q ≤ N} ↦
        CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr (binaryWordPrefixEquiv N q.1 q.2).symm)
          (pauliHaarThirdTwirlTensorIdCP q.1
            (PauliBinaryWord (N - q.1)))) hq
    unfold pauliActivePrefixHaarCP
    rw [dif_neg hnotFull]
    unfold choKimActiveBinaryWordEquiv
    simpa [qActive, qHead, activeSplit] using htransport
  have hinactive :
      CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr
            ((Equiv.refl (PauliBinaryWord K)).prodCongr tail))
          (pauliHaarThirdTwirlTensorIdCP K
            (PauliBinaryWord (r * K))) =
        pauliHaarThirdTwirlTensorIdCP K
          (PauliBinaryWord (N - K)) := by
    dsimp only [tail, N]
    exact finiteUnitaryThirdTwirlTensorIdCP_reindex_inactive_base
      (headBlockTailCastEquiv r K) (pauliCosetCliffordUnitary K)
  have hsplit : head.trans
      ((Equiv.refl (PauliBinaryWord K)).prodCongr tail) = activeSplit := by
    dsimp only [head, tail, activeSplit, N]
    exact headBlockBinaryWordEquiv_trans_tailCast r K
  have hcomp :
      ((Equiv.refl (PauliBinaryWord K)).prodCongr tail).trans
          activeSplit.symm = head.symm := by
    apply Equiv.ext
    intro x
    change activeSplit.symm
      (((Equiv.refl (PauliBinaryWord K)).prodCongr tail) x) =
        head.symm x
    rw [← hsplit]
    rcases x with ⟨x₁, x₂⟩
    simp
  have hcomp3 :
      (tripleIndexCongr
          ((Equiv.refl (PauliBinaryWord K)).prodCongr tail)).trans
          (tripleIndexCongr activeSplit.symm) =
        tripleIndexCongr head.symm := by
    apply Equiv.ext
    intro x
    rcases x with ⟨x₁, x₂, x₃⟩
    change
      (((Equiv.refl (PauliBinaryWord K)).prodCongr tail).trans
          activeSplit.symm x₁,
        ((Equiv.refl (PauliBinaryWord K)).prodCongr tail).trans
          activeSplit.symm x₂,
        ((Equiv.refl (PauliBinaryWord K)).prodCongr tail).trans
          activeSplit.symm x₃) =
      (head.symm x₁, head.symm x₂, head.symm x₃)
    rw [hcomp]
  rw [hactive, ← hinactive, reindexEquiv_trans_base, hcomp3]
  rw [← finiteUnitaryThirdTwirlCP_blockZero_reindex_head r K]
  exact (reindexEquiv_symm_cancel_base
    (tripleIndexCongr head) Phi).symm

/-- For every nonempty block register, the first canonical block gate is
exactly the Haar reference on the active support after gate zero. -/
theorem finiteUnitaryThirdTwirlCP_blockZero_eq_activePrefix
    (m K : ℕ) (hm : 0 < m) (hK : 0 < K) :
    finiteUnitaryThirdTwirlCP
        (fun a : PauliCosetCliffordEnsemble K ↦
          singleBlockEmbeddedUnitary m K ⟨0, hm⟩
            (pauliCosetCliffordUnitary K a)) =
      pauliActivePrefixHaarCP (m * K) K 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  by_cases hr : r = 0
  · subst r
    simpa using finiteUnitaryThirdTwirlCP_blockZero_eq_activePrefix_one K
  · exact finiteUnitaryThirdTwirlCP_blockZero_eq_activePrefix_of_tail
      r K (Nat.pos_of_ne_zero hr) hK

/-- A literal unshifted gate is the single transport of its canonical
binary-word finite twirl. -/
theorem finiteUnitaryThirdTwirlCP_choKimBlockGate_eq_reindex_direct
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    finiteUnitaryThirdTwirlCP
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (choKimLiteralBinaryWordEquivFin hdiv))
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            singleBlockEmbeddedUnitary (n / K) K j
              (pauliCosetCliffordUnitary K a))) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  exact choKimEmbeddedBlockPauliCosetCliffordUnitaryFin_eq_direct
    hdiv j a

/-- The first literal gate is exactly the active-Haar reference at zero. -/
theorem ChoKimBlockCondition.choKimBlockZero_eq_activeHaar
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    finiteUnitaryThirdTwirlCP
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin h.block_dvd
          ⟨0, h.blockQuotient_pos hn⟩) =
      choKimActiveHaarCP h.block_dvd 0 := by
  rw [finiteUnitaryThirdTwirlCP_choKimBlockGate_eq_reindex_direct]
  unfold choKimActiveHaarCP
  rw [finiteUnitaryThirdTwirlCP_blockZero_eq_activePrefix
    (n / K) K (h.blockQuotient_pos hn) h.block_pos]

/-- Prefix zero of a nonempty alternating pair list is its first unshifted
gate. -/
theorem alternatingCPPrefix_zero_eq_first
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {m : ℕ} (hm : 0 < m) (U S : Fin m → A →CP A) :
    alternatingCPPrefix (alternatingCPGateList U S) 0 =
      U ⟨0, hm⟩ := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rw [alternatingCPGateList_succ]
  rfl

/-- The actual periodic reference family starts at the exact first-gate
Haar map, with no base approximation error. -/
theorem ChoKimBlockCondition.alternatingCPPrefix_zero_eq_activeHaar
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    alternatingCPPrefix
        (alternatingCPGateList
          (fun q ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin
              h.block_dvd q))
          (fun q ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
              h.block_dvd q))) 0 =
      choKimActiveHaarCP h.block_dvd 0 := by
  rw [alternatingCPPrefix_zero_eq_first (h.blockQuotient_pos hn)]
  exact h.choKimBlockZero_eq_activeHaar hn

/-! ## Closing shifted gate and exact full-Haar absorption -/

/-- Canonical binary-word unitary underlying one shifted literal gate. -/
def choKimCanonicalShiftedBlockUnitary
    (n K : ℕ) (j : Fin (n / K))
    (a : PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (PauliBinaryWord ((n / K) * K)) ℂ :=
  shiftedSingleBlockEmbeddedUnitary (n / K) K
    (cyclicQubitShift ((n / K) * K) (K / 2)) j
    (pauliCosetCliffordUnitary K a)

/-- A literal shifted gate is the single transport of its canonical
binary-word finite twirl. -/
theorem finiteUnitaryThirdTwirlCP_choKimShiftedGate_eq_reindex_direct
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    finiteUnitaryThirdTwirlCP
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (choKimLiteralBinaryWordEquivFin hdiv))
        (finiteUnitaryThirdTwirlCP
          (choKimCanonicalShiftedBlockUnitary n K j)) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  exact choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin_eq_direct
    hdiv j a

/-- Full Haar absorbs every shifted literal gate exactly. -/
theorem choKimFullHaarCP_comp_shiftedGate_eq_full
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    CompletelyPositiveMap.comp (choKimFullHaarCP hdiv)
        (finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j)) =
      choKimFullHaarCP hdiv := by
  rw [finiteUnitaryThirdTwirlCP_choKimShiftedGate_eq_reindex_direct]
  unfold choKimFullHaarCP
  rw [← CompletelyPositiveMap.reindexEquiv_comp]
  rw [pauliHaarThirdTwirlCP_comp_finiteUnitaryThirdTwirlCP]

/-- Last block coordinate of a nonempty block traversal. -/
def choKimLastBlockIndex (m : ℕ) (hm : 0 < m) : Fin m :=
  ⟨m - 1, by omega⟩

@[simp] theorem choKimLastBlockIndex_val (m : ℕ) (hm : 0 < m) :
    (choKimLastBlockIndex m hm).1 = m - 1 := rfl

/-- The last alternating selector is the closing shifted gate. -/
theorem alternatingCPGateAt_choKim_closing
    {n K : ℕ} (hdiv : K ∣ n) (hm : 0 < n / K) :
    alternatingCPGateAt
        (alternatingCPGateList
          (fun q ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv q))
          (fun q ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv q)))
        (2 * (n / K) - 1) =
      (false, finiteUnitaryThirdTwirlCP
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv
          (choKimLastBlockIndex (n / K) hm))) := by
  let j := choKimLastBlockIndex (n / K) hm
  rw [show 2 * (n / K) - 1 = 2 * j.1 + 1 by
    dsimp only [j, choKimLastBlockIndex]
    omega]
  exact alternatingCPGateAt_odd _ _ j

/-- The closing step has exact reference error zero, weakened to the common
Cho--Kim pairwise error used by the iteration. -/
theorem ChoKimBlockCondition.alternatingActiveHaar_closing_relativeCP
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    let gates := alternatingCPGateList
      (fun q ↦ finiteUnitaryThirdTwirlCP
        (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin h.block_dvd q))
      (fun q ↦ finiteUnitaryThirdTwirlCP
        (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
          h.block_dvd q))
    let closing := 2 * (n / K) - 1
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (if (alternatingCPGateAt gates closing).1 then
        CompletelyPositiveMap.comp
          (alternatingCPGateAt gates closing).2
          (choKimActiveHaarCP h.block_dvd (2 * (n / K) - 2))
       else CompletelyPositiveMap.comp
          (choKimActiveHaarCP h.block_dvd (2 * (n / K) - 2))
          (alternatingCPGateAt gates closing).2).toLinearMap
      (choKimActiveHaarCP h.block_dvd closing).toLinearMap := by
  dsimp only
  have hm := h.blockQuotient_pos hn
  rw [alternatingCPGateAt_choKim_closing h.block_dvd hm]
  simp only [Bool.false_eq_true, if_false]
  rw [choKimActiveHaarCP_penultimate_eq_full h hn,
    choKimActiveHaarCP_closing_eq_full h hn,
    choKimFullHaarCP_comp_shiftedGate_eq_full]
  exact (relativeCPApproximation_zero_refl
    (choKimFullHaarCP h.block_dvd)).mono_error
      (choKimFThree_nonneg (h.eighteen_le_overlap hn))

end

end TomographyOracleCore
