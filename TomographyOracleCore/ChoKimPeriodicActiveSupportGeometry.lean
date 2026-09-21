import TomographyOracleCore.ChoKimPeriodicAlternatingCPPrefix
import TomographyOracleCore.SingleBlockThirdTwirlReindex
import TomographyOracleCore.ChoKimOverlapCycle

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance choKimSupportSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimSupportStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Active-support geometry of the periodic Cho--Kim traversal

All support claims are made first in the canonical binary-word basis on
`m*K` labelled qubits.  Only after those claims are fixed do we transport the
maps once to the literal `Fin (2^n)` basis.  Thus no cardinality-only
equivalence is used to infer physical support.

The alternating gate order is `A₀,S₀,A₁,S₁,…`.  Starting with `A₀`,
the traversal grows a consecutive active interval by `K/2` at every gate
until `A_(m-1)` has covered the whole register.  The last shifted gate
`S_(m-1)` closes the periodic cycle and adds no qubits.
-/

/-! ## Exact selectors in the alternating list -/

theorem alternatingCPGateList_succ
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {m : ℕ} (U S : Fin (m + 1) → A →CP A) :
    alternatingCPGateList U S =
      [(true, U 0), (false, S 0)] ++
        alternatingCPGateList (fun j ↦ U j.succ) (fun j ↦ S j.succ) := by
  unfold alternatingCPGateList
  rw [List.ofFn_succ, List.flatMap_cons]

/-- Dropping the two tags belonging to the head pair commutes with total
list lookup. -/
theorem List.getD_cons_cons_add_two
    {X : Type*} (x y d : X) (l : List X) (i : ℕ) :
    (x :: y :: l).getD (i + 2) d = l.getD i d := by
  induction i <;> rfl

/-- The same drop-two identity in the literal pair-list form produced by the
alternating `flatMap`. -/
theorem List.getD_pair_append_add_two
    {X : Type*} (x y d : X) (l : List X) (i : ℕ) :
    ([x, y] ++ l).getD (i + 2) d = l.getD i d := by
  exact List.getD_cons_cons_add_two x y d l i

theorem alternatingCPGateAt_even
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {m : ℕ} (U S : Fin m → A →CP A) (j : Fin m) :
    alternatingCPGateAt (alternatingCPGateList U S) (2 * j.1) =
      (true, U j) := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · rw [alternatingCPGateList_succ]
        simp [alternatingCPGateAt]
      · rw [alternatingCPGateList_succ]
        unfold alternatingCPGateAt
        rw [show 2 * (j.succ : Fin (m + 1)).1 = 2 * j.1 + 2 by
          change 2 * (j.1 + 1) = 2 * j.1 + 2
          omega]
        rw [List.getD_pair_append_add_two]
        simpa [alternatingCPGateAt] using
          ih (fun q ↦ U q.succ) (fun q ↦ S q.succ) j

theorem alternatingCPGateAt_odd
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {m : ℕ} (U S : Fin m → A →CP A) (j : Fin m) :
    alternatingCPGateAt (alternatingCPGateList U S) (2 * j.1 + 1) =
      (false, S j) := by
  induction m with
  | zero => exact Fin.elim0 j
  | succ m ih =>
      refine Fin.cases ?_ (fun j ↦ ?_) j
      · rw [alternatingCPGateList_succ]
        simp [alternatingCPGateAt]
      · rw [alternatingCPGateList_succ]
        unfold alternatingCPGateAt
        rw [show 2 * (j.succ : Fin (m + 1)).1 + 1 =
            (2 * j.1 + 1) + 2 by
          change 2 * (j.1 + 1) + 1 = (2 * j.1 + 1) + 2
          omega]
        rw [List.getD_pair_append_add_two]
        simpa [alternatingCPGateAt] using
          ih (fun q ↦ U q.succ) (fun q ↦ S q.succ) j

/-! ## Active qubit count and support-compatible prefix split -/

/-- Number of active qubits after the gate at zero-based index `i`. -/
def choKimActiveQubitCount (N K i : ℕ) : ℕ :=
  min N (K + i * (K / 2))

theorem choKimActiveQubitCount_le (N K i : ℕ) :
    choKimActiveQubitCount N K i ≤ N :=
  min_le_left _ _

theorem choKimActiveQubitCount_zero
    {N K : ℕ} (hK : K ≤ N) :
    choKimActiveQubitCount N K 0 = K := by
  simp [choKimActiveQubitCount, min_eq_right hK]

theorem ChoKimBlockCondition.activeQubitCount_zero_eq_block
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimActiveQubitCount ((n / K) * K) K 0 = K := by
  rw [Nat.div_mul_cancel h.block_dvd]
  exact choKimActiveQubitCount_zero (h.block_le_qubits hn)

theorem choKimActiveQubitCount_mono (N K : ℕ) :
    Monotone (choKimActiveQubitCount N K) := by
  intro i j hij
  unfold choKimActiveQubitCount
  exact min_le_min_left N (Nat.add_le_add_left
    (Nat.mul_le_mul_right (K / 2) hij) K)

/-- `A_(m-1)` already makes the active support global. -/
theorem choKimActiveQubitCount_penultimate
    {m K : ℕ} (hm : 0 < m) (hK : Even K) :
    choKimActiveQubitCount (m * K) K (2 * m - 2) = m * K := by
  obtain ⟨k, hk⟩ := hK
  subst K
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  subst m
  unfold choKimActiveQubitCount
  have hhalf : (k + k) / 2 = k := by omega
  have hindex : 2 * (r + 1) - 2 = 2 * r := by omega
  rw [hhalf, hindex]
  apply min_eq_left
  apply le_of_eq
  calc
    (r + 1) * (k + k) = r * k + r * k + (k + k) := by
      simp only [Nat.add_mul, Nat.mul_add, one_mul]
      ac_rfl
    _ = (k + k) + (2 * r) * k := by
      rw [two_mul, Nat.add_mul]
      ac_rfl

/-- The last shifted gate is the closing edge and adds no new qubits. -/
theorem choKimActiveQubitCount_closing
    {m K : ℕ} (hm : 0 < m) (hK : Even K) :
    choKimActiveQubitCount (m * K) K (2 * m - 1) = m * K := by
  apply le_antisymm (choKimActiveQubitCount_le _ _ _)
  calc
    m * K = choKimActiveQubitCount (m * K) K (2 * m - 2) :=
      (choKimActiveQubitCount_penultimate hm hK).symm
    _ ≤ choKimActiveQubitCount (m * K) K (2 * m - 1) :=
      choKimActiveQubitCount_mono _ _ (by omega)

theorem ChoKimBlockCondition.activeQubitCount_penultimate_eq_n
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimActiveQubitCount ((n / K) * K) K (2 * (n / K) - 2) = n := by
  rw [choKimActiveQubitCount_penultimate (h.blockQuotient_pos hn)
    h.block_even, Nat.div_mul_cancel h.block_dvd]

theorem ChoKimBlockCondition.activeQubitCount_closing_eq_n
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimActiveQubitCount ((n / K) * K) K (2 * (n / K) - 1) = n := by
  rw [choKimActiveQubitCount_closing (h.blockQuotient_pos hn)
    h.block_even, Nat.div_mul_cancel h.block_dvd]

/-- The canonical equivalence between a prefix/tail sum of qubit coordinates
and the complete register. -/
def finPrefixSumEquiv (N q : ℕ) (hq : q ≤ N) :
    Fin q ⊕ Fin (N - q) ≃ Fin N :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hq))

/-- Split a binary word into its first `q` qubits and its untouched tail. -/
def binaryWordPrefixEquiv (N q : ℕ) (hq : q ≤ N) :
    PauliBinaryWord N ≃ PauliBinaryWord q × PauliBinaryWord (N - q) :=
  (Equiv.piCongrLeft (fun _ : Fin N ↦ ZMod 2)
      (finPrefixSumEquiv N q hq)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin q) (Fin (N - q)) (ZMod 2))

/-- Support-compatible active/tail split after gate `i`. -/
def choKimActiveBinaryWordEquiv (N K i : ℕ) :
    PauliBinaryWord N ≃
      PauliBinaryWord (choKimActiveQubitCount N K i) ×
        PauliBinaryWord (N - choKimActiveQubitCount N K i) :=
  binaryWordPrefixEquiv N (choKimActiveQubitCount N K i)
    (choKimActiveQubitCount_le N K i)

/-! ## One exact local Haar gate, transported to the literal basis -/

/-- Direct, single transport from the canonical binary-word basis to the
literal Cho--Kim `Fin` basis. -/
theorem choKimEmbeddedBlockPauliCosetCliffordUnitaryFin_eq_direct
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K))
    (a : PauliCosetCliffordEnsemble K) :
    choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j a =
      factorizationReindexUnitary (choKimLiteralBinaryWordEquivFin hdiv)
        (singleBlockEmbeddedUnitary (n / K) K j
          (pauliCosetCliffordUnitary K a)) := by
  let e := factorizationPauliBinaryWordEquivFin ((n / K) * K)
  let l := choKimLiteralBinaryWordEquivFin hdiv
  have hel : e.trans (e.symm.trans l) = l := by
    ext x
    simp
  unfold choKimEmbeddedBlockPauliCosetCliffordUnitaryFin
    embeddedBlockPauliCosetCliffordUnitaryFin
    blockTensorUnitaryFinMonoidHom
    singleBlockEmbeddedUnitary
  change factorizationReindexUnitary (e.symm.trans l)
      (factorizationReindexUnitary e _) = _
  rw [factorizationReindexUnitary_trans, hel]

theorem choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin_eq_direct
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K))
    (a : PauliCosetCliffordEnsemble K) :
    choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j a =
      factorizationReindexUnitary (choKimLiteralBinaryWordEquivFin hdiv)
        (shiftedSingleBlockEmbeddedUnitary (n / K) K
          (cyclicQubitShift ((n / K) * K) (K / 2)) j
          (pauliCosetCliffordUnitary K a)) := by
  let e := factorizationPauliBinaryWordEquivFin ((n / K) * K)
  let l := choKimLiteralBinaryWordEquivFin hdiv
  have hel : e.trans (e.symm.trans l) = l := by
    ext x
    simp
  unfold choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
    embeddedShiftedBlockPauliCosetCliffordUnitaryFin
    shiftedBlockTensorUnitaryFinMonoidHom
    shiftedSingleBlockEmbeddedUnitary
  change factorizationReindexUnitary (e.symm.trans l)
      (factorizationReindexUnitary e _) = _
  rw [factorizationReindexUnitary_trans, hel]
  apply congrArg (factorizationReindexUnitary l)
  simp only [MonoidHom.comp_apply, singleBlockEmbeddedUnitary]
  change (MulAut.conj (binaryWordPermutationUnitary
      (cyclicQubitShift ((n / K) * K) (K / 2)))) _ = _
  rw [MulAut.conj_apply]

/-- Literal-basis support split for one unshifted gate. -/
def choKimBlockGateSplitEquiv
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    Fin (2 ^ n) ≃
      PauliBinaryWord K ×
        ({i : Fin (n / K) // i ≠ j} → PauliBinaryWord K) :=
  (choKimLiteralBinaryWordEquivFin hdiv).symm.trans
    (singleBlockBinaryWordEquiv (n / K) K j)

/-- Literal-basis support split for one shifted gate. -/
def choKimShiftedBlockGateSplitEquiv
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    Fin (2 ^ n) ≃
      PauliBinaryWord K ×
        ({i : Fin (n / K) // i ≠ j} → PauliBinaryWord K) :=
  (choKimLiteralBinaryWordEquivFin hdiv).symm.trans
    (shiftedSingleBlockBinaryWordEquiv (n / K) K
      (cyclicQubitShift ((n / K) * K) (K / 2)) j)

/-- Every literal unshifted gate is exactly local Haar on its `K`-qubit
support tensored with identity on the complementary block coordinates. -/
theorem finiteUnitaryThirdTwirlCP_choKimBlockGate_reindex_eq_localHaar
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (choKimBlockGateSplitEquiv hdiv j))
        (finiteUnitaryThirdTwirlCP
          (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j)) =
      pauliHaarThirdTwirlTensorIdCP K
        ({i : Fin (n / K) // i ≠ j} → PauliBinaryWord K) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold pauliHaarThirdTwirlTensorIdCP
    finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  rw [choKimEmbeddedBlockPauliCosetCliffordUnitaryFin_eq_direct]
  rw [factorizationReindexUnitary_trans]
  have htrans : (choKimLiteralBinaryWordEquivFin hdiv).trans
      (choKimBlockGateSplitEquiv hdiv j) =
        singleBlockBinaryWordEquiv (n / K) K j := by
    apply Equiv.ext
    intro x
    change singleBlockBinaryWordEquiv (n / K) K j
        ((choKimLiteralBinaryWordEquivFin hdiv).symm
          (choKimLiteralBinaryWordEquivFin hdiv x)) = _
    rw [Equiv.symm_apply_apply]
  rw [htrans]
  exact factorizationReindexUnitary_singleBlockEmbeddedUnitary
    (n / K) K j (pauliCosetCliffordUnitary K a)

/-- Every literal shifted gate is exactly local Haar on its shifted `K`-qubit
support tensored with identity on the complement. -/
theorem finiteUnitaryThirdTwirlCP_choKimShiftedBlockGate_reindex_eq_localHaar
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (choKimShiftedBlockGateSplitEquiv hdiv j))
        (finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j)) =
      pauliHaarThirdTwirlTensorIdCP K
        ({i : Fin (n / K) // i ≠ j} → PauliBinaryWord K) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold pauliHaarThirdTwirlTensorIdCP
    finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  rw [choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin_eq_direct]
  rw [factorizationReindexUnitary_trans]
  have htrans : (choKimLiteralBinaryWordEquivFin hdiv).trans
      (choKimShiftedBlockGateSplitEquiv hdiv j) =
        shiftedSingleBlockBinaryWordEquiv (n / K) K
          (cyclicQubitShift ((n / K) * K) (K / 2)) j := by
    apply Equiv.ext
    intro x
    change shiftedSingleBlockBinaryWordEquiv (n / K) K
        (cyclicQubitShift ((n / K) * K) (K / 2)) j
        ((choKimLiteralBinaryWordEquivFin hdiv).symm
          (choKimLiteralBinaryWordEquivFin hdiv x)) = _
    rw [Equiv.symm_apply_apply]
  rw [htrans]
  exact factorizationReindexUnitary_shiftedSingleBlockEmbeddedUnitary
    (n / K) K (cyclicQubitShift ((n / K) * K) (K / 2)) j
      (pauliCosetCliffordUnitary K a)

/-- Even positions in the literal alternating list are exactly the
unshifted local-Haar gates above. -/
theorem alternatingCPGateAt_choKim_even_reindex_eq_localHaar
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (choKimBlockGateSplitEquiv hdiv j))
        (alternatingCPGateAt
          (alternatingCPGateList
            (fun q ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv q))
            (fun q ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv q)))
          (2 * j.1)).2 =
      pauliHaarThirdTwirlTensorIdCP K
        ({i : Fin (n / K) // i ≠ j} → PauliBinaryWord K) := by
  rw [show (alternatingCPGateAt
      (alternatingCPGateList
        (fun q ↦ finiteUnitaryThirdTwirlCP
          (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv q))
        (fun q ↦ finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv q)))
      (2 * j.1)).2 =
        finiteUnitaryThirdTwirlCP
          (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j) by
    exact congrArg Prod.snd (alternatingCPGateAt_even _ _ j)]
  exact finiteUnitaryThirdTwirlCP_choKimBlockGate_reindex_eq_localHaar
    hdiv j

/-- Odd positions in the literal alternating list are exactly the shifted
local-Haar gates above, including the closing gate `S_(m-1)`. -/
theorem alternatingCPGateAt_choKim_odd_reindex_eq_localHaar
    {n K : ℕ} (hdiv : K ∣ n) (j : Fin (n / K)) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (choKimShiftedBlockGateSplitEquiv hdiv j))
        (alternatingCPGateAt
          (alternatingCPGateList
            (fun q ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv q))
            (fun q ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv q)))
          (2 * j.1 + 1)).2 =
      pauliHaarThirdTwirlTensorIdCP K
        ({i : Fin (n / K) // i ≠ j} → PauliBinaryWord K) := by
  rw [show (alternatingCPGateAt
      (alternatingCPGateList
        (fun q ↦ finiteUnitaryThirdTwirlCP
          (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv q))
        (fun q ↦ finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv q)))
      (2 * j.1 + 1)).2 =
        finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j) by
    exact congrArg Prod.snd (alternatingCPGateAt_odd _ _ j)]
  exact finiteUnitaryThirdTwirlCP_choKimShiftedBlockGate_reindex_eq_localHaar
    hdiv j

/-! ## Active Haar reference family and its full-support endpoint -/

/-- Haar on the active prefix, tensored with identity on the untouched tail,
as a CP map in the original canonical binary-word basis.  At full support we
choose the definitionally standard full-system representative. -/
def pauliActivePrefixHaarCP (N K i : ℕ) :
    CStarMatrix (TripleIndex (PauliBinaryWord N))
        (TripleIndex (PauliBinaryWord N)) ℂ →CP
      CStarMatrix (TripleIndex (PauliBinaryWord N))
        (TripleIndex (PauliBinaryWord N)) ℂ :=
  if _hfull : choKimActiveQubitCount N K i = N then
    pauliHaarThirdTwirlCP N
  else
    CompletelyPositiveMap.reindexEquiv
      (tripleIndexCongr (choKimActiveBinaryWordEquiv N K i).symm)
      (pauliHaarThirdTwirlTensorIdCP (choKimActiveQubitCount N K i)
        (PauliBinaryWord (N - choKimActiveQubitCount N K i)))

theorem pauliActivePrefixHaarCP_eq_full
    {N K i : ℕ} (hfull : choKimActiveQubitCount N K i = N) :
    pauliActivePrefixHaarCP N K i = pauliHaarThirdTwirlCP N := by
  simp [pauliActivePrefixHaarCP, hfull]

/-- Standard full-system Haar CP representative in the literal Cho--Kim
basis. -/
def choKimFullHaarCP {n K : ℕ} (hdiv : K ∣ n) :
    CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ →CP
      CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ :=
  CompletelyPositiveMap.reindexEquiv
    (tripleIndexCongr (choKimLiteralBinaryWordEquivFin hdiv))
    (pauliHaarThirdTwirlCP ((n / K) * K))

/-- Active-prefix Haar reference, transported once to the literal circuit
basis. -/
def choKimActiveHaarCP {n K : ℕ} (hdiv : K ∣ n) (i : ℕ) :
    CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ →CP
      CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ :=
  CompletelyPositiveMap.reindexEquiv
    (tripleIndexCongr (choKimLiteralBinaryWordEquivFin hdiv))
    (pauliActivePrefixHaarCP ((n / K) * K) K i)

/-- At the penultimate gate the reference is already the standard global
Haar map; the closing shifted gate leaves this reference unchanged. -/
theorem choKimActiveHaarCP_penultimate_eq_full
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimActiveHaarCP h.block_dvd (2 * (n / K) - 2) =
      choKimFullHaarCP h.block_dvd := by
  unfold choKimActiveHaarCP choKimFullHaarCP
  rw [pauliActivePrefixHaarCP_eq_full
    (choKimActiveQubitCount_penultimate (h.blockQuotient_pos hn) h.block_even)]

theorem choKimActiveHaarCP_closing_eq_full
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimActiveHaarCP h.block_dvd (2 * (n / K) - 1) =
      choKimFullHaarCP h.block_dvd := by
  unfold choKimActiveHaarCP choKimFullHaarCP
  rw [pauliActivePrefixHaarCP_eq_full
    (choKimActiveQubitCount_closing (h.blockQuotient_pos hn) h.block_even)]

end

end TomographyOracleCore
