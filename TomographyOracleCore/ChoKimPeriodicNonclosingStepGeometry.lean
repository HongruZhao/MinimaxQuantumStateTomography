import TomographyOracleCore.ChoKimPeriodicCPGateList
import TomographyOracleCore.ChoKimPeriodicActiveSupportGeometry
import TomographyOracleCore.ChoKimPeriodicBaseClosingGeometry
import TomographyOracleCore.FiniteChoiTensorIdThirdTwirlReindex
import TomographyOracleCore.PauliHaarThirdTwirlEmptyInactive
import TomographyOracleCore.RelativeDesignConcretePairwiseActualHaarInactive
import TomographyOracleCore.RelativeDesignReferenceTransport
import Mathlib.Logic.Equiv.Fin.Rotate

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance choKimNonclosingSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimNonclosingStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

theorem tripleIndexCongr_symm_eq
    {I J : Type*} (e : I ≃ J) :
    (tripleIndexCongr e).symm = tripleIndexCongr e.symm := by
  apply Equiv.ext
  rintro ⟨x₀, x₁, x₂⟩
  rfl

/-!
# Exact geometry of one non-closing Cho--Kim gluing step

The proof is carried out in the canonical binary-word coordinates before the
single transport to `Fin (2^n)`.  If `h = K/2`, then after gate `i` the active
interval is

`[0, K + i*h)`.

For `i < 2*(n/K)-2`, the next gate meets that interval in exactly its last
`h` qubits and contributes exactly `h` new qubits.  The four physical pieces
are therefore

* the old-only interval;
* the `h`-qubit overlap;
* the `h`-qubit new-only interval;
* the untouched tail.

Every equivalence below is assembled from `Fin` sums, products, and the
literal cyclic qubit shift.  No equivalence is selected merely from a
cardinality equality.
-/

/-! ## Coordinate-preserving binary-word splits -/

/-- Split a binary word of length `a+b` at the literal coordinate `a`. -/
def pauliBinaryWordAddEquiv (a b : ℕ) :
    PauliBinaryWord (a + b) ≃
      PauliBinaryWord a × PauliBinaryWord b :=
  (Equiv.piCongrLeft (fun _ : Fin (a + b) ↦ ZMod 2)
      (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b))).symm.trans
  (Equiv.sumArrowEquivProdArrow (Fin a) (Fin b) (ZMod 2))

/-- Concatenate two literal consecutive binary words. -/
def pauliBinaryWordConcatEquiv (a b : ℕ) :
    PauliBinaryWord a × PauliBinaryWord b ≃
      PauliBinaryWord (a + b) :=
  (pauliBinaryWordAddEquiv a b).symm

@[simp] theorem pauliBinaryWordConcatEquiv_apply_castAdd
    (a b : ℕ) (u : PauliBinaryWord a) (v : PauliBinaryWord b)
    (p : Fin a) :
    pauliBinaryWordConcatEquiv a b (u, v) (Fin.castAdd b p) = u p := by
  change
    (pauliBinaryWordAddEquiv a b
      ((pauliBinaryWordAddEquiv a b).symm (u, v))).1 p = u p
  exact congrArg (fun z => z.1 p)
    ((pauliBinaryWordAddEquiv a b).apply_symm_apply (u, v))

@[simp] theorem pauliBinaryWordConcatEquiv_apply_natAdd
    (a b : ℕ) (u : PauliBinaryWord a) (v : PauliBinaryWord b)
    (p : Fin b) :
    pauliBinaryWordConcatEquiv a b (u, v) (Fin.natAdd a p) = v p := by
  change
    (pauliBinaryWordAddEquiv a b
      ((pauliBinaryWordAddEquiv a b).symm (u, v))).2 p = v p
  exact congrArg (fun z => z.2 p)
    ((pauliBinaryWordAddEquiv a b).apply_symm_apply (u, v))

@[simp] theorem pauliBinaryWordAddEquiv_fst_apply
    (a b : ℕ) (x : PauliBinaryWord (a + b)) (p : Fin a) :
    (pauliBinaryWordAddEquiv a b x).1 p = x (Fin.castAdd b p) := rfl

@[simp] theorem pauliBinaryWordAddEquiv_snd_apply
    (a b : ℕ) (x : PauliBinaryWord (a + b)) (p : Fin b) :
    (pauliBinaryWordAddEquiv a b x).2 p = x (Fin.natAdd a p) := rfl

@[simp] theorem binaryWordPrefixEquiv_fst_apply
    (N q : ℕ) (hq : q ≤ N) (x : PauliBinaryWord N) (p : Fin q) :
    (binaryWordPrefixEquiv N q hq x).1 p =
      x (Fin.cast (Nat.add_sub_of_le hq) (Fin.castAdd (N - q) p)) := by
  rfl

@[simp] theorem binaryWordPrefixEquiv_snd_apply
    (N q : ℕ) (hq : q ≤ N) (x : PauliBinaryWord N)
    (p : Fin (N - q)) :
    (binaryWordPrefixEquiv N q hq x).2 p =
      x (Fin.cast (Nat.add_sub_of_le hq) (Fin.natAdd q p)) := by
  rfl

/-- Transport binary words only along an equality of coordinate lengths. -/
def pauliBinaryWordCongr {a b : ℕ} (h : a = b) :
    PauliBinaryWord a ≃ PauliBinaryWord b := by
  subst b
  exact Equiv.refl _

@[simp] theorem pauliBinaryWordCongr_apply
    {a b : ℕ} (h : a = b) (x : PauliBinaryWord a) (p : Fin b) :
    pauliBinaryWordCongr h x p = x (Fin.cast h.symm p) := by
  subst b
  rfl

/-- Split three consecutive physical intervals without changing their order. -/
def pauliBinaryWordThreeEquiv (a b c : ℕ) :
    PauliBinaryWord ((a + b) + c) ≃
      (PauliBinaryWord a × PauliBinaryWord b) ×
        PauliBinaryWord c :=
  (pauliBinaryWordAddEquiv (a + b) c).trans
    ((pauliBinaryWordAddEquiv a b).prodCongr
      (Equiv.refl (PauliBinaryWord c)))

@[simp] theorem pauliBinaryWordThreeEquiv_fst_fst_apply
    (a b c : ℕ) (x : PauliBinaryWord ((a + b) + c)) (p : Fin a) :
    (pauliBinaryWordThreeEquiv a b c x).1.1 p =
      x (Fin.castAdd c (Fin.castAdd b p)) := by
  rfl

@[simp] theorem pauliBinaryWordThreeEquiv_fst_snd_apply
    (a b c : ℕ) (x : PauliBinaryWord ((a + b) + c)) (p : Fin b) :
    (pauliBinaryWordThreeEquiv a b c x).1.2 p =
      x (Fin.castAdd c (Fin.natAdd a p)) := by
  rfl

@[simp] theorem pauliBinaryWordThreeEquiv_snd_apply
    (a b c : ℕ) (x : PauliBinaryWord ((a + b) + c)) (p : Fin c) :
    (pauliBinaryWordThreeEquiv a b c x).2 p =
      x (Fin.natAdd (a + b) p) := by
  rfl

/-- Reorder `(prefix,middle,tail)` so that the acted-on middle interval is
the first tensor factor. -/
def middleIntervalReassocEquiv (A B R : Type*) :
    ((A × B) × R) ≃ B × (A × R) where
  toFun x := (x.1.2, x.1.1, x.2)
  invFun x := ((x.2.1, x.1), x.2.2)
  left_inv x := rfl
  right_inv x := rfl

/-- Extract a literal middle interval of length `k`, retaining its prefix and
tail as the untouched tensor factor. -/
def pauliBinaryWordMiddleEquiv (a k r : ℕ) :
    PauliBinaryWord ((a + k) + r) ≃
      PauliBinaryWord k ×
        (PauliBinaryWord a × PauliBinaryWord r) :=
  (pauliBinaryWordThreeEquiv a k r).trans
    (middleIntervalReassocEquiv
      (PauliBinaryWord a) (PauliBinaryWord k) (PauliBinaryWord r))

/-- Middle-interval split after rewriting the total length by an exact
arithmetic equality. -/
def pauliBinaryWordMiddleEquivOfEq
    {N : ℕ} (a k r : ℕ) (hN : (a + k) + r = N) :
    PauliBinaryWord N ≃
      PauliBinaryWord k ×
        (PauliBinaryWord a × PauliBinaryWord r) :=
  (pauliBinaryWordCongr hN.symm).trans
    (pauliBinaryWordMiddleEquiv a k r)

@[simp] theorem pauliBinaryWordMiddleEquivOfEq_fst_apply
    {N a k r : ℕ} (hN : (a + k) + r = N)
    (x : PauliBinaryWord N) (p : Fin k) :
    (pauliBinaryWordMiddleEquivOfEq a k r hN x).1 p =
      x (Fin.cast hN (Fin.castAdd r (Fin.natAdd a p))) := by
  subst N
  rfl

@[simp] theorem pauliBinaryWordMiddleEquivOfEq_prefix_apply
    {N a k r : ℕ} (hN : (a + k) + r = N)
    (x : PauliBinaryWord N) (p : Fin a) :
    (pauliBinaryWordMiddleEquivOfEq a k r hN x).2.1 p =
      x (Fin.cast hN (Fin.castAdd r (Fin.castAdd k p))) := by
  subst N
  rfl

@[simp] theorem pauliBinaryWordMiddleEquivOfEq_tail_apply
    {N a k r : ℕ} (hN : (a + k) + r = N)
    (x : PauliBinaryWord N) (p : Fin r) :
    (pauliBinaryWordMiddleEquivOfEq a k r hN x).2.2 p =
      x (Fin.cast hN (Fin.natAdd (a + k) p)) := by
  subst N
  rfl

/-- Split four consecutive intervals in the manuscript order `A,B,C,R`. -/
def pauliBinaryWordABCREquiv (a b c r : ℕ) :
    PauliBinaryWord (((a + b) + c) + r) ≃
      ((PauliBinaryWord a × PauliBinaryWord b) ×
        PauliBinaryWord c) × PauliBinaryWord r :=
  (pauliBinaryWordAddEquiv ((a + b) + c) r).trans <|
    (pauliBinaryWordThreeEquiv a b c).prodCongr
      (Equiv.refl (PauliBinaryWord r))

/-- Reverse only the three active subsystem labels.  This is the orientation
needed when the next gate is composed on the left. -/
def reverseABCReassocEquiv (A B C R : Type*) :
    ((C × B) × A) × R ≃ ((A × B) × C) × R where
  toFun x := (((x.1.2, x.1.1.2), x.1.1.1), x.2)
  invFun x := (((x.1.2, x.1.1.2), x.1.1.1), x.2)
  left_inv x := rfl
  right_inv x := rfl

/-- The active-only part of `reverseABCReassocEquiv`. -/
def reverseABCOneReplicaEquiv (A B C : Type*) :
    ((C × B) × A) ≃ ((A × B) × C) where
  toFun x := ((x.2, x.1.2), x.1.1)
  invFun x := ((x.2, x.1.2), x.1.1)
  left_inv x := rfl
  right_inv x := rfl

/-- One-replica version of the `B,C,A → A,B,C` register reorder. -/
def bcaOneReplicaEquivABC (A B C : Type*) :
    ((B × C) × A) ≃ ((A × B) × C) where
  toFun x := ((x.2, x.1.1), x.1.2)
  invFun x := ((x.1.2, x.2), x.1.1)
  left_inv x := rfl
  right_inv x := rfl

theorem tripleIndexCongr_bcaOneReplica_trans_ABC
    (A B C : Type*) :
    (tripleIndexCongr (bcaOneReplicaEquivABC A B C)).trans
        (tripleIndexABCEquiv A B C) =
      tripleIndexBCAEquivABC A B C := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x₀, x₁, x₂⟩
  rfl

/-! ## Cyclic shift on literal coordinates -/

/-- On a nonempty register, the project cyclic shift is addition in `Fin`. -/
theorem cyclicQubitShift_eq_finCycle
    {N s : ℕ} (hN : 0 < N) (hs : s < N) :
    cyclicQubitShift N s = finCycle ⟨s, hs⟩ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
  rw [cyclicQubitShift, Fin.cycleRange_last]
  apply Equiv.ext
  intro x
  change ((finRotate (N + 1)) ^ s) x = finCycle ⟨s, hs⟩ x
  rw [Equiv.Perm.coe_pow]
  exact congrFun (finCycle_eq_finRotate_iterate (k := ⟨s, hs⟩)).symm x

/-- Value-level form of the cyclic shift when the addition does not wrap. -/
theorem cyclicQubitShift_val_of_add_lt
    {N s : ℕ} (hN : 0 < N) (hs : s < N)
    (p : Fin N) (hadd : p.1 + s < N) :
    (cyclicQubitShift N s p).1 = p.1 + s := by
  rw [cyclicQubitShift_eq_finCycle hN hs]
  change ((p + ⟨s, hs⟩ : Fin N) : ℕ) = p.1 + s
  simp [Fin.add_def, Nat.mod_eq_of_lt hadd]

/-- Value-level form of the cyclic shift without imposing a no-wrap
hypothesis.  This is used exactly once, on the final half-block of the old
tail, where the shift wraps onto the first half-block of the register. -/
theorem cyclicQubitShift_val
    {N s : ℕ} (hN : 0 < N) (hs : s < N) (p : Fin N) :
    (cyclicQubitShift N s p).1 = (p.1 + s) % N := by
  rw [cyclicQubitShift_eq_finCycle hN hs]
  rfl

/-- The last `s` coordinates wrap to the first `s` coordinates under the
literal cyclic shift. -/
theorem cyclicQubitShift_val_of_final_segment
    {N s : ℕ} (hN : 0 < N) (hs : s < N)
    (q : Fin s) :
    (cyclicQubitShift N s
        ⟨N - s + q.1, by omega⟩).1 = q.1 := by
  rw [cyclicQubitShift_val hN hs]
  have hsum : N - s + q.1 + s = N + q.1 := by omega
  rw [hsum]
  simpa [Nat.add_mod, Nat.mod_eq_of_lt (q.2.trans hs)]

/-! ## Reindexing tensor identities -/

/-- Two successive basis transports of a CP endomorphism are one transport
along the composite equivalence. -/
theorem CompletelyPositiveMap.reindexEquiv_trans
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

theorem CompletelyPositiveMap.reindexEquiv_refl
    {I : Type*} [Fintype I] [DecidableEq I]
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CompletelyPositiveMap.reindexEquiv (Equiv.refl I) Phi = Phi := by
  apply DFunLike.coe_injective
  funext X
  rfl

theorem CompletelyPositiveMap.reindexEquiv_symm_cancel
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    CompletelyPositiveMap.reindexEquiv e.symm
        (CompletelyPositiveMap.reindexEquiv e Phi) = Phi := by
  rw [CompletelyPositiveMap.reindexEquiv_trans,
    Equiv.self_trans_symm, CompletelyPositiveMap.reindexEquiv_refl]

/-- The normalized finite third twirl is natural under an arbitrary explicit
change of basis on its untouched register. -/
theorem finiteUnitaryThirdTwirlTensorIdCP_reindex_inactive
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

/-- Reindexing only the acted factor of a tensor-identity unitary reindexes
the acted unitary and leaves the untouched coordinate literally fixed. -/
theorem factorizationReindexUnitary_finiteUnitaryTensorId_active
    {I I' J : Type*}
    [Fintype I] [Fintype I'] [Fintype J]
    [DecidableEq I] [DecidableEq I'] [DecidableEq J]
    (e : I ≃ I') (U : Matrix.unitaryGroup I ℂ) :
    factorizationReindexUnitary
        (e.prodCongr (Equiv.refl J))
        (finiteUnitaryTensorId (J := J) U) =
      finiteUnitaryTensorId (J := J)
        (factorizationReindexUnitary e U) := by
  apply Subtype.ext
  ext x y
  rcases x with ⟨xi, xj⟩
  rcases y with ⟨yi, yj⟩
  rfl

/-- Flatten a factorized active/inactive finite twirl back onto the exact
physical one-replica split.  The equality `houter` is the trust boundary:
it requires the supplied subsystem split to be the physical split followed
by the displayed active-coordinate equivalence. -/
theorem CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
    {Q P P' R S T E : Type*}
    [Fintype Q] [Fintype P] [Fintype P'] [Fintype R]
    [Fintype S] [Fintype T] [Fintype E]
    [Nonempty P] [Nonempty P'] [Nonempty R]
    [Nonempty S] [Nonempty T] [Nonempty E]
    [DecidableEq Q] [DecidableEq P] [DecidableEq P']
    [DecidableEq R] [DecidableEq S] [DecidableEq T]
    (physical : Q ≃ P × R) (active : P ≃ P')
    (outer : Q ≃ P' × R)
    (houter : physical.trans
        (active.prodCongr (Equiv.refl R)) = outer)
    (replica : TripleIndex P' ≃ S)
    (inactive : TripleIndex R ≃ T)
    (U : E → Matrix.unitaryGroup P ℂ) :
    CompletelyPositiveMap.finiteChoiTensorId
        (tripleIndexActiveInactiveEquiv outer replica inactive)
        (CompletelyPositiveMap.reindexEquiv
          ((tripleIndexCongr active).trans replica)
          (finiteUnitaryThirdTwirlCP U)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr physical).symm
        (finiteUnitaryThirdTwirlTensorIdCP (J := R) U) := by
  rw [← CompletelyPositiveMap.reindexEquiv_trans]
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  rw [CompletelyPositiveMap.finiteChoiTensorId_reindexedThirdTwirl]
  unfold finiteUnitaryThirdTwirlTensorIdCP
  change CompletelyPositiveMap.reindexEquiv
      (tripleIndexCongr outer.symm)
        (finiteUnitaryThirdTwirlCP _) =
    CompletelyPositiveMap.reindexEquiv
      (tripleIndexCongr physical.symm)
        (finiteUnitaryThirdTwirlCP _)
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv,
    finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  rw [← factorizationReindexUnitary_finiteUnitaryTensorId_active]
  rw [factorizationReindexUnitary_trans]
  have he :
      (active.prodCongr (Equiv.refl R)).trans outer.symm =
        physical.symm := by
    rw [← houter]
    apply Equiv.ext
    intro x
    rcases x with ⟨xp, xr⟩
    simp
  rw [he]

/-- Nested untouched factors reassociate to one product-valued untouched
factor. -/
theorem factorizationReindexUnitary_finiteUnitaryTensorId_assoc
    {I J R : Type*}
    [Fintype I] [Fintype J] [Fintype R]
    [DecidableEq I] [DecidableEq J] [DecidableEq R]
    (U : Matrix.unitaryGroup I ℂ) :
    factorizationReindexUnitary (Equiv.prodAssoc I J R)
        (finiteUnitaryTensorId (J := R)
          (finiteUnitaryTensorId (J := J) U)) =
      finiteUnitaryTensorId (J := J × R) U := by
  apply Subtype.ext
  ext x y
  rcases x with ⟨xI, xJ, xR⟩
  rcases y with ⟨yI, yJ, yR⟩
  simp [factorizationReindexUnitary, finiteUnitaryTensorId, Prod.ext_iff]

/-- CP-map form of tensor-identity reassociation. -/
theorem finiteUnitaryThirdTwirlTensorIdCP_reindex_assoc
    {I J R E : Type*}
    [Fintype I] [Fintype J] [Fintype R] [Fintype E]
    [DecidableEq I] [DecidableEq J] [DecidableEq R]
    [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (Equiv.prodAssoc I J R))
        (finiteUnitaryThirdTwirlTensorIdCP (J := R)
          (fun a ↦ finiteUnitaryTensorId (J := J) (U a))) =
      finiteUnitaryThirdTwirlTensorIdCP (J := J × R) U := by
  unfold finiteUnitaryThirdTwirlTensorIdCP
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  exact factorizationReindexUnitary_finiteUnitaryTensorId_assoc (U a)

/-- Flatten two literal untouched factors after the corresponding
one-replica reassociation of a physical split. -/
theorem finiteUnitaryThirdTwirlTensorIdCP_nested_physical
    {Q I J R E : Type*}
    [Fintype Q] [Fintype I] [Fintype J] [Fintype R] [Fintype E]
    [DecidableEq Q] [DecidableEq I] [DecidableEq J] [DecidableEq R]
    [Nonempty E]
    (flat : Q ≃ I × (J × R))
    (nested : Q ≃ (I × J) × R)
    (hsplit : flat.trans (Equiv.prodAssoc I J R).symm = nested)
    (U : E → Matrix.unitaryGroup I ℂ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr nested).symm
        (finiteUnitaryThirdTwirlTensorIdCP (J := R)
          (fun a ↦ finiteUnitaryTensorId (J := J) (U a))) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr flat).symm
        (finiteUnitaryThirdTwirlTensorIdCP (J := J × R) U) := by
  have he :
      (tripleIndexCongr nested).symm =
        (tripleIndexCongr (Equiv.prodAssoc I J R)).trans
          (tripleIndexCongr flat).symm := by
    have he₀ : nested.symm =
        (Equiv.prodAssoc I J R).trans flat.symm := by
      rw [← hsplit]
      apply Equiv.ext
      intro x
      simp
    apply Equiv.ext
    intro x
    rcases x with ⟨x₀, x₁, x₂⟩
    change
      (nested.symm x₀, nested.symm x₁, nested.symm x₂) =
        (flat.symm ((Equiv.prodAssoc I J R) x₀),
          flat.symm ((Equiv.prodAssoc I J R) x₁),
          flat.symm ((Equiv.prodAssoc I J R) x₂))
    rw [he₀]
    rfl
  rw [he, ← CompletelyPositiveMap.reindexEquiv_trans]
  rw [finiteUnitaryThirdTwirlTensorIdCP_reindex_assoc]

/-! ## Non-closing arithmetic -/

/-- Raw (not truncated by `min`) active length after gate `i`. -/
def choKimRawActiveQubitCount (K i : ℕ) : ℕ :=
  K + i * (K / 2)

theorem choKimRawActiveQubitCount_mono (K : ℕ) :
    Monotone (choKimRawActiveQubitCount K) := by
  intro i j hij
  unfold choKimRawActiveQubitCount
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (K / 2) hij) K

theorem choKimRawActiveQubitCount_penultimate
    {m K : ℕ} (hm : 0 < m) (hK : Even K) :
    choKimRawActiveQubitCount K (2 * m - 2) = m * K := by
  obtain ⟨k, rfl⟩ := hK
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  unfold choKimRawActiveQubitCount
  have hhalf : (k + k) / 2 = k := by omega
  have hindex : 2 * (r + 1) - 2 = 2 * r := by omega
  rw [hhalf, hindex]
  simp [Nat.succ_eq_add_one]
  ring

theorem ChoKimBlockCondition.rawActive_succ_le_total
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimRawActiveQubitCount K (i + 1) ≤ (n / K) * K := by
  have hm := h.blockQuotient_pos hn
  have hi' : i + 1 ≤ 2 * (n / K) - 2 := by omega
  calc
    choKimRawActiveQubitCount K (i + 1) ≤
        choKimRawActiveQubitCount K (2 * (n / K) - 2) :=
      choKimRawActiveQubitCount_mono K hi'
    _ = (n / K) * K :=
      choKimRawActiveQubitCount_penultimate hm h.block_even

theorem ChoKimBlockCondition.rawActive_le_total_of_nonclosing
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimRawActiveQubitCount K i ≤ (n / K) * K := by
  exact (choKimRawActiveQubitCount_mono K (Nat.le_succ i)).trans
    (h.rawActive_succ_le_total hn hi)

theorem ChoKimBlockCondition.activeQubitCount_eq_raw_of_nonclosing
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimActiveQubitCount ((n / K) * K) K i =
      choKimRawActiveQubitCount K i := by
  exact min_eq_right (h.rawActive_le_total_of_nonclosing hn hi)

theorem ChoKimBlockCondition.activeQubitCount_succ_eq_raw_of_nonclosing
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimActiveQubitCount ((n / K) * K) K (i + 1) =
      choKimRawActiveQubitCount K (i + 1) := by
  exact min_eq_right (h.rawActive_succ_le_total hn hi)

theorem ChoKimBlockCondition.halfBlock_pos
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    0 < K / 2 := by
  have hK := h.block_pos
  obtain ⟨k, hk⟩ := h.block_even
  subst K
  omega

theorem ChoKimBlockCondition.halfBlock_add_halfBlock
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    K / 2 + K / 2 = K := by
  obtain ⟨k, rfl⟩ := h.block_even
  omega

theorem ChoKimBlockCondition.halfBlock_le_rawActive
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    K / 2 ≤ choKimRawActiveQubitCount K i := by
  unfold choKimRawActiveQubitCount
  have hhalf : K / 2 ≤ K := Nat.div_le_self K 2
  omega

theorem choKimRawActiveQubitCount_succ (K i : ℕ) :
    choKimRawActiveQubitCount K (i + 1) =
      choKimRawActiveQubitCount K i + K / 2 := by
  unfold choKimRawActiveQubitCount
  rw [Nat.add_mul]
  simp only [one_mul]
  omega

theorem ChoKimBlockCondition.rawActive_sub_half_add
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    choKimRawActiveQubitCount K i - K / 2 + K / 2 =
      choKimRawActiveQubitCount K i := by
  exact Nat.sub_add_cancel h.halfBlock_le_rawActive

theorem ChoKimBlockCondition.nonclosing_partition_total
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (((choKimRawActiveQubitCount K i - K / 2) + K / 2) + K / 2) +
        ((n / K) * K - choKimRawActiveQubitCount K (i + 1)) =
      (n / K) * K := by
  rw [h.rawActive_sub_half_add,
    ← choKimRawActiveQubitCount_succ]
  exact Nat.add_sub_of_le (h.rawActive_succ_le_total hn hi)

/-! ## The four actual subsystem types -/

abbrev ChoKimOldOnly (K i : ℕ) :=
  PauliBinaryWord (choKimRawActiveQubitCount K i - K / 2)

abbrev ChoKimOverlap (K : ℕ) := PauliBinaryWord (K / 2)

abbrev ChoKimNewOnly (K : ℕ) := PauliBinaryWord (K / 2)

abbrev ChoKimInactive (n K i : ℕ) :=
  PauliBinaryWord ((n / K) * K - choKimRawActiveQubitCount K (i + 1))

theorem ChoKimBlockCondition.nonclosing_newActive_tail_total
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimRawActiveQubitCount K (i + 1) +
        ((n / K) * K - choKimRawActiveQubitCount K (i + 1)) =
      (n / K) * K :=
  Nat.add_sub_of_le (h.rawActive_succ_le_total hn hi)

theorem ChoKimBlockCondition.nonclosing_old_new_tail_total
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimRawActiveQubitCount K i + K / 2) +
        ((n / K) * K - choKimRawActiveQubitCount K (i + 1)) =
      (n / K) * K := by
  rw [← choKimRawActiveQubitCount_succ]
  exact h.nonclosing_newActive_tail_total hn hi

theorem ChoKimBlockCondition.oldInactive_length
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    K / 2 + ((n / K) * K -
        choKimRawActiveQubitCount K (i + 1)) =
      (n / K) * K - choKimRawActiveQubitCount K i := by
  have htotal := h.rawActive_succ_le_total hn hi
  rw [choKimRawActiveQubitCount_succ] at htotal ⊢
  omega

theorem ChoKimBlockCondition.nonclosing_middle_tail_total
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    ((choKimRawActiveQubitCount K i - K / 2) + K) +
        ((n / K) * K - choKimRawActiveQubitCount K (i + 1)) =
      (n / K) * K := by
  have hsub := h.rawActive_sub_half_add (i := i)
  have hhalf := h.halfBlock_add_halfBlock
  have htotal := h.nonclosing_old_new_tail_total hn hi
  omega

/-- Split the literal inactive suffix after the old active prefix into the
new half-block followed by the untouched tail. -/
def choKimOldInactiveSuffixSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K - choKimRawActiveQubitCount K i) ≃
      ChoKimNewOnly K × ChoKimInactive n K i :=
  (pauliBinaryWordCongr (h.oldInactive_length hn hi).symm).trans
    (pauliBinaryWordAddEquiv (K / 2)
      ((n / K) * K - choKimRawActiveQubitCount K (i + 1)))

/-- Literal old-active-prefix / inactive-suffix split, with the inactive
suffix itself split into its new half-block and untouched tail. -/
def choKimOldActiveFlatPhysicalSplitCore
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      PauliBinaryWord (choKimRawActiveQubitCount K i) ×
        (ChoKimNewOnly K × ChoKimInactive n K i) :=
  (binaryWordPrefixEquiv ((n / K) * K)
      (choKimRawActiveQubitCount K i)
      (h.rawActive_le_total_of_nonclosing hn hi)).trans
    ((Equiv.refl
      (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
        (choKimOldInactiveSuffixSplit h hn hi))

/-- The exact physical split `old-active | new-half | untouched-tail`. -/
def choKimOldNewInactivePhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      (PauliBinaryWord (choKimRawActiveQubitCount K i) ×
        ChoKimNewOnly K) × ChoKimInactive n K i :=
  (choKimOldActiveFlatPhysicalSplitCore h hn hi).trans
    (Equiv.prodAssoc
      (PauliBinaryWord (choKimRawActiveQubitCount K i))
      (ChoKimNewOnly K) (ChoKimInactive n K i)).symm

/-- The exact physical split `next-middle-gate | old-only-prefix |
untouched-tail`.  The acted factor is moved first only after the literal
middle interval has been extracted. -/
def choKimMiddleGateLiteralPhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      (PauliBinaryWord K × ChoKimOldOnly K i) ×
        ChoKimInactive n K i :=
  (pauliBinaryWordMiddleEquivOfEq
      (choKimRawActiveQubitCount K i - K / 2) K
      ((n / K) * K - choKimRawActiveQubitCount K (i + 1))
      (h.nonclosing_middle_tail_total hn hi)).trans
    (Equiv.prodAssoc (PauliBinaryWord K) (ChoKimOldOnly K i)
      (ChoKimInactive n K i)).symm

/-- The exact physical split `enlarged-active-prefix | untouched-tail`. -/
def choKimNewActiveLiteralPhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      PauliBinaryWord (choKimRawActiveQubitCount K (i + 1)) ×
        ChoKimInactive n K i :=
  (pauliBinaryWordCongr
      (h.nonclosing_newActive_tail_total hn hi).symm).trans
    (pauliBinaryWordAddEquiv
      (choKimRawActiveQubitCount K (i + 1))
      ((n / K) * K - choKimRawActiveQubitCount K (i + 1)))

/-- In a right-composition step, the old active interval is `A×B`. -/
def choKimForwardABEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord (choKimRawActiveQubitCount K i) ≃
      ChoKimOldOnly K i × ChoKimOverlap K :=
  (pauliBinaryWordCongr h.rawActive_sub_half_add.symm).trans
    (pauliBinaryWordAddEquiv
      (choKimRawActiveQubitCount K i - K / 2) (K / 2))

/-- The next `K`-qubit gate is the physical interval `B×C`. -/
def choKimForwardBCEquiv
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord K ≃ ChoKimOverlap K × ChoKimNewOnly K :=
  (pauliBinaryWordCongr h.halfBlock_add_halfBlock.symm).trans
    (pauliBinaryWordAddEquiv (K / 2) (K / 2))

/-- Forward subsystem-major split of the enlarged active interval. -/
def choKimForwardABCEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord (choKimRawActiveQubitCount K (i + 1)) ≃
      (ChoKimOldOnly K i × ChoKimOverlap K) ×
        ChoKimNewOnly K :=
  (pauliBinaryWordCongr <| by
      rw [choKimRawActiveQubitCount_succ,
        h.rawActive_sub_half_add]).trans
    (pauliBinaryWordThreeEquiv
      (choKimRawActiveQubitCount K i - K / 2)
      (K / 2) (K / 2))

/-- Full forward `A,B,C,R` split of the canonical physical register. -/
def choKimForwardABCRSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      ((ChoKimOldOnly K i × ChoKimOverlap K) ×
        ChoKimNewOnly K) × ChoKimInactive n K i :=
  (choKimOldNewInactivePhysicalSplit h hn hi).trans
    ((((choKimForwardABEquiv h).prodCongr
        (Equiv.refl (ChoKimNewOnly K))).prodCongr
      (Equiv.refl (ChoKimInactive n K i))))

/-- Replica-level form of the exact forward support partition. -/
def choKimForwardReplicaSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    TripleIndex (PauliBinaryWord ((n / K) * K)) ≃
      ThreeReplicaABC (ChoKimOldOnly K i) (ChoKimOverlap K)
          (ChoKimNewOnly K) ×
        ThreeReplica (ChoKimInactive n K i) :=
  tripleIndexActiveInactiveEquiv
    (choKimForwardABCRSplit h hn hi)
    (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
      (ChoKimNewOnly K))
    (tripleIndexEquivThreeReplica (ChoKimInactive n K i))

/-- In a left-composition step the new gate is named `A×B`; the physical
half-block order is therefore swapped. -/
def choKimReverseABEquiv
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord K ≃ ChoKimNewOnly K × ChoKimOverlap K :=
  (choKimForwardBCEquiv h).trans (Equiv.prodComm _ _)

/-- In a left-composition step the old active interval is named `B×C`; its
physical order `C,B` is swapped explicitly. -/
def choKimReverseBCEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord (choKimRawActiveQubitCount K i) ≃
      ChoKimOverlap K × ChoKimOldOnly K i :=
  (choKimForwardABEquiv h).trans (Equiv.prodComm _ _)

/-- Reversed subsystem labels for a left-composition enlarged support. -/
def choKimReverseABCEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord (choKimRawActiveQubitCount K (i + 1)) ≃
      (ChoKimNewOnly K × ChoKimOverlap K) ×
        ChoKimOldOnly K i :=
  (choKimForwardABCEquiv h).trans
    (reverseABCOneReplicaEquiv
      (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i))

/-! ## The six exact one-replica active-coordinate transports -/

/-- Forward old-reference coordinates: split the old active prefix as
`A×B`, leaving the new half-block `C` in place. -/
def choKimForwardOldCoordinateEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord (choKimRawActiveQubitCount K i) ×
        ChoKimNewOnly K ≃
      (ChoKimOldOnly K i × ChoKimOverlap K) ×
        ChoKimNewOnly K :=
  (choKimForwardABEquiv h).prodCongr
    (Equiv.refl (ChoKimNewOnly K))

/-- Forward gate coordinates: the physical middle gate is `B×C`; after
extracting it first, move the old-only prefix `A` back to subsystem-major
order. -/
def choKimForwardGateCoordinateEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord K × ChoKimOldOnly K i ≃
      (ChoKimOldOnly K i × ChoKimOverlap K) ×
        ChoKimNewOnly K :=
  ((choKimForwardBCEquiv h).prodCongr
      (Equiv.refl (ChoKimOldOnly K i))).trans
    (bcaOneReplicaEquivABC (ChoKimOldOnly K i)
      (ChoKimOverlap K) (ChoKimNewOnly K))

/-- Reverse gate coordinates: the same physical middle gate is named
`A×B = new×overlap`. -/
def choKimReverseGateCoordinateEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord K × ChoKimOldOnly K i ≃
      (ChoKimNewOnly K × ChoKimOverlap K) ×
        ChoKimOldOnly K i :=
  (choKimForwardGateCoordinateEquiv h).trans
    (reverseABCOneReplicaEquiv
      (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i))

/-- Reverse old-reference coordinates: the old active prefix is named
`B×C = overlap×old`, and the new half-block is moved to `A`. -/
def choKimReverseOldCoordinateEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    PauliBinaryWord (choKimRawActiveQubitCount K i) ×
        ChoKimNewOnly K ≃
      (ChoKimNewOnly K × ChoKimOverlap K) ×
        ChoKimOldOnly K i :=
  (choKimForwardOldCoordinateEquiv h).trans
    (reverseABCOneReplicaEquiv
      (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i))

/-- The physical `B×C` middle-gate split, obtained from the literal
`old | new-half | tail` partition by the explicit forward coordinate map.
The separate `choKimMiddleGateLiteralPhysicalSplit` records its direct
interval formula for the support audit. -/
def choKimMiddleGatePhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      (PauliBinaryWord K × ChoKimOldOnly K i) ×
        ChoKimInactive n K i :=
  (choKimForwardABCRSplit h hn hi).trans
    (((choKimForwardGateCoordinateEquiv h).prodCongr
      (Equiv.refl (ChoKimInactive n K i))).symm)

/-- The enlarged-active-prefix split, obtained from the common literal
`A,B,C,R` partition.  Its direct prefix formula is kept separately in
`choKimNewActiveLiteralPhysicalSplit`. -/
def choKimNewActivePhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      PauliBinaryWord (choKimRawActiveQubitCount K (i + 1)) ×
        ChoKimInactive n K i :=
  (choKimForwardABCRSplit h hn hi).trans
    (((choKimForwardABCEquiv h).prodCongr
      (Equiv.refl (ChoKimInactive n K i))).symm)

/-- Full reversed `A,B,C,R` split used only on left-composition steps. -/
def choKimReverseABCRSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      ((ChoKimNewOnly K × ChoKimOverlap K) ×
        ChoKimOldOnly K i) × ChoKimInactive n K i :=
  (choKimForwardABCRSplit h hn hi).trans
    ((reverseABCOneReplicaEquiv
      (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)).prodCongr
        (Equiv.refl (ChoKimInactive n K i)))

/-- Replica-level form of the exact reversed support partition. -/
def choKimReverseReplicaSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    TripleIndex (PauliBinaryWord ((n / K) * K)) ≃
      ThreeReplicaABC (ChoKimNewOnly K) (ChoKimOverlap K)
          (ChoKimOldOnly K i) ×
        ThreeReplica (ChoKimInactive n K i) :=
  tripleIndexActiveInactiveEquiv
    (choKimReverseABCRSplit h hn hi)
    (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
      (ChoKimOldOnly K i))
    (tripleIndexEquivThreeReplica (ChoKimInactive n K i))

/-! The following six equalities are the literal support audit.  Each says
that the common `A,B,C,R` split is obtained from the indicated physical
split by the corresponding one-replica coordinate map. -/

theorem choKimForwardOldPhysical_factor
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimOldNewInactivePhysicalSplit h hn hi).trans
        ((choKimForwardOldCoordinateEquiv h).prodCongr
          (Equiv.refl (ChoKimInactive n K i))) =
      choKimForwardABCRSplit h hn hi := by
  rfl

theorem choKimForwardGatePhysical_factor
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimMiddleGatePhysicalSplit h hn hi).trans
        ((choKimForwardGateCoordinateEquiv h).prodCongr
          (Equiv.refl (ChoKimInactive n K i))) =
      choKimForwardABCRSplit h hn hi := by
  apply Equiv.ext
  intro x
  exact
    (((choKimForwardGateCoordinateEquiv h).prodCongr
      (Equiv.refl (ChoKimInactive n K i))).apply_symm_apply
        ((choKimForwardABCRSplit h hn hi) x))

theorem choKimForwardNewPhysical_factor
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimNewActivePhysicalSplit h hn hi).trans
        ((choKimForwardABCEquiv h).prodCongr
          (Equiv.refl (ChoKimInactive n K i))) =
      choKimForwardABCRSplit h hn hi := by
  apply Equiv.ext
  intro x
  exact
    (((choKimForwardABCEquiv h).prodCongr
      (Equiv.refl (ChoKimInactive n K i))).apply_symm_apply
        ((choKimForwardABCRSplit h hn hi) x))

theorem choKimReverseGatePhysical_factor
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimMiddleGatePhysicalSplit h hn hi).trans
        ((choKimReverseGateCoordinateEquiv h).prodCongr
          (Equiv.refl (ChoKimInactive n K i))) =
      choKimReverseABCRSplit h hn hi := by
  apply Equiv.ext
  intro x
  let fg := (choKimForwardGateCoordinateEquiv (i := i) h).prodCongr
    (Equiv.refl (ChoKimInactive n K i))
  let rho := (reverseABCOneReplicaEquiv
    (ChoKimNewOnly K) (ChoKimOverlap K)
    (ChoKimOldOnly K i)).prodCongr
      (Equiv.refl (ChoKimInactive n K i))
  change rho (fg (fg.symm ((choKimForwardABCRSplit h hn hi) x))) =
    rho ((choKimForwardABCRSplit h hn hi) x)
  exact congrArg rho (fg.apply_symm_apply _)

theorem choKimReverseOldPhysical_factor
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimOldNewInactivePhysicalSplit h hn hi).trans
        ((choKimReverseOldCoordinateEquiv h).prodCongr
          (Equiv.refl (ChoKimInactive n K i))) =
      choKimReverseABCRSplit h hn hi := by
  apply Equiv.ext
  intro x
  rfl

theorem choKimReverseNewPhysical_factor
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimNewActivePhysicalSplit h hn hi).trans
        ((choKimReverseABCEquiv h).prodCongr
          (Equiv.refl (ChoKimInactive n K i))) =
      choKimReverseABCRSplit h hn hi := by
  apply Equiv.ext
  intro x
  let fa := (choKimForwardABCEquiv (i := i) h).prodCongr
    (Equiv.refl (ChoKimInactive n K i))
  let rho := (reverseABCOneReplicaEquiv
    (ChoKimNewOnly K) (ChoKimOverlap K)
    (ChoKimOldOnly K i)).prodCongr
      (Equiv.refl (ChoKimInactive n K i))
  change rho (fa (fa.symm ((choKimForwardABCRSplit h hn hi) x))) =
    rho ((choKimForwardABCRSplit h hn hi) x)
  exact congrArg rho (fa.apply_symm_apply _)

theorem choKimForwardOld_replicaEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    (tripleIndexCongr (choKimForwardOldCoordinateEquiv h)).trans
        (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
          (ChoKimNewOnly K)) =
      pauliHaarABReplicaEquiv (choKimRawActiveQubitCount K i)
        (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
        (choKimForwardABEquiv h) := by
  rfl

theorem choKimForwardGate_replicaEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    (tripleIndexCongr (choKimForwardGateCoordinateEquiv h)).trans
        (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
          (ChoKimNewOnly K)) =
      pauliHaarBCReplicaEquiv K
        (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
        (choKimForwardBCEquiv h) := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x₀, x₁, x₂⟩
  rfl

theorem choKimForwardNew_replicaEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    (tripleIndexCongr (choKimForwardABCEquiv h)).trans
        (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
          (ChoKimNewOnly K)) =
      pauliHaarABCReplicaEquiv
        (choKimRawActiveQubitCount K (i + 1))
        (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
        (choKimForwardABCEquiv h) := by
  rfl

theorem choKimReverseGate_replicaEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    (tripleIndexCongr (choKimReverseGateCoordinateEquiv h)).trans
        (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
          (ChoKimOldOnly K i)) =
      pauliHaarABReplicaEquiv K
        (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
        (choKimReverseABEquiv h) := by
  rfl

theorem choKimReverseOld_replicaEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    (tripleIndexCongr (choKimReverseOldCoordinateEquiv h)).trans
        (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
          (ChoKimOldOnly K i)) =
      pauliHaarBCReplicaEquiv (choKimRawActiveQubitCount K i)
        (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
        (choKimReverseBCEquiv h) := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x₀, x₁, x₂⟩
  rfl

theorem choKimReverseNew_replicaEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    (tripleIndexCongr (choKimReverseABCEquiv h)).trans
        (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
          (ChoKimOldOnly K i)) =
      pauliHaarABCReplicaEquiv
        (choKimRawActiveQubitCount K (i + 1))
        (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
        (choKimReverseABCEquiv h) := by
  rfl

/-! ## Dimension premises discharged from the physical partition -/

theorem two_mul_two_pow_le_two_pow_add
    {a b : ℕ} (ha : 1 ≤ a) :
    2 * (2 : ℝ) ^ b ≤ (2 : ℝ) ^ (a + b) := by
  calc
    2 * (2 : ℝ) ^ b = (2 : ℝ) ^ (1 + b) := by
      rw [pow_add]
      norm_num
    _ ≤ (2 : ℝ) ^ (a + b) :=
      pow_le_pow_right₀ (by norm_num) (Nat.add_le_add_right ha b)

theorem ChoKimBlockCondition.oldOnly_pos
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    0 < choKimRawActiveQubitCount K i - K / 2 := by
  have hh := h.halfBlock_pos
  have hK : K / 2 + K / 2 = K := h.halfBlock_add_halfBlock
  unfold choKimRawActiveQubitCount
  omega

theorem ChoKimBlockCondition.two_overlap_le_old_dimension
    {n K i : ℕ} (h : ChoKimBlockCondition n K) :
    2 * choKimOverlapDimension K ≤
      (((2 ^ choKimRawActiveQubitCount K i : ℕ) : ℝ)) := by
  have ha : 1 ≤ choKimRawActiveQubitCount K i - K / 2 :=
    h.oldOnly_pos
  have hp := two_mul_two_pow_le_two_pow_add
    (b := K / 2) ha
  rw [h.rawActive_sub_half_add] at hp
  simpa [choKimOverlapDimension] using hp

theorem ChoKimBlockCondition.two_overlap_le_block_dimension
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    2 * choKimOverlapDimension K ≤ (((2 ^ K : ℕ) : ℝ)) := by
  have hp := two_mul_two_pow_le_two_pow_add
    (b := K / 2) (Nat.succ_le_iff.mpr h.halfBlock_pos)
  rw [h.halfBlock_add_halfBlock] at hp
  simpa [choKimOverlapDimension] using hp

theorem ChoKimBlockCondition.overlap_add_nine_le_union_dimension
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    choKimOverlapDimension K + 9 ≤
      (((2 ^ choKimRawActiveQubitCount K (i + 1) : ℕ) : ℝ)) := by
  have hq := h.eighteen_le_overlap hn
  have hold := h.two_overlap_le_old_dimension (i := i)
  have hmono :
      (((2 ^ choKimRawActiveQubitCount K i : ℕ) : ℝ)) ≤
        (((2 ^ choKimRawActiveQubitCount K (i + 1) : ℕ) : ℝ)) := by
    exact_mod_cast Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (choKimRawActiveQubitCount_mono K (Nat.le_succ i))
  linarith

theorem choKimOverlapDimension_eq_card_overlap (K : ℕ) :
    choKimOverlapDimension K =
      (Fintype.card (ChoKimOverlap K) : ℝ) := by
  simp [choKimOverlapDimension, PauliBinaryWord]

/-! ## Concrete SHH estimates in the two physical orientations -/

/-- The exact forward-factorized non-closing step.  Its first map is Haar on
the old active `A×B` interval and its second map is Haar on the next `B×C`
gate. -/
theorem ChoKimBlockCondition.relativeCPApproximation_forwardFactorizedStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (CompletelyPositiveMap.comp
        (CompletelyPositiveMap.finiteChoiTensorId
          (choKimForwardReplicaSplit h hn hi)
          (finiteThreeMomentABHaarCP
            (choKimRawActiveQubitCount K i)
            (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
            (choKimForwardABEquiv h)))
        (CompletelyPositiveMap.finiteChoiTensorId
          (choKimForwardReplicaSplit h hn hi)
          (finiteThreeMomentBCHaarCP K
            (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
            (choKimForwardBCEquiv h)))).toLinearMap
      (CompletelyPositiveMap.finiteChoiTensorId
        (choKimForwardReplicaSplit h hn hi)
        (finiteThreeMomentABCHaarCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
          (choKimForwardABCEquiv h))).toLinearMap := by
  apply relativeCPApproximation_concretePairwiseActualHaar_inactive
    (choKimRawActiveQubitCount K i) K
    (choKimRawActiveQubitCount K (i + 1))
    (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
    (ChoKimInactive n K i)
    (TripleIndex (PauliBinaryWord ((n / K) * K)))
    (choKimForwardReplicaSplit h hn hi)
    (choKimForwardABEquiv h) (choKimForwardBCEquiv h)
    (choKimForwardABCEquiv h)
    (choKimOverlapDimension K)
  · exact h.eighteen_le_overlap hn
  · rw [choKimOverlapDimension_eq_card_overlap]
  · exact h.two_overlap_le_old_dimension
  · exact h.two_overlap_le_block_dimension
  · exact h.overlap_add_nine_le_union_dimension hn

/-- The exact reversed-factorized non-closing step.  Here the new gate is
`A×B`, the old active interval is `B×C`, and the theorem's composition
therefore has the required left-composition order. -/
theorem ChoKimBlockCondition.relativeCPApproximation_reverseFactorizedStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (CompletelyPositiveMap.comp
        (CompletelyPositiveMap.finiteChoiTensorId
          (choKimReverseReplicaSplit h hn hi)
          (finiteThreeMomentABHaarCP K
            (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
            (choKimReverseABEquiv h)))
        (CompletelyPositiveMap.finiteChoiTensorId
          (choKimReverseReplicaSplit h hn hi)
          (finiteThreeMomentBCHaarCP
            (choKimRawActiveQubitCount K i)
            (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
            (choKimReverseBCEquiv h)))).toLinearMap
      (CompletelyPositiveMap.finiteChoiTensorId
        (choKimReverseReplicaSplit h hn hi)
        (finiteThreeMomentABCHaarCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
          (choKimReverseABCEquiv h))).toLinearMap := by
  apply relativeCPApproximation_concretePairwiseActualHaar_inactive
    K (choKimRawActiveQubitCount K i)
    (choKimRawActiveQubitCount K (i + 1))
    (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
    (ChoKimInactive n K i)
    (TripleIndex (PauliBinaryWord ((n / K) * K)))
    (choKimReverseReplicaSplit h hn hi)
    (choKimReverseABEquiv h) (choKimReverseBCEquiv h)
    (choKimReverseABCEquiv h)
    (choKimOverlapDimension K)
  · exact h.eighteen_le_overlap hn
  · rw [choKimOverlapDimension_eq_card_overlap]
  · exact h.two_overlap_le_block_dimension
  · exact h.two_overlap_le_old_dimension
  · exact h.overlap_add_nine_le_union_dimension hn

/-! ## The six factorized maps flattened onto their physical splits -/

theorem ChoKimBlockCondition.forwardAB_eq_physicalNested
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.finiteChoiTensorId
        (choKimForwardReplicaSplit h hn hi)
        (finiteThreeMomentABHaarCP
          (choKimRawActiveQubitCount K i)
          (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
          (choKimForwardABEquiv h)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimOldNewInactivePhysicalSplit h hn hi)).symm
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := ChoKimInactive n K i)
          (fun a : PauliCosetCliffordEnsemble
              (choKimRawActiveQubitCount K i) ↦
            finiteUnitaryTensorId (J := ChoKimNewOnly K)
              (pauliCosetCliffordUnitary
                (choKimRawActiveQubitCount K i) a))) := by
  simpa only [choKimForwardReplicaSplit,
      finiteThreeMomentABHaarCP, pauliHaarThirdTwirlTensorIdCP,
      finiteUnitaryThirdTwirlTensorIdCP,
      choKimForwardOld_replicaEquiv] using
    CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
      (choKimOldNewInactivePhysicalSplit h hn hi)
      (choKimForwardOldCoordinateEquiv h)
      (choKimForwardABCRSplit h hn hi)
      (choKimForwardOldPhysical_factor h hn hi)
      (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
        (ChoKimNewOnly K))
      (tripleIndexEquivThreeReplica (ChoKimInactive n K i))
      (fun a : PauliCosetCliffordEnsemble
          (choKimRawActiveQubitCount K i) ↦
        finiteUnitaryTensorId (J := ChoKimNewOnly K)
          (pauliCosetCliffordUnitary
            (choKimRawActiveQubitCount K i) a))

theorem ChoKimBlockCondition.forwardBC_eq_physicalNested
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.finiteChoiTensorId
        (choKimForwardReplicaSplit h hn hi)
        (finiteThreeMomentBCHaarCP K
          (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
          (choKimForwardBCEquiv h)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimMiddleGatePhysicalSplit h hn hi)).symm
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := ChoKimInactive n K i)
          (fun a : PauliCosetCliffordEnsemble K ↦
            finiteUnitaryTensorId (J := ChoKimOldOnly K i)
              (pauliCosetCliffordUnitary K a))) := by
  simpa only [choKimForwardReplicaSplit,
      finiteThreeMomentBCHaarCP, pauliHaarThirdTwirlTensorIdCP,
      finiteUnitaryThirdTwirlTensorIdCP,
      choKimForwardGate_replicaEquiv] using
    CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
      (choKimMiddleGatePhysicalSplit h hn hi)
      (choKimForwardGateCoordinateEquiv h)
      (choKimForwardABCRSplit h hn hi)
      (choKimForwardGatePhysical_factor h hn hi)
      (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
        (ChoKimNewOnly K))
      (tripleIndexEquivThreeReplica (ChoKimInactive n K i))
      (fun a : PauliCosetCliffordEnsemble K ↦
        finiteUnitaryTensorId (J := ChoKimOldOnly K i)
          (pauliCosetCliffordUnitary K a))

theorem ChoKimBlockCondition.forwardABC_eq_physical
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.finiteChoiTensorId
        (choKimForwardReplicaSplit h hn hi)
        (finiteThreeMomentABCHaarCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimOldOnly K i) (ChoKimOverlap K) (ChoKimNewOnly K)
          (choKimForwardABCEquiv h)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimNewActivePhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimInactive n K i)) := by
  simpa only [choKimForwardReplicaSplit,
      finiteThreeMomentABCHaarCP, pauliHaarThirdTwirlTensorIdCP,
      pauliHaarThirdTwirlCP, finitePauliCosetThirdTwirlCP,
      finiteUnitaryThirdTwirlTensorIdCP,
      choKimForwardNew_replicaEquiv] using
    CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
      (choKimNewActivePhysicalSplit h hn hi)
      (choKimForwardABCEquiv h)
      (choKimForwardABCRSplit h hn hi)
      (choKimForwardNewPhysical_factor h hn hi)
      (tripleIndexABCEquiv (ChoKimOldOnly K i) (ChoKimOverlap K)
        (ChoKimNewOnly K))
      (tripleIndexEquivThreeReplica (ChoKimInactive n K i))
      (pauliCosetCliffordUnitary
        (choKimRawActiveQubitCount K (i + 1)))

theorem ChoKimBlockCondition.reverseAB_eq_physicalNested
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.finiteChoiTensorId
        (choKimReverseReplicaSplit h hn hi)
        (finiteThreeMomentABHaarCP K
          (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
          (choKimReverseABEquiv h)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimMiddleGatePhysicalSplit h hn hi)).symm
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := ChoKimInactive n K i)
          (fun a : PauliCosetCliffordEnsemble K ↦
            finiteUnitaryTensorId (J := ChoKimOldOnly K i)
              (pauliCosetCliffordUnitary K a))) := by
  simpa only [choKimReverseReplicaSplit,
      finiteThreeMomentABHaarCP, pauliHaarThirdTwirlTensorIdCP,
      finiteUnitaryThirdTwirlTensorIdCP,
      choKimReverseGate_replicaEquiv] using
    CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
      (choKimMiddleGatePhysicalSplit h hn hi)
      (choKimReverseGateCoordinateEquiv h)
      (choKimReverseABCRSplit h hn hi)
      (choKimReverseGatePhysical_factor h hn hi)
      (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
        (ChoKimOldOnly K i))
      (tripleIndexEquivThreeReplica (ChoKimInactive n K i))
      (fun a : PauliCosetCliffordEnsemble K ↦
        finiteUnitaryTensorId (J := ChoKimOldOnly K i)
          (pauliCosetCliffordUnitary K a))

theorem ChoKimBlockCondition.reverseBC_eq_physicalNested
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.finiteChoiTensorId
        (choKimReverseReplicaSplit h hn hi)
        (finiteThreeMomentBCHaarCP
          (choKimRawActiveQubitCount K i)
          (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
          (choKimReverseBCEquiv h)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimOldNewInactivePhysicalSplit h hn hi)).symm
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := ChoKimInactive n K i)
          (fun a : PauliCosetCliffordEnsemble
              (choKimRawActiveQubitCount K i) ↦
            finiteUnitaryTensorId (J := ChoKimNewOnly K)
              (pauliCosetCliffordUnitary
                (choKimRawActiveQubitCount K i) a))) := by
  simpa only [choKimReverseReplicaSplit,
      finiteThreeMomentBCHaarCP, pauliHaarThirdTwirlTensorIdCP,
      finiteUnitaryThirdTwirlTensorIdCP,
      choKimReverseOld_replicaEquiv] using
    CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
      (choKimOldNewInactivePhysicalSplit h hn hi)
      (choKimReverseOldCoordinateEquiv h)
      (choKimReverseABCRSplit h hn hi)
      (choKimReverseOldPhysical_factor h hn hi)
      (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
        (ChoKimOldOnly K i))
      (tripleIndexEquivThreeReplica (ChoKimInactive n K i))
      (fun a : PauliCosetCliffordEnsemble
          (choKimRawActiveQubitCount K i) ↦
        finiteUnitaryTensorId (J := ChoKimNewOnly K)
          (pauliCosetCliffordUnitary
            (choKimRawActiveQubitCount K i) a))

theorem ChoKimBlockCondition.reverseABC_eq_physical
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.finiteChoiTensorId
        (choKimReverseReplicaSplit h hn hi)
        (finiteThreeMomentABCHaarCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimNewOnly K) (ChoKimOverlap K) (ChoKimOldOnly K i)
          (choKimReverseABCEquiv h)) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimNewActivePhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimInactive n K i)) := by
  simpa only [choKimReverseReplicaSplit,
      finiteThreeMomentABCHaarCP, pauliHaarThirdTwirlTensorIdCP,
      pauliHaarThirdTwirlCP, finitePauliCosetThirdTwirlCP,
      finiteUnitaryThirdTwirlTensorIdCP,
      choKimReverseNew_replicaEquiv] using
    CompletelyPositiveMap.finiteChoiTensorId_factorizedThirdTwirl_eq_physical
      (choKimNewActivePhysicalSplit h hn hi)
      (choKimReverseABCEquiv h)
      (choKimReverseABCRSplit h hn hi)
      (choKimReverseNewPhysical_factor h hn hi)
      (tripleIndexABCEquiv (ChoKimNewOnly K) (ChoKimOverlap K)
        (ChoKimOldOnly K i))
      (tripleIndexEquivThreeReplica (ChoKimInactive n K i))
      (pauliCosetCliffordUnitary
        (choKimRawActiveQubitCount K (i + 1)))

/-! ## Flatten the two untouched factors -/

def choKimOldActiveFlatPhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      PauliBinaryWord (choKimRawActiveQubitCount K i) ×
        (ChoKimNewOnly K × ChoKimInactive n K i) :=
  choKimOldActiveFlatPhysicalSplitCore h hn hi

def choKimMiddleGateFlatPhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      PauliBinaryWord K ×
        (ChoKimOldOnly K i × ChoKimInactive n K i) :=
  (choKimMiddleGatePhysicalSplit h hn hi).trans
    (Equiv.prodAssoc (PauliBinaryWord K) (ChoKimOldOnly K i)
      (ChoKimInactive n K i))

theorem choKimOldActiveFlatPhysicalSplit_assoc
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimOldActiveFlatPhysicalSplit h hn hi).trans
        (Equiv.prodAssoc
          (PauliBinaryWord (choKimRawActiveQubitCount K i))
          (ChoKimNewOnly K) (ChoKimInactive n K i)).symm =
      choKimOldNewInactivePhysicalSplit h hn hi := by
  apply Equiv.ext
  intro x
  rfl

theorem choKimMiddleGateFlatPhysicalSplit_assoc
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimMiddleGateFlatPhysicalSplit h hn hi).trans
        (Equiv.prodAssoc (PauliBinaryWord K) (ChoKimOldOnly K i)
          (ChoKimInactive n K i)).symm =
      choKimMiddleGatePhysicalSplit h hn hi := by
  apply Equiv.ext
  intro x
  simp [choKimMiddleGateFlatPhysicalSplit]

theorem ChoKimBlockCondition.oldNested_eq_flatPhysical
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimOldNewInactivePhysicalSplit h hn hi)).symm
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := ChoKimInactive n K i)
          (fun a : PauliCosetCliffordEnsemble
              (choKimRawActiveQubitCount K i) ↦
            finiteUnitaryTensorId (J := ChoKimNewOnly K)
              (pauliCosetCliffordUnitary
                (choKimRawActiveQubitCount K i) a))) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimOldActiveFlatPhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K i)
          (ChoKimNewOnly K × ChoKimInactive n K i)) := by
  simpa only [pauliHaarThirdTwirlTensorIdCP] using
    finiteUnitaryThirdTwirlTensorIdCP_nested_physical
      (choKimOldActiveFlatPhysicalSplit h hn hi)
      (choKimOldNewInactivePhysicalSplit h hn hi)
      (choKimOldActiveFlatPhysicalSplit_assoc h hn hi)
      (pauliCosetCliffordUnitary
        (choKimRawActiveQubitCount K i))

theorem ChoKimBlockCondition.gateNested_eq_flatPhysical
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimMiddleGatePhysicalSplit h hn hi)).symm
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := ChoKimInactive n K i)
          (fun a : PauliCosetCliffordEnsemble K ↦
            finiteUnitaryTensorId (J := ChoKimOldOnly K i)
              (pauliCosetCliffordUnitary K a))) =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimMiddleGateFlatPhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP K
          (ChoKimOldOnly K i × ChoKimInactive n K i)) := by
  simpa only [pauliHaarThirdTwirlTensorIdCP] using
    finiteUnitaryThirdTwirlTensorIdCP_nested_physical
      (choKimMiddleGateFlatPhysicalSplit h hn hi)
      (choKimMiddleGatePhysicalSplit h hn hi)
      (choKimMiddleGateFlatPhysicalSplit_assoc h hn hi)
      (pauliCosetCliffordUnitary K)

/-!
The remaining lemmas identify the three displayed factorized maps with,
respectively, the old active Haar reference, the literal next gate, and the
new active Haar reference.  They use only the explicit interval splits above,
the cyclic-shift value theorem, and the tensor-identity naturality lemmas.
-/

/-! ## A consecutive unshifted block is the literal middle interval -/

/-- Removing `j` from an ordered `Fin m` splits the remaining indices into
those below and those above `j`. -/
def finOmitSplitEquiv {m : ℕ} (j : Fin m) :
    {p : Fin m // p ≠ j} ≃ Fin j.1 ⊕ Fin (m - j.1 - 1) where
  toFun p := if hp : p.1.1 < j.1 then
      Sum.inl ⟨p.1.1, hp⟩
    else
      Sum.inr ⟨p.1.1 - (j.1 + 1), by
        have hpval : p.1.1 ≠ j.1 := by
          intro heq
          apply p.2
          exact Fin.ext heq
        omega⟩
  invFun p := match p with
    | Sum.inl q =>
        ⟨⟨q.1, q.2.trans j.2⟩, by
          intro heq
          have hv := congrArg Fin.val heq
          exact (Nat.ne_of_lt q.2) hv⟩
    | Sum.inr q =>
        ⟨⟨j.1 + 1 + q.1, by
          have hj : j.1 < m := j.2
          have hq : q.1 < m - j.1 - 1 := q.2
          omega⟩, by
          apply Fin.ne_of_val_ne
          intro hv
          have hlt : j.1 < j.1 + 1 + q.1 := by omega
          exact (Nat.ne_of_gt hlt) hv⟩
  left_inv p := by
    rcases p with ⟨p, hpj⟩
    have hpval : p.1 ≠ j.1 := by
      intro heq
      apply hpj
      exact Fin.ext heq
    by_cases hp : p.1 < j.1
    · simp [hp]
    · simp [hp]
      apply Fin.ext
      simp
      omega
  right_inv p := by
    rcases p with p | p
    · simp [p.2]
    · simp
      omega

@[simp] theorem finOmitSplitEquiv_symm_inl_val
    {m : ℕ} (j : Fin m) (q : Fin j.1) :
    ((finOmitSplitEquiv j).symm (Sum.inl q)).1.1 = q.1 := rfl

@[simp] theorem finOmitSplitEquiv_symm_inr_val
    {m : ℕ} (j : Fin m) (q : Fin (m - j.1 - 1)) :
    ((finOmitSplitEquiv j).symm (Sum.inr q)).1.1 =
      j.1 + 1 + q.1 := rfl

/-- The other block coordinates, in their physical order, are exactly the
qubits before and after block `j`. -/
def singleBlockComplementMiddleEquiv
    {m : ℕ} (K : ℕ) (j : Fin m) :
    ({p : Fin m // p ≠ j} → PauliBinaryWord K) ≃
      PauliBinaryWord (j.1 * K) ×
        PauliBinaryWord ((m - j.1 - 1) * K) :=
  ((Equiv.piCongrLeft
      (fun _ : Fin j.1 ⊕ Fin (m - j.1 - 1) ↦ PauliBinaryWord K)
      (finOmitSplitEquiv j)).trans
    (Equiv.sumArrowEquivProdArrow
      (Fin j.1) (Fin (m - j.1 - 1)) (PauliBinaryWord K))).trans
    ((binaryWordBlockEquiv j.1 K).symm.prodCongr
      (binaryWordBlockEquiv (m - j.1 - 1) K).symm)

theorem singleBlock_middle_total (K : ℕ) {m : ℕ} (j : Fin m) :
    (j.1 * K + K) + (m - j.1 - 1) * K = m * K := by
  have hm : j.1 + 1 + (m - j.1 - 1) = m := by omega
  calc
    (j.1 * K + K) + (m - j.1 - 1) * K =
        (j.1 + 1 + (m - j.1 - 1)) * K := by ring
    _ = m * K := by rw [hm]

/-- Literal prefix/middle/tail split around the unshifted block `j`. -/
def singleBlockMiddleBinaryWordEquiv
    {m : ℕ} (K : ℕ) (j : Fin m) :
    PauliBinaryWord (m * K) ≃
      PauliBinaryWord K ×
        (PauliBinaryWord (j.1 * K) ×
          PauliBinaryWord ((m - j.1 - 1) * K)) :=
  pauliBinaryWordMiddleEquivOfEq
    (j.1 * K) K ((m - j.1 - 1) * K)
    (singleBlock_middle_total K j)

/-- The block-tensor split and the literal middle-interval split have exactly
the same coordinates. -/
theorem singleBlockBinaryWordEquiv_trans_middleComplement
    {m : ℕ} (K : ℕ) (j : Fin m) :
    (singleBlockBinaryWordEquiv m K j).trans
        ((Equiv.refl (PauliBinaryWord K)).prodCongr
          (singleBlockComplementMiddleEquiv K j)) =
      singleBlockMiddleBinaryWordEquiv K j := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · funext p
    simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
      singleBlockBinaryWordEquiv_apply_fst,
      binaryWordBlockEquiv_apply]
    simp [singleBlockMiddleBinaryWordEquiv,
      pauliBinaryWordMiddleEquivOfEq, pauliBinaryWordMiddleEquiv,
      pauliBinaryWordThreeEquiv, pauliBinaryWordAddEquiv,
      middleIntervalReassocEquiv]
    apply congrArg x
    apply Fin.ext
    simp [singleBlockMiddleBinaryWordEquiv,
      pauliBinaryWordMiddleEquivOfEq, pauliBinaryWordMiddleEquiv,
      pauliBinaryWordThreeEquiv, pauliBinaryWordAddEquiv,
      middleIntervalReassocEquiv, finProdFinEquiv]
    ring
  · apply Prod.ext
    · funext p
      simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
        singleBlockComplementMiddleEquiv,
        singleBlockBinaryWordEquiv_apply_snd,
        Equiv.sumArrowEquivProdArrow_apply_fst,
        binaryWordBlockEquiv, Equiv.piCongrLeft_apply,
        Equiv.piCongrLeft_apply_apply]
      simp [singleBlockMiddleBinaryWordEquiv,
        pauliBinaryWordMiddleEquivOfEq, pauliBinaryWordMiddleEquiv,
        pauliBinaryWordThreeEquiv, pauliBinaryWordAddEquiv,
        middleIntervalReassocEquiv]
      rw [Equiv.piCongrLeft_apply]
      simp only [eq_rec_constant,
        singleBlockBinaryWordEquiv_apply_snd,
        binaryWordBlockEquiv_apply, pauliBinaryWordCongr_apply]
      apply congrArg x
      apply Fin.ext
      have hp := finProdFinEquiv.apply_symm_apply p
      simpa [finOmitSplitEquiv, finProdFinEquiv_symm_apply] using
        congrArg Fin.val hp
    · funext p
      simp only [Equiv.trans_apply, Equiv.prodCongr_apply, Equiv.refl_apply,
        singleBlockComplementMiddleEquiv,
        singleBlockBinaryWordEquiv_apply_snd,
        Equiv.sumArrowEquivProdArrow_apply_snd,
        binaryWordBlockEquiv, Equiv.piCongrLeft_apply,
        Equiv.piCongrLeft_apply_apply]
      simp [singleBlockMiddleBinaryWordEquiv,
        pauliBinaryWordMiddleEquivOfEq, pauliBinaryWordMiddleEquiv,
        pauliBinaryWordThreeEquiv, pauliBinaryWordAddEquiv,
        middleIntervalReassocEquiv]
      rw [Equiv.piCongrLeft_apply]
      simp only [eq_rec_constant,
        singleBlockBinaryWordEquiv_apply_snd,
        binaryWordBlockEquiv_apply, pauliBinaryWordCongr_apply]
      apply congrArg x
      apply Fin.ext
      have hp := finProdFinEquiv.apply_symm_apply p
      have hpv := congrArg Fin.val hp
      have hpdecomp := Nat.mod_add_div p.1 K
      simp [singleBlockMiddleBinaryWordEquiv,
        pauliBinaryWordMiddleEquivOfEq, pauliBinaryWordMiddleEquiv,
        pauliBinaryWordThreeEquiv, pauliBinaryWordAddEquiv,
        middleIntervalReassocEquiv, finOmitSplitEquiv,
        finProdFinEquiv_symm_apply] at hpv ⊢
      ring_nf at hpv ⊢
      omega

/-! ## A non-closing shifted block is also a literal middle interval -/

/-- Reassociate the old complement coordinates after splitting its final
half-block.  The final half-block wraps to the head of the shifted
complement; the old prefix follows it; the shortened old tail remains last. -/
def rotateMiddleComplementReassocEquiv (A T H : Type*) :
    A × (T × H) ≃ (H × A) × T where
  toFun x := ((x.2.2, x.1), x.2.1)
  invFun x := (x.1.2, x.2, x.1.1)
  left_inv x := rfl
  right_inv x := rfl

/-- Exact coordinate rotation on the complement of a middle interval.
The old complement is `prefix(a) × tail(r)`.  Under a right cyclic shift by
`s ≤ r`, the final `s` tail coordinates wrap to the front, giving the new
complement `prefix(a+s) × tail(r-s)`. -/
def rotateMiddleComplementEquiv (a r s : ℕ) (hsr : s ≤ r) :
    PauliBinaryWord a × PauliBinaryWord r ≃
      PauliBinaryWord (a + s) × PauliBinaryWord (r - s) :=
  ((Equiv.refl (PauliBinaryWord a)).prodCongr
      ((pauliBinaryWordCongr (Nat.sub_add_cancel hsr).symm).trans
        (pauliBinaryWordAddEquiv (r - s) s))).trans <|
    (rotateMiddleComplementReassocEquiv
      (PauliBinaryWord a) (PauliBinaryWord (r - s))
      (PauliBinaryWord s)).trans <|
      (((pauliBinaryWordConcatEquiv s a).trans
        (pauliBinaryWordCongr (Nat.add_comm s a))).prodCongr
          (Equiv.refl (PauliBinaryWord (r - s))))

@[simp] theorem rotateMiddleComplementEquiv_fst_final
    (a r s : ℕ) (hsr : s ≤ r)
    (u : PauliBinaryWord a) (v : PauliBinaryWord r) (q : Fin s) :
    (rotateMiddleComplementEquiv a r s hsr (u, v)).1
        (Fin.cast (Nat.add_comm s a) (Fin.castAdd a q)) =
      v (Fin.cast (Nat.sub_add_cancel hsr)
        (Fin.natAdd (r - s) q)) := by
  have hidx :
      Fin.cast (Nat.add_comm s a).symm
          (Fin.cast (Nat.add_comm s a) (Fin.castAdd a q)) =
        Fin.castAdd a q := by
    apply Fin.ext
    rfl
  change
    pauliBinaryWordCongr (Nat.add_comm s a)
      (pauliBinaryWordConcatEquiv s a
        ((pauliBinaryWordAddEquiv (r - s) s
          (pauliBinaryWordCongr (Nat.sub_add_cancel hsr).symm v)).2, u))
      (Fin.cast (Nat.add_comm s a) (Fin.castAdd a q)) = _
  rw [pauliBinaryWordCongr_apply, hidx,
    pauliBinaryWordConcatEquiv_apply_castAdd,
    pauliBinaryWordAddEquiv_snd_apply, pauliBinaryWordCongr_apply]

@[simp] theorem rotateMiddleComplementEquiv_fst_prefix
    (a r s : ℕ) (hsr : s ≤ r)
    (u : PauliBinaryWord a) (v : PauliBinaryWord r) (p : Fin a) :
    (rotateMiddleComplementEquiv a r s hsr (u, v)).1
        (Fin.cast (Nat.add_comm s a) (Fin.natAdd s p)) = u p := by
  have hidx :
      Fin.cast (Nat.add_comm s a).symm
          (Fin.cast (Nat.add_comm s a) (Fin.natAdd s p)) =
        Fin.natAdd s p := by
    apply Fin.ext
    rfl
  change
    pauliBinaryWordCongr (Nat.add_comm s a)
      (pauliBinaryWordConcatEquiv s a
        ((pauliBinaryWordAddEquiv (r - s) s
          (pauliBinaryWordCongr (Nat.sub_add_cancel hsr).symm v)).2, u))
      (Fin.cast (Nat.add_comm s a) (Fin.natAdd s p)) = _
  rw [pauliBinaryWordCongr_apply, hidx,
    pauliBinaryWordConcatEquiv_apply_natAdd]

@[simp] theorem rotateMiddleComplementEquiv_fst_apply_of_ge
    (a r s : ℕ) (hsr : s ≤ r)
    (z : PauliBinaryWord a × PauliBinaryWord r)
    (p : Fin (a + s)) (hp : s ≤ p.1) :
    (rotateMiddleComplementEquiv a r s hsr z).1 p =
      z.1 (⟨p.1 - s, by omega⟩ : Fin a) := by
  let q : Fin a := ⟨p.1 - s, by omega⟩
  have hcast : Fin.cast (Nat.add_comm s a).symm p =
      Fin.natAdd s q := by
    apply Fin.ext
    dsimp [q]
    omega
  simp only [rotateMiddleComplementEquiv, Equiv.trans_apply,
    Equiv.prodCongr_apply, Prod.map_fst, Prod.map_snd,
    Equiv.refl_apply, rotateMiddleComplementReassocEquiv,
    pauliBinaryWordCongr_apply]
  rw [hcast, pauliBinaryWordConcatEquiv_apply_natAdd]
  rfl

@[simp] theorem rotateMiddleComplementEquiv_snd
    (a r s : ℕ) (hsr : s ≤ r)
    (u : PauliBinaryWord a) (v : PauliBinaryWord r) (p : Fin (r - s)) :
    (rotateMiddleComplementEquiv a r s hsr (u, v)).2 p =
      v (Fin.cast (Nat.sub_add_cancel hsr) (Fin.castAdd s p)) := by
  simp [rotateMiddleComplementEquiv, rotateMiddleComplementReassocEquiv]

theorem shiftedMiddle_tail_half_le
    {m K : ℕ} (j : Fin m) (hj : j.1 + 1 < m) :
    K / 2 ≤ (m - j.1 - 1) * K := by
  have hblocks : 1 ≤ m - j.1 - 1 := by omega
  calc
    K / 2 ≤ K := Nat.div_le_self K 2
    _ = 1 * K := by simp
    _ ≤ (m - j.1 - 1) * K := Nat.mul_le_mul_right K hblocks

theorem shiftedSingleBlock_middle_total
    {m K : ℕ} (j : Fin m) (hj : j.1 + 1 < m) :
    ((j.1 * K + K / 2 + K) +
        ((m - j.1 - 1) * K - K / 2)) = m * K := by
  have htotal := singleBlock_middle_total K j
  have hhalf := shiftedMiddle_tail_half_le (K := K) j hj
  omega

/-- The old block-complement coordinates, rewritten in the physical order
of the complement of the shifted block. -/
def shiftedSingleBlockComplementMiddleEquiv
    {m : ℕ} (K : ℕ) (j : Fin m) (hj : j.1 + 1 < m) :
    ({p : Fin m // p ≠ j} → PauliBinaryWord K) ≃
      PauliBinaryWord (j.1 * K + K / 2) ×
        PauliBinaryWord ((m - j.1 - 1) * K - K / 2) :=
  (singleBlockComplementMiddleEquiv K j).trans
    (rotateMiddleComplementEquiv (j.1 * K)
      ((m - j.1 - 1) * K) (K / 2)
      (shiftedMiddle_tail_half_le j hj))

/-- Literal prefix/middle/tail split around the non-wrapping shifted block
`S_j = [jK+K/2, jK+K+K/2)`. -/
def shiftedSingleBlockMiddleBinaryWordEquiv
    {m : ℕ} (K : ℕ) (j : Fin m) (hj : j.1 + 1 < m) :
    PauliBinaryWord (m * K) ≃
      PauliBinaryWord K ×
        (PauliBinaryWord (j.1 * K + K / 2) ×
          PauliBinaryWord ((m - j.1 - 1) * K - K / 2)) :=
  pauliBinaryWordMiddleEquivOfEq
    (j.1 * K + K / 2) K
    ((m - j.1 - 1) * K - K / 2)
    (shiftedSingleBlock_middle_total j hj)

/-- The shifted block-tensor split is exactly the literal shifted middle
interval split, including the cyclic wrap in the untouched complement. -/
theorem shiftedSingleBlockBinaryWordEquiv_trans_middleComplement
    {m K : ℕ} (j : Fin m) (hj : j.1 + 1 < m) (hK : 0 < K) :
    (shiftedSingleBlockBinaryWordEquiv m K
        (cyclicQubitShift (m * K) (K / 2)) j).trans
        ((Equiv.refl (PauliBinaryWord K)).prodCongr
          (shiftedSingleBlockComplementMiddleEquiv K j hj)) =
      shiftedSingleBlockMiddleBinaryWordEquiv K j hj := by
  have hm : 0 < m := Nat.zero_lt_of_lt j.2
  have hN : 0 < m * K := Nat.mul_pos hm hK
  have hs : K / 2 < m * K := by
    have hhalf : K / 2 < K := Nat.div_lt_self hK (by omega)
    have hKm : K ≤ m * K := by
      simpa using Nat.mul_le_mul_right K (Nat.succ_le_iff.mpr hm)
    omega
  let shift := cyclicQubitShift (m * K) (K / 2)
  let complement := singleBlockComplementMiddleEquiv K j
  let rotate := rotateMiddleComplementEquiv (j.1 * K)
    ((m - j.1 - 1) * K) (K / 2)
    (shiftedMiddle_tail_half_le j hj)
  calc
    _ = (((permuteBinaryWord shift).symm.trans
          ((singleBlockBinaryWordEquiv m K j).trans
            ((Equiv.refl (PauliBinaryWord K)).prodCongr complement))).trans
          ((Equiv.refl (PauliBinaryWord K)).prodCongr rotate)) := by
        apply Equiv.ext
        intro x
        rfl
    _ = (((permuteBinaryWord shift).symm.trans
          (singleBlockMiddleBinaryWordEquiv K j)).trans
          ((Equiv.refl (PauliBinaryWord K)).prodCongr rotate)) := by
        rw [singleBlockBinaryWordEquiv_trans_middleComplement]
    _ = shiftedSingleBlockMiddleBinaryWordEquiv K j hj := by
      apply Equiv.ext
      intro x
      apply Prod.ext
      · funext p
        change
          (singleBlockMiddleBinaryWordEquiv K j
            ((permuteBinaryWord shift).symm x)).1 p =
          (shiftedSingleBlockMiddleBinaryWordEquiv K j hj x).1 p
        simp only [singleBlockMiddleBinaryWordEquiv,
          shiftedSingleBlockMiddleBinaryWordEquiv,
          pauliBinaryWordMiddleEquivOfEq_fst_apply,
          permuteBinaryWord_symm_apply, shift]
        apply congrArg x
        apply Fin.ext
        have hj2 : j.1 + 2 ≤ m := by omega
        have hblock : (j.1 + 2) * K ≤ m * K :=
          Nat.mul_le_mul_right K hj2
        rw [cyclicQubitShift_val_of_add_lt hN hs]
        · simp
          ring
        · simp
          ring_nf at hblock ⊢
          omega
      · apply Prod.ext
        · funext p
          let htail := shiftedMiddle_tail_half_le (K := K) j hj
          by_cases hp : p.1 < K / 2
          · let q : Fin (K / 2) := ⟨p.1, hp⟩
            let oldFinal : Fin (m * K) :=
              Fin.cast (singleBlock_middle_total K j)
                (Fin.natAdd (j.1 * K + K)
                  (Fin.cast (Nat.sub_add_cancel htail)
                    (Fin.natAdd
                      ((m - j.1 - 1) * K - K / 2) q)))
            have hpEq : p =
                Fin.cast (Nat.add_comm (K / 2) (j.1 * K))
                  (Fin.castAdd (j.1 * K) q) := by
              apply Fin.ext
              rfl
            change
              (rotateMiddleComplementEquiv (j.1 * K)
                ((m - j.1 - 1) * K) (K / 2) htail
                (singleBlockMiddleBinaryWordEquiv K j
                  ((permuteBinaryWord shift).symm x)).2).1 p =
              (shiftedSingleBlockMiddleBinaryWordEquiv K j hj x).2.1 p
            rw [hpEq, rotateMiddleComplementEquiv_fst_final]
            simp only [singleBlockMiddleBinaryWordEquiv,
              shiftedSingleBlockMiddleBinaryWordEquiv,
              pauliBinaryWordMiddleEquivOfEq_prefix_apply,
              pauliBinaryWordMiddleEquivOfEq_tail_apply,
              permuteBinaryWord_symm_apply, shift]
            change x (cyclicQubitShift (m * K) (K / 2) oldFinal) = _
            have hold : oldFinal =
                ⟨m * K - K / 2 + q.1, by omega⟩ := by
              apply Fin.ext
              simp [oldFinal]
              have htotal := singleBlock_middle_total K j
              have hsub := Nat.sub_add_cancel htail
              omega
            apply congrArg x
            rw [hold]
            apply Fin.ext
            rw [cyclicQubitShift_val_of_final_segment hN hs]
            simp [q]
          · have hge : K / 2 ≤ p.1 := Nat.le_of_not_gt hp
            change
              (rotateMiddleComplementEquiv (j.1 * K)
                ((m - j.1 - 1) * K) (K / 2) htail
                (singleBlockMiddleBinaryWordEquiv K j
                  ((permuteBinaryWord shift).symm x)).2).1 p =
              (shiftedSingleBlockMiddleBinaryWordEquiv K j hj x).2.1 p
            rw [rotateMiddleComplementEquiv_fst_apply_of_ge
              _ _ _ _ _ p hge]
            simp only [singleBlockMiddleBinaryWordEquiv,
              shiftedSingleBlockMiddleBinaryWordEquiv,
              pauliBinaryWordMiddleEquivOfEq_prefix_apply,
              permuteBinaryWord_symm_apply, shift]
            apply congrArg x
            apply Fin.ext
            rw [cyclicQubitShift_val_of_add_lt hN hs]
            · simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
              have hcancel := Nat.sub_add_cancel hge
              ring_nf
              omega
            · simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
              change (p.1 - K / 2) + K / 2 < m * K
              have hcancel := Nat.sub_add_cancel hge
              have hj1 : j.1 + 1 ≤ m := by omega
              have hblock := Nat.mul_le_mul_right K hj1
              have hhalf := Nat.div_le_self K 2
              calc
                p.1 - K / 2 + K / 2 = p.1 := hcancel
                _ < j.1 * K + K / 2 := p.2
                _ ≤ (j.1 + 1) * K := by
                  ring_nf at hblock ⊢
                  omega
                _ ≤ m * K := hblock
        · funext p
          let htail := shiftedMiddle_tail_half_le (K := K) j hj
          change
            (rotateMiddleComplementEquiv (j.1 * K)
              ((m - j.1 - 1) * K) (K / 2) htail
              (singleBlockMiddleBinaryWordEquiv K j
                ((permuteBinaryWord shift).symm x)).2).2 p =
            (shiftedSingleBlockMiddleBinaryWordEquiv K j hj x).2.2 p
          rw [rotateMiddleComplementEquiv_snd]
          simp only [singleBlockMiddleBinaryWordEquiv,
            shiftedSingleBlockMiddleBinaryWordEquiv,
            pauliBinaryWordMiddleEquivOfEq_tail_apply,
            permuteBinaryWord_symm_apply, shift]
          apply congrArg x
          apply Fin.ext
          rw [cyclicQubitShift_val_of_add_lt hN hs]
          · simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
            ring_nf
          · simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
            change j.1 * K + K + p.1 + K / 2 < m * K
            have hps : p.1 + K / 2 < (m - j.1 - 1) * K := by
              calc
                p.1 + K / 2 <
                    ((m - j.1 - 1) * K - K / 2) + K / 2 :=
                  Nat.add_lt_add_right p.2 (K / 2)
                _ = (m - j.1 - 1) * K :=
                  Nat.sub_add_cancel htail
            calc
              j.1 * K + K + p.1 + K / 2 <
                  j.1 * K + K + (m - j.1 - 1) * K := by omega
              _ = m * K := singleBlock_middle_total K j

/-- Reindexing a non-closing shifted embedded unitary by its literal shifted
middle interval gives the local unitary tensored with identity on the exact
physical complement. -/
theorem factorizationReindexUnitary_shiftedSingleBlockMiddle
    {m K : ℕ} (j : Fin m) (hj : j.1 + 1 < m) (hK : 0 < K)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    factorizationReindexUnitary
        (shiftedSingleBlockMiddleBinaryWordEquiv K j hj)
        (shiftedSingleBlockEmbeddedUnitary m K
          (cyclicQubitShift (m * K) (K / 2)) j U) =
      finiteUnitaryTensorId
        (J := PauliBinaryWord (j.1 * K + K / 2) ×
          PauliBinaryWord ((m - j.1 - 1) * K - K / 2)) U := by
  rw [← shiftedSingleBlockBinaryWordEquiv_trans_middleComplement
    j hj hK]
  rw [← factorizationReindexUnitary_trans]
  rw [factorizationReindexUnitary_shiftedSingleBlockEmbeddedUnitary]
  exact factorizationReindexUnitary_finiteUnitaryTensorId_inactive
    (shiftedSingleBlockComplementMiddleEquiv K j hj) U

/-- CP-map version of the exact non-closing shifted middle identity. -/
theorem finiteUnitaryThirdTwirlCP_shiftedSingleBlockMiddle
    {m K : ℕ} (j : Fin m) (hj : j.1 + 1 < m) (hK : 0 < K) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (shiftedSingleBlockMiddleBinaryWordEquiv K j hj))
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            shiftedSingleBlockEmbeddedUnitary m K
              (cyclicQubitShift (m * K) (K / 2)) j
              (pauliCosetCliffordUnitary K a))) =
      pauliHaarThirdTwirlTensorIdCP K
        (PauliBinaryWord (j.1 * K + K / 2) ×
          PauliBinaryWord ((m - j.1 - 1) * K - K / 2)) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold pauliHaarThirdTwirlTensorIdCP
    finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  exact factorizationReindexUnitary_shiftedSingleBlockMiddle
    j hj hK (pauliCosetCliffordUnitary K a)

/-- Reindexing an actual unshifted embedded unitary by its literal physical
middle interval gives exactly the local unitary tensored with the identity. -/
theorem factorizationReindexUnitary_singleBlockMiddle
    {m : ℕ} (K : ℕ) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    factorizationReindexUnitary (singleBlockMiddleBinaryWordEquiv K j)
        (singleBlockEmbeddedUnitary m K j U) =
      finiteUnitaryTensorId
        (J := PauliBinaryWord (j.1 * K) ×
          PauliBinaryWord ((m - j.1 - 1) * K)) U := by
  rw [← singleBlockBinaryWordEquiv_trans_middleComplement]
  rw [← factorizationReindexUnitary_trans]
  rw [factorizationReindexUnitary_singleBlockEmbeddedUnitary]
  exact factorizationReindexUnitary_finiteUnitaryTensorId_inactive
    (singleBlockComplementMiddleEquiv K j) U

/-- CP-map version of the literal unshifted middle-interval identity. -/
theorem finiteUnitaryThirdTwirlCP_singleBlockMiddle
    {m K : ℕ} (j : Fin m) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (singleBlockMiddleBinaryWordEquiv K j))
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            singleBlockEmbeddedUnitary m K j
              (pauliCosetCliffordUnitary K a))) =
      pauliHaarThirdTwirlTensorIdCP K
        (PauliBinaryWord (j.1 * K) ×
          PauliBinaryWord ((m - j.1 - 1) * K)) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold pauliHaarThirdTwirlTensorIdCP
    finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  exact factorizationReindexUnitary_singleBlockMiddle K j
    (pauliCosetCliffordUnitary K a)

/-! ## The flat old/new physical maps are the active-prefix references -/

/-- Concatenate the new half-block and untouched tail into the literal
inactive suffix after the old active prefix. -/
def choKimOldInactiveWordEquiv
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    ChoKimNewOnly K × ChoKimInactive n K i ≃
      PauliBinaryWord ((n / K) * K -
        choKimRawActiveQubitCount K i) :=
  (choKimOldInactiveSuffixSplit h hn hi).symm

def choKimOldActivePrefixPhysicalSplit
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    PauliBinaryWord ((n / K) * K) ≃
      PauliBinaryWord (choKimRawActiveQubitCount K i) ×
        PauliBinaryWord ((n / K) * K -
          choKimRawActiveQubitCount K i) :=
  binaryWordPrefixEquiv ((n / K) * K)
    (choKimRawActiveQubitCount K i)
    (h.rawActive_le_total_of_nonclosing hn hi)

theorem choKimOldFlatPhysical_trans_inactive
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    (choKimOldActiveFlatPhysicalSplit h hn hi).trans
        ((Equiv.refl
          (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
            (choKimOldInactiveWordEquiv h hn hi)) =
      choKimOldActivePrefixPhysicalSplit h hn hi := by
  let activeSplit := choKimOldActivePrefixPhysicalSplit h hn hi
  let E := choKimOldInactiveSuffixSplit h hn hi
  apply Equiv.ext
  intro x
  change Prod.map id E.symm (Prod.map id E (activeSplit x)) = activeSplit x
  rcases hsplit : activeSplit x with ⟨xa, xi⟩
  change (xa, E.symm (E xi)) = (xa, xi)
  rw [E.symm_apply_apply]

theorem ChoKimBlockCondition.rawActive_lt_total_of_nonclosing
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimRawActiveQubitCount K i < (n / K) * K := by
  have hsucc := h.rawActive_succ_le_total hn hi
  have hhalf := h.halfBlock_pos
  rw [choKimRawActiveQubitCount_succ] at hsucc
  omega

theorem ChoKimBlockCondition.oldFlatPhysical_eq_activePrefix
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimOldActiveFlatPhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K i)
          (ChoKimNewOnly K × ChoKimInactive n K i)) =
      pauliActivePrefixHaarCP ((n / K) * K) K i := by
  classical
  let flat := choKimOldActiveFlatPhysicalSplit h hn hi
  let inactive := choKimOldInactiveWordEquiv h hn hi
  let activeSplit := choKimOldActivePrefixPhysicalSplit h hn hi
  let Phi := pauliHaarThirdTwirlTensorIdCP
    (choKimRawActiveQubitCount K i)
    (ChoKimNewOnly K × ChoKimInactive n K i)
  have hcount := h.activeQubitCount_eq_raw_of_nonclosing hn hi
  have hnotFull :
      choKimActiveQubitCount ((n / K) * K) K i ≠ (n / K) * K := by
    rw [hcount]
    exact ne_of_lt (h.rawActive_lt_total_of_nonclosing hn hi)
  have hactive : pauliActivePrefixHaarCP ((n / K) * K) K i =
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr activeSplit).symm
        (pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K i)
          (PauliBinaryWord ((n / K) * K -
            choKimRawActiveQubitCount K i))) := by
    have hle := h.rawActive_le_total_of_nonclosing hn hi
    let qActive : {q : ℕ // q ≤ (n / K) * K} :=
      ⟨choKimActiveQubitCount ((n / K) * K) K i,
        choKimActiveQubitCount_le ((n / K) * K) K i⟩
    let qRaw : {q : ℕ // q ≤ (n / K) * K} :=
      ⟨choKimRawActiveQubitCount K i, hle⟩
    have hq : qActive = qRaw := by
      apply Subtype.ext
      exact hcount
    have htransport := congrArg
      (fun q : {q : ℕ // q ≤ (n / K) * K} ↦
        CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr
            (binaryWordPrefixEquiv ((n / K) * K) q.1 q.2)).symm
          (pauliHaarThirdTwirlTensorIdCP q.1
            (PauliBinaryWord ((n / K) * K - q.1)))) hq
    unfold pauliActivePrefixHaarCP
    rw [dif_neg hnotFull]
    unfold choKimActiveBinaryWordEquiv
    simp only [tripleIndexCongr_symm_eq] at htransport ⊢
    simpa [qActive, qRaw, activeSplit,
      choKimOldActivePrefixPhysicalSplit] using htransport
  have hinactive :
      CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr
            ((Equiv.refl
              (PauliBinaryWord
                (choKimRawActiveQubitCount K i))).prodCongr inactive))
          Phi =
        pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K i)
          (PauliBinaryWord ((n / K) * K -
            choKimRawActiveQubitCount K i)) := by
    dsimp only [Phi, inactive]
    exact finiteUnitaryThirdTwirlTensorIdCP_reindex_inactive
      (choKimOldInactiveWordEquiv h hn hi)
      (pauliCosetCliffordUnitary
        (choKimRawActiveQubitCount K i))
  have hsplit : flat.trans
      ((Equiv.refl
        (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
          inactive) = activeSplit := by
    dsimp only [flat, inactive, activeSplit]
    exact choKimOldFlatPhysical_trans_inactive h hn hi
  have hcomp :
      ((Equiv.refl
        (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
          inactive).trans activeSplit.symm = flat.symm := by
    rw [← hsplit]
    apply Equiv.ext
    rintro ⟨xa, xi⟩
    simp
  have hcomp3 :
      (tripleIndexCongr
        ((Equiv.refl
          (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
            inactive)).trans
          (tripleIndexCongr activeSplit).symm =
        (tripleIndexCongr flat).symm := by
    apply Equiv.ext
    rintro ⟨x₀, x₁, x₂⟩
    change
      (((Equiv.refl
        (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
          inactive).trans activeSplit.symm x₀,
       ((Equiv.refl
        (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
          inactive).trans activeSplit.symm x₁,
       ((Equiv.refl
        (PauliBinaryWord (choKimRawActiveQubitCount K i))).prodCongr
          inactive).trans activeSplit.symm x₂) =
        (flat.symm x₀, flat.symm x₁, flat.symm x₂)
    rw [hcomp]
  rw [hactive, ← hinactive,
    CompletelyPositiveMap.reindexEquiv_trans, hcomp3]

/-! ## Literal support normalizations for the next reference and gate -/

theorem choKimNewActivePhysicalSplit_eq_literal
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimNewActivePhysicalSplit h hn hi =
      choKimNewActiveLiteralPhysicalSplit h hn hi := by
  have hsub := h.rawActive_sub_half_add (i := i)
  have hhalf := h.halfBlock_add_halfBlock
  have hsucc := choKimRawActiveQubitCount_succ K i
  have hpart := h.nonclosing_partition_total hn hi
  have htail := h.oldInactive_length hn hi
  let F := (choKimForwardABCEquiv (i := i) h).prodCongr
    (Equiv.refl (ChoKimInactive n K i))
  have hliteral :
      (choKimNewActiveLiteralPhysicalSplit h hn hi).trans F =
        choKimForwardABCRSplit h hn hi := by
    apply Equiv.ext
    intro x
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · funext p
          simp [F, choKimNewActiveLiteralPhysicalSplit,
            choKimForwardABCRSplit,
            choKimOldNewInactivePhysicalSplit,
            choKimOldActiveFlatPhysicalSplitCore,
            choKimOldInactiveSuffixSplit,
            choKimForwardABCEquiv, choKimForwardABEquiv]
          change x _ = x _
          apply congrArg x
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
        · funext p
          simp [F, choKimNewActiveLiteralPhysicalSplit,
            choKimForwardABCRSplit,
            choKimOldNewInactivePhysicalSplit,
            choKimOldActiveFlatPhysicalSplitCore,
            choKimOldInactiveSuffixSplit,
            choKimForwardABCEquiv, choKimForwardABEquiv]
          change x _ = x _
          apply congrArg x
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
      · funext p
        simp [F, choKimNewActiveLiteralPhysicalSplit,
          choKimForwardABCRSplit,
          choKimOldNewInactivePhysicalSplit,
          choKimOldActiveFlatPhysicalSplitCore,
          choKimOldInactiveSuffixSplit,
          choKimForwardABCEquiv, choKimForwardABEquiv]
        change x _ = x _
        apply congrArg x
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
        omega
    · funext p
      simp [F, choKimNewActiveLiteralPhysicalSplit,
        choKimForwardABCRSplit,
        choKimOldNewInactivePhysicalSplit,
        choKimOldActiveFlatPhysicalSplitCore,
        choKimOldInactiveSuffixSplit,
        choKimForwardABCEquiv, choKimForwardABEquiv]
      change x _ = x _
      apply congrArg x
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
      omega
  apply Equiv.ext
  intro x
  apply F.injective
  have hp := DFunLike.congr_fun
    (choKimForwardNewPhysical_factor h hn hi) x
  have hl := DFunLike.congr_fun hliteral x
  exact hp.trans hl.symm

theorem choKimMiddleGateFlatPhysicalSplit_eq_literal
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimMiddleGateFlatPhysicalSplit h hn hi =
      (pauliBinaryWordMiddleEquivOfEq
        (choKimRawActiveQubitCount K i - K / 2) K
        ((n / K) * K - choKimRawActiveQubitCount K (i + 1))
        (h.nonclosing_middle_tail_total hn hi)) := by
  have hsub := h.rawActive_sub_half_add (i := i)
  have hhalf := h.halfBlock_add_halfBlock
  have hsucc := choKimRawActiveQubitCount_succ K i
  have hpart := h.nonclosing_partition_total hn hi
  have htail := h.oldInactive_length hn hi
  let assocBack :=
    (Equiv.prodAssoc (PauliBinaryWord K) (ChoKimOldOnly K i)
      (ChoKimInactive n K i)).symm
  let Fgate := (choKimForwardGateCoordinateEquiv (i := i) h).prodCongr
    (Equiv.refl (ChoKimInactive n K i))
  let G := assocBack.trans Fgate
  have hphysical :
      (choKimMiddleGateFlatPhysicalSplit h hn hi).trans G =
        choKimForwardABCRSplit h hn hi := by
    dsimp only [G, assocBack, Fgate]
    rw [← Equiv.trans_assoc,
      choKimMiddleGateFlatPhysicalSplit_assoc h hn hi,
      choKimForwardGatePhysical_factor h hn hi]
  have hliteral :
      (pauliBinaryWordMiddleEquivOfEq
          (choKimRawActiveQubitCount K i - K / 2) K
          ((n / K) * K - choKimRawActiveQubitCount K (i + 1))
          (h.nonclosing_middle_tail_total hn hi)).trans G =
        choKimForwardABCRSplit h hn hi := by
    apply Equiv.ext
    intro x
    apply Prod.ext
    · apply Prod.ext
      · apply Prod.ext
        · funext p
          simp [G, assocBack, Fgate,
            choKimForwardABCRSplit,
            choKimOldNewInactivePhysicalSplit,
            choKimOldActiveFlatPhysicalSplitCore,
            choKimOldInactiveSuffixSplit,
            choKimForwardGateCoordinateEquiv, choKimForwardBCEquiv,
            choKimForwardABEquiv, bcaOneReplicaEquivABC]
          change x _ = x _
          apply congrArg x
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
        · funext p
          simp [G, assocBack, Fgate,
            choKimForwardABCRSplit,
            choKimOldNewInactivePhysicalSplit,
            choKimOldActiveFlatPhysicalSplitCore,
            choKimOldInactiveSuffixSplit,
            choKimForwardGateCoordinateEquiv, choKimForwardBCEquiv,
            choKimForwardABEquiv, bcaOneReplicaEquivABC]
          change x _ = x _
          apply congrArg x
          apply Fin.ext
          simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
      · funext p
        simp [G, assocBack, Fgate,
          choKimForwardABCRSplit,
          choKimOldNewInactivePhysicalSplit,
          choKimOldActiveFlatPhysicalSplitCore,
          choKimOldInactiveSuffixSplit,
          choKimForwardGateCoordinateEquiv, choKimForwardBCEquiv,
          choKimForwardABEquiv, bcaOneReplicaEquivABC]
        change x _ = x _
        apply congrArg x
        apply Fin.ext
        simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd,
          Fin.val_addNat]
        omega
    · funext p
      simp [G, assocBack, Fgate,
        choKimForwardABCRSplit,
        choKimOldNewInactivePhysicalSplit,
        choKimOldActiveFlatPhysicalSplitCore,
        choKimOldInactiveSuffixSplit,
        choKimForwardGateCoordinateEquiv, choKimForwardBCEquiv,
        choKimForwardABEquiv, bcaOneReplicaEquivABC]
      change x _ = x _
      apply congrArg x
      apply Fin.ext
      simp only [Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd]
      omega
  apply Equiv.ext
  intro x
  apply G.injective
  have hp := DFunLike.congr_fun hphysical x
  have hl := DFunLike.congr_fun hliteral x
  exact hp.trans hl.symm

theorem choKimNewActiveLiteralPhysicalSplit_eq_prefix
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    choKimNewActiveLiteralPhysicalSplit h hn hi =
      binaryWordPrefixEquiv ((n / K) * K)
        (choKimRawActiveQubitCount K (i + 1))
        (h.rawActive_succ_le_total hn hi) := by
  apply Equiv.ext
  intro x
  apply Prod.ext
  · funext p
    simp only [choKimNewActiveLiteralPhysicalSplit, Equiv.trans_apply,
      pauliBinaryWordAddEquiv_fst_apply, pauliBinaryWordCongr_apply,
      binaryWordPrefixEquiv_fst_apply]
  · funext p
    simp only [choKimNewActiveLiteralPhysicalSplit, Equiv.trans_apply,
      pauliBinaryWordAddEquiv_snd_apply, pauliBinaryWordCongr_apply,
      binaryWordPrefixEquiv_snd_apply]

/-- A literal prefix Haar twirl is the active-prefix reference, including
the endpoint where the inactive tail has length zero. -/
theorem pauliHaarThirdTwirlTensorIdCP_prefix_eq_active
    {N K t q : ℕ} (hq : q ≤ N)
    (hcount : choKimActiveQubitCount N K t = q) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (binaryWordPrefixEquiv N q hq)).symm
        (pauliHaarThirdTwirlTensorIdCP q (PauliBinaryWord (N - q))) =
      pauliActivePrefixHaarCP N K t := by
  classical
  subst q
  by_cases hfull : choKimActiveQubitCount N K t = N
  · rw [pauliActivePrefixHaarCP_eq_full hfull]
    let qActive : {q : ℕ // q ≤ N} :=
      ⟨choKimActiveQubitCount N K t, hq⟩
    let qFull : {q : ℕ // q ≤ N} := ⟨N, le_rfl⟩
    have hqFull : qActive = qFull := by
      apply Subtype.ext
      exact hfull
    have htransport := congrArg
      (fun q : {q : ℕ // q ≤ N} ↦
        CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr
            (binaryWordPrefixEquiv N q.1 q.2)).symm
          (pauliHaarThirdTwirlTensorIdCP q.1
            (PauliBinaryWord (N - q.1)))) hqFull
    have hfullMap :=
      pauliHaarThirdTwirlTensorIdCP_reindex_fullPrefix_exact N
    simpa [qActive, qFull] using htransport.trans hfullMap
  · unfold pauliActivePrefixHaarCP
    rw [dif_neg hfull]
    unfold choKimActiveBinaryWordEquiv
    simpa only [tripleIndexCongr_symm_eq]

theorem ChoKimBlockCondition.newPhysical_eq_activePrefix
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimNewActivePhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP
          (choKimRawActiveQubitCount K (i + 1))
          (ChoKimInactive n K i)) =
      pauliActivePrefixHaarCP ((n / K) * K) K (i + 1) := by
  rw [choKimNewActivePhysicalSplit_eq_literal h hn hi,
    choKimNewActiveLiteralPhysicalSplit_eq_prefix h hn hi]
  simpa only [ChoKimInactive] using
    pauliHaarThirdTwirlTensorIdCP_prefix_eq_active
      (h.rawActive_succ_le_total hn hi)
      (h.activeQubitCount_succ_eq_raw_of_nonclosing hn hi)

/-! ## The physical middle gate is the selected canonical gate -/

theorem ChoKimBlockCondition.middleGatePhysical_eq_unshifted
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) (j : Fin (n / K))
    (hij : i + 1 = 2 * j.1) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimMiddleGateFlatPhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP K
          (ChoKimOldOnly K i × ChoKimInactive n K i)) =
      finiteUnitaryThirdTwirlCP
        (fun a : PauliCosetCliffordEnsemble K ↦
          singleBlockEmbeddedUnitary (n / K) K j
            (pauliCosetCliffordUnitary K a)) := by
  classical
  have hhalf := h.halfBlock_add_halfBlock
  have hraw :
      choKimRawActiveQubitCount K i = j.1 * K + K / 2 := by
    unfold choKimRawActiveQubitCount
    calc
      K + i * (K / 2) =
          (K / 2 + K / 2) + i * (K / 2) := by rw [hhalf]
      _ = (i + 1) * (K / 2) + K / 2 := by ring
      _ = (2 * j.1) * (K / 2) + K / 2 := by rw [hij]
      _ = j.1 * (K / 2 + K / 2) + K / 2 := by ring
      _ = j.1 * K + K / 2 := by rw [hhalf]
  have ha :
      choKimRawActiveQubitCount K i - K / 2 = j.1 * K := by
    rw [hraw, Nat.add_sub_cancel]
  have hsucc :
      choKimRawActiveQubitCount K (i + 1) = (j.1 + 1) * K := by
    unfold choKimRawActiveQubitCount
    rw [hij]
    calc
      K + 2 * j.1 * (K / 2) =
          j.1 * (K / 2 + K / 2) + K := by ring
      _ = j.1 * K + K := by rw [hhalf]
      _ = (j.1 + 1) * K := by ring
  have htail :
      (n / K) * K - choKimRawActiveQubitCount K (i + 1) =
        ((n / K) - j.1 - 1) * K := by
    rw [hsucc, ← Nat.sub_mul]
    congr 1
  rw [choKimMiddleGateFlatPhysicalSplit_eq_literal h hn hi]
  unfold ChoKimOldOnly ChoKimInactive
  let D := {p : ℕ × ℕ // (p.1 + K) + p.2 = (n / K) * K}
  let rawD : D :=
    ⟨(choKimRawActiveQubitCount K i - K / 2,
        (n / K) * K - choKimRawActiveQubitCount K (i + 1)),
      h.nonclosing_middle_tail_total hn hi⟩
  let canonD : D :=
    ⟨(j.1 * K, ((n / K) - j.1 - 1) * K),
      singleBlock_middle_total K j⟩
  have hd : rawD = canonD := by
    apply Subtype.ext
    apply Prod.ext
    · exact ha
    · exact htail
  have htransport := congrArg
    (fun d : D ↦
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (pauliBinaryWordMiddleEquivOfEq d.1.1 K d.1.2 d.2)).symm
        (pauliHaarThirdTwirlTensorIdCP K
          (PauliBinaryWord d.1.1 × PauliBinaryWord d.1.2))) hd
  calc
    _ = CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr
            (singleBlockMiddleBinaryWordEquiv K j)).symm
          (pauliHaarThirdTwirlTensorIdCP K
            (PauliBinaryWord (j.1 * K) ×
              PauliBinaryWord (((n / K) - j.1 - 1) * K))) := by
        simpa [D, rawD, canonD, singleBlockMiddleBinaryWordEquiv] using
          htransport
    _ = _ := by
      rw [← finiteUnitaryThirdTwirlCP_singleBlockMiddle (K := K) j]
      exact CompletelyPositiveMap.reindexEquiv_symm_cancel _ _

/-- In an odd-selector non-closing step, the literal physical middle gate is
exactly the canonical shifted block gate.  The untouched coordinates are
transported together with their proof-indexed lengths. -/
theorem ChoKimBlockCondition.middleGatePhysical_eq_shifted
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) (j : Fin (n / K))
    (hij : i + 1 = 2 * j.1 + 1) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (choKimMiddleGateFlatPhysicalSplit h hn hi)).symm
        (pauliHaarThirdTwirlTensorIdCP K
          (ChoKimOldOnly K i × ChoKimInactive n K i)) =
      finiteUnitaryThirdTwirlCP
        (fun a : PauliCosetCliffordEnsemble K ↦
          shiftedSingleBlockEmbeddedUnitary (n / K) K
            (cyclicQubitShift ((n / K) * K) (K / 2)) j
            (pauliCosetCliffordUnitary K a)) := by
  classical
  have hj : j.1 + 1 < n / K := by omega
  have hiEven : i = 2 * j.1 := by omega
  have hhalf := h.halfBlock_add_halfBlock
  have hraw :
      choKimRawActiveQubitCount K i = (j.1 + 1) * K := by
    unfold choKimRawActiveQubitCount
    rw [hiEven]
    calc
      K + 2 * j.1 * (K / 2) =
          j.1 * (K / 2 + K / 2) + K := by ring
      _ = j.1 * K + K := by rw [hhalf]
      _ = (j.1 + 1) * K := by ring
  have ha :
      choKimRawActiveQubitCount K i - K / 2 =
        j.1 * K + K / 2 := by
    rw [hraw, show (j.1 + 1) * K = j.1 * K + K by ring]
    omega
  have htail :
      (n / K) * K - choKimRawActiveQubitCount K (i + 1) =
        ((n / K) - j.1 - 1) * K - K / 2 := by
    have hp := h.nonclosing_middle_tail_total hn hi
    have hs := shiftedSingleBlock_middle_total (K := K) j hj
    rw [ha] at hp
    exact Nat.add_left_cancel (hp.trans hs.symm)
  rw [choKimMiddleGateFlatPhysicalSplit_eq_literal h hn hi]
  unfold ChoKimOldOnly ChoKimInactive
  let D := {p : ℕ × ℕ // (p.1 + K) + p.2 = (n / K) * K}
  let rawD : D :=
    ⟨(choKimRawActiveQubitCount K i - K / 2,
        (n / K) * K - choKimRawActiveQubitCount K (i + 1)),
      h.nonclosing_middle_tail_total hn hi⟩
  let shiftedD : D :=
    ⟨(j.1 * K + K / 2,
        ((n / K) - j.1 - 1) * K - K / 2),
      shiftedSingleBlock_middle_total (K := K) j hj⟩
  have hd : rawD = shiftedD := by
    apply Subtype.ext
    apply Prod.ext
    · exact ha
    · exact htail
  have htransport := congrArg
    (fun d : D ↦
      CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (pauliBinaryWordMiddleEquivOfEq d.1.1 K d.1.2 d.2)).symm
        (pauliHaarThirdTwirlTensorIdCP K
          (PauliBinaryWord d.1.1 × PauliBinaryWord d.1.2))) hd
  calc
    _ = CompletelyPositiveMap.reindexEquiv
          (tripleIndexCongr
            (shiftedSingleBlockMiddleBinaryWordEquiv K j hj)).symm
          (pauliHaarThirdTwirlTensorIdCP K
            (PauliBinaryWord (j.1 * K + K / 2) ×
              PauliBinaryWord
                (((n / K) - j.1 - 1) * K - K / 2))) := by
        simpa [D, rawD, shiftedD,
          shiftedSingleBlockMiddleBinaryWordEquiv] using htransport
    _ = _ := by
      rw [← finiteUnitaryThirdTwirlCP_shiftedSingleBlockMiddle
        (K := K) j hj h.block_pos]
      exact CompletelyPositiveMap.reindexEquiv_symm_cancel _ _

/-! ## Canonical non-closing relative-CP steps -/

/-- The factorized forward estimate, flattened to the exact old-active,
shifted-gate, and new-active physical maps. -/
theorem ChoKimBlockCondition.relativeCPApproximation_forwardPhysicalStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) (j : Fin (n / K))
    (hij : i + 1 = 2 * j.1 + 1) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (CompletelyPositiveMap.comp
        (pauliActivePrefixHaarCP ((n / K) * K) K i)
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            shiftedSingleBlockEmbeddedUnitary (n / K) K
              (cyclicQubitShift ((n / K) * K) (K / 2)) j
              (pauliCosetCliffordUnitary K a)))).toLinearMap
      (pauliActivePrefixHaarCP
        ((n / K) * K) K (i + 1)).toLinearMap := by
  have hstep := h.relativeCPApproximation_forwardFactorizedStep hn hi
  rw [h.forwardAB_eq_physicalNested hn hi,
    h.oldNested_eq_flatPhysical hn hi,
    h.oldFlatPhysical_eq_activePrefix hn hi,
    h.forwardBC_eq_physicalNested hn hi,
    h.gateNested_eq_flatPhysical hn hi,
    h.middleGatePhysical_eq_shifted hn hi j hij,
    h.forwardABC_eq_physical hn hi,
    h.newPhysical_eq_activePrefix hn hi] at hstep
  exact hstep

/-- The factorized reverse estimate, flattened to the exact new unshifted
gate, old-active map, and new-active physical map. -/
theorem ChoKimBlockCondition.relativeCPApproximation_reversePhysicalStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) (j : Fin (n / K))
    (hij : i + 1 = 2 * j.1) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            singleBlockEmbeddedUnitary (n / K) K j
              (pauliCosetCliffordUnitary K a)))
        (pauliActivePrefixHaarCP ((n / K) * K) K i)).toLinearMap
      (pauliActivePrefixHaarCP
        ((n / K) * K) K (i + 1)).toLinearMap := by
  have hstep := h.relativeCPApproximation_reverseFactorizedStep hn hi
  rw [h.reverseAB_eq_physicalNested hn hi,
    h.gateNested_eq_flatPhysical hn hi,
    h.middleGatePhysical_eq_unshifted hn hi j hij,
    h.reverseBC_eq_physicalNested hn hi,
    h.oldNested_eq_flatPhysical hn hi,
    h.oldFlatPhysical_eq_activePrefix hn hi,
    h.reverseABC_eq_physical hn hi,
    h.newPhysical_eq_activePrefix hn hi] at hstep
  exact hstep

/-! ## Single transport to the literal circuit basis -/

/-- Forward non-closing step in the literal `Fin (2^n)` circuit basis. -/
theorem ChoKimBlockCondition.relativeCPApproximation_forwardLiteralStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) (j : Fin (n / K))
    (hij : i + 1 = 2 * j.1 + 1) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (CompletelyPositiveMap.comp
        (choKimActiveHaarCP h.block_dvd i)
        (finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
            h.block_dvd j))).toLinearMap
      (choKimActiveHaarCP h.block_dvd (i + 1)).toLinearMap := by
  classical
  let e := tripleIndexCongr
    (choKimLiteralBinaryWordEquivFin h.block_dvd)
  have hstep := h.relativeCPApproximation_forwardPhysicalStep
    hn hi j hij
  have hfin := relativeCPApproximation_reindexEquiv e _ _ _ hstep
  rw [CompletelyPositiveMap.reindexEquiv_comp] at hfin
  have hU :
      (fun a : PauliCosetCliffordEnsemble K ↦
        shiftedSingleBlockEmbeddedUnitary (n / K) K
          (cyclicQubitShift ((n / K) * K) (K / 2)) j
          (pauliCosetCliffordUnitary K a)) =
        choKimCanonicalShiftedBlockUnitary n K j := by
    funext a
    rfl
  have hgate :
      CompletelyPositiveMap.reindexEquiv e
          (finiteUnitaryThirdTwirlCP
            (fun a : PauliCosetCliffordEnsemble K ↦
              shiftedSingleBlockEmbeddedUnitary (n / K) K
                (cyclicQubitShift ((n / K) * K) (K / 2)) j
                (pauliCosetCliffordUnitary K a))) =
        finiteUnitaryThirdTwirlCP
          (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
            h.block_dvd j) := by
    rw [hU]
    dsimp only [e]
    exact (finiteUnitaryThirdTwirlCP_choKimShiftedGate_eq_reindex_direct
      h.block_dvd j).symm
  rw [hgate] at hfin
  simpa only [e, choKimActiveHaarCP] using hfin

/-- Reverse non-closing step in the literal `Fin (2^n)` circuit basis. -/
theorem ChoKimBlockCondition.relativeCPApproximation_reverseLiteralStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) (j : Fin (n / K))
    (hij : i + 1 = 2 * j.1) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (CompletelyPositiveMap.comp
        (finiteUnitaryThirdTwirlCP
          (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin
            h.block_dvd j))
        (choKimActiveHaarCP h.block_dvd i)).toLinearMap
      (choKimActiveHaarCP h.block_dvd (i + 1)).toLinearMap := by
  classical
  let e := tripleIndexCongr
    (choKimLiteralBinaryWordEquivFin h.block_dvd)
  have hstep := h.relativeCPApproximation_reversePhysicalStep
    hn hi j hij
  have hfin := relativeCPApproximation_reindexEquiv e _ _ _ hstep
  rw [CompletelyPositiveMap.reindexEquiv_comp] at hfin
  rw [← finiteUnitaryThirdTwirlCP_choKimBlockGate_eq_reindex_direct
    h.block_dvd j] at hfin
  simpa only [e, choKimActiveHaarCP] using hfin

/-! ## Public parity-selected non-closing step -/

/-- Every non-closing edge of the literal alternating Cho--Kim path compares
the tag-ordered composition of the current active Haar reference and the
actual next gate to the next active Haar reference. -/
theorem ChoKimBlockCondition.relativeCPApproximation_nonclosingActiveHaarStep
    {n K i : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (hi : i < 2 * (n / K) - 2) :
    RelativeCPApproximation (choKimFThree (choKimOverlapDimension K))
      (if (alternatingCPGateAt
          (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1)).1 then
        CompletelyPositiveMap.comp
          (alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1)).2
          (choKimActiveHaarCP h.block_dvd i)
       else
        CompletelyPositiveMap.comp
          (choKimActiveHaarCP h.block_dvd i)
          (alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1)).2
      ).toLinearMap
      (choKimActiveHaarCP h.block_dvd (i + 1)).toLinearMap := by
  rcases Nat.even_or_odd' (i + 1) with ⟨q, hq | hq⟩
  · let j : Fin (n / K) := ⟨q, by omega⟩
    have hij : i + 1 = 2 * j.1 := by
      simpa only [j] using hq
    have hgateAt :
        alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1) =
          (true, finiteUnitaryThirdTwirlCP
            (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin
              h.block_dvd j)) := by
      unfold choKimAlternatingThirdTwirlCPGates
      rw [hij]
      exact alternatingCPGateAt_even _ _ j
    simpa [hgateAt] using
      h.relativeCPApproximation_reverseLiteralStep hn hi j hij
  · let j : Fin (n / K) := ⟨q, by omega⟩
    have hij : i + 1 = 2 * j.1 + 1 := by
      simpa only [j] using hq
    have hgateAt :
        alternatingCPGateAt
            (choKimAlternatingThirdTwirlCPGates h.block_dvd) (i + 1) =
          (false, finiteUnitaryThirdTwirlCP
            (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin
              h.block_dvd j)) := by
      unfold choKimAlternatingThirdTwirlCPGates
      rw [hij]
      exact alternatingCPGateAt_odd _ _ j
    simpa [hgateAt] using
      h.relativeCPApproximation_forwardLiteralStep hn hi j hij

end

end TomographyOracleCore
