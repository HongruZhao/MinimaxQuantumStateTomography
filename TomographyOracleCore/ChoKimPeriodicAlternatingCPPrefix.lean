import TomographyOracleCore.ChoKimPeriodicThirdTwirlCPCommutation
import TomographyOracleCore.RelativeDesignConstructiveGluingIteration
import Mathlib.Data.List.GetD

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance choKimAlternatingSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choKimAlternatingStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Explicit alternating spanning-path prefix

The gate list is `A₀,B₀,A₁,B₁,...`.  An `A` gate is composed on
the left and a `B` gate on the right.  Thus every prefix is connected along
the cycle with its closing edge removed, while the final map has the exact
physical layer order.
-/

/-- One mixed left/right composition step. -/
def mixedCPGateStep
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (acc : A →CP A) (gate : Bool × (A →CP A)) : A →CP A :=
  if gate.1 then CompletelyPositiveMap.comp gate.2 acc
  else CompletelyPositiveMap.comp acc gate.2

/-- Reverse (left-growing) product of a list of CP endomorphisms. -/
def reverseCPListFold
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : List (A →CP A) → A →CP A
  | [] => CompletelyPositiveMap.identity
  | Phi :: rest => CompletelyPositiveMap.comp (reverseCPListFold rest) Phi

/-- Forward (right-growing) product of a list of CP endomorphisms. -/
def forwardCPListFold
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] : List (A →CP A) → A →CP A
  | [] => CompletelyPositiveMap.identity
  | Phi :: rest => CompletelyPositiveMap.comp Phi (forwardCPListFold rest)

/-- Alternating tagged gate list attached to two finite layers. -/
def alternatingCPGateList
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {m : ℕ} (U S : Fin m → A →CP A) :
    List (Bool × (A →CP A)) :=
  (List.ofFn fun j ↦ (U j, S j)).flatMap
    (fun p ↦ [(true, p.1), (false, p.2)])

@[simp] theorem length_alternatingCPGateList
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    {m : ℕ} (U S : Fin m → A →CP A) :
    (alternatingCPGateList U S).length = 2 * m := by
  simpa [alternatingCPGateList, List.length_flatMap, List.sum_ofFn,
    Nat.mul_comm]

/-- Prefix after the first `i+1` alternating gates. -/
def alternatingCPPrefix
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (gates : List (Bool × (A →CP A))) (i : ℕ) : A →CP A :=
  (gates.take (i + 1)).foldl mixedCPGateStep
    CompletelyPositiveMap.identity

/-- Total next-gate selector; the default is used only outside the finite
constructive-iteration range. -/
def alternatingCPGateAt
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (gates : List (Bool × (A →CP A))) (i : ℕ) :
    Bool × (A →CP A) :=
  gates.getD i (false, CompletelyPositiveMap.identity)

/-- Exact prefix recurrence used by constructive mixed gluing. -/
theorem alternatingCPPrefix_succ
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (gates : List (Bool × (A →CP A))) (i : ℕ)
    (hi : i + 1 < gates.length) :
    alternatingCPPrefix gates (i + 1) =
      if (alternatingCPGateAt gates (i + 1)).1 then
        CompletelyPositiveMap.comp
          (alternatingCPGateAt gates (i + 1)).2
          (alternatingCPPrefix gates i)
      else CompletelyPositiveMap.comp
          (alternatingCPPrefix gates i)
          (alternatingCPGateAt gates (i + 1)).2 := by
  unfold alternatingCPPrefix alternatingCPGateAt
  rw [← List.take_concat_get' gates (i + 1) hi]
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil]
  rw [List.getD_eq_getElem gates _ hi]
  rfl

/-- General accumulator invariant for an alternating list of gate pairs. -/
theorem foldl_mixedCPGateStep_flatMap_pairs
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (acc : A →CP A) (pairs : List ((A →CP A) × (A →CP A))) :
    (pairs.flatMap (fun p ↦ [(true, p.1), (false, p.2)])).foldl
        mixedCPGateStep acc =
      CompletelyPositiveMap.comp
        (reverseCPListFold (pairs.map Prod.fst))
        (CompletelyPositiveMap.comp acc
          (forwardCPListFold (pairs.map Prod.snd))) := by
  induction pairs generalizing acc with
  | nil => simp [reverseCPListFold, forwardCPListFold]
  | cons p rest ih =>
      rw [List.flatMap_cons]
      rw [List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil, mixedCPGateStep]
      rw [ih]
      simp only [List.map_cons, reverseCPListFold, forwardCPListFold]
      simp only [Bool.true_eq, if_true, Bool.false_eq_true, if_false,
        CompletelyPositiveMap.comp_assoc]

/-- The two list folds coincide with the concrete finite third-twirl CP
folds on a `Fin m` family. -/
theorem reverseCPListFold_ofFn_finiteThirdTwirl
    {D m : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) :
    reverseCPListFold
        (List.ofFn fun j ↦ finiteUnitaryThirdTwirlCP (U j)) =
      reverseFinThirdTwirlCPFold m U := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, reverseCPListFold, reverseFinThirdTwirlCPFold]
      rw [ih (fun j ↦ U j.succ)]

theorem forwardCPListFold_ofFn_finiteThirdTwirl
    {D m : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) :
    forwardCPListFold
        (List.ofFn fun j ↦ finiteUnitaryThirdTwirlCP (U j)) =
      forwardFinThirdTwirlCPFold m U := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [List.ofFn_succ, forwardCPListFold, forwardFinThirdTwirlCPFold]
      rw [ih (fun j ↦ U j.succ)]

/-- The full alternating prefix is the reverse unshifted fold followed by
the forward shifted fold. -/
theorem alternatingCPPrefix_final_finiteThirdTwirl
    {D m : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (hm : 0 < m)
    (U S : Fin m → E → Matrix.unitaryGroup (Fin D) ℂ) :
    alternatingCPPrefix
        (alternatingCPGateList
          (fun j ↦ finiteUnitaryThirdTwirlCP (U j))
          (fun j ↦ finiteUnitaryThirdTwirlCP (S j)))
        (2 * m - 1) =
      CompletelyPositiveMap.comp
        (reverseFinThirdTwirlCPFold m U)
        (forwardFinThirdTwirlCPFold m S) := by
  let pairs := List.ofFn fun j : Fin m ↦
    (finiteUnitaryThirdTwirlCP (U j), finiteUnitaryThirdTwirlCP (S j))
  have hfst : pairs.map Prod.fst =
      List.ofFn (fun j ↦ finiteUnitaryThirdTwirlCP (U j)) := by
    simp [pairs, Function.comp_def]
  have hsnd : pairs.map Prod.snd =
      List.ofFn (fun j ↦ finiteUnitaryThirdTwirlCP (S j)) := by
    simp [pairs, Function.comp_def]
  have hlen : (alternatingCPGateList
      (fun j ↦ finiteUnitaryThirdTwirlCP (U j))
      (fun j ↦ finiteUnitaryThirdTwirlCP (S j))).length = 2 * m :=
    length_alternatingCPGateList _ _
  have hindex : 2 * m - 1 + 1 = 2 * m := by omega
  have htake : (alternatingCPGateList
      (fun j ↦ finiteUnitaryThirdTwirlCP (U j))
      (fun j ↦ finiteUnitaryThirdTwirlCP (S j))).take (2 * m) =
      alternatingCPGateList
        (fun j ↦ finiteUnitaryThirdTwirlCP (U j))
        (fun j ↦ finiteUnitaryThirdTwirlCP (S j)) := by
    rw [← hlen, List.take_length]
  unfold alternatingCPPrefix
  rw [hindex, htake]
  unfold alternatingCPGateList
  change (pairs.flatMap
      (fun p ↦ [(true, p.1), (false, p.2)])).foldl
      mixedCPGateStep CompletelyPositiveMap.identity = _
  rw [foldl_mixedCPGateStep_flatMap_pairs]
  simp only [CompletelyPositiveMap.identity_comp]
  rw [hfst, hsnd, reverseCPListFold_ofFn_finiteThirdTwirl,
    forwardCPListFold_ofFn_finiteThirdTwirl]

/-- Concrete final-prefix identity for the periodic Cho--Kim circuit. -/
theorem alternatingCPPrefix_choKim_eq_literal
    {n K : ℕ} (hdiv : K ∣ n) (hm : 0 < n / K) :
    alternatingCPPrefix
        (alternatingCPGateList
          (fun j ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j))
          (fun j ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j)))
        (2 * (n / K) - 1) =
      finiteUnitaryThirdTwirlCP
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) := by
  rw [alternatingCPPrefix_final_finiteThirdTwirl hm]
  rw [forwardFinThirdTwirlCPFold_choKimShifted_eq_reverse]
  exact (finiteUnitaryThirdTwirlCP_choKim_eq_localCPFolds hdiv).symm

/-- Constructive relative-CP iteration along the literal alternating gate
prefix.  There is no supplied final-design premise: the final ensemble is
rewritten to the physical periodic circuit by the theorem above. -/
theorem relativeCPApproximation_choKim_of_alternating_prefix
    {n K : ℕ} (hdiv : K ∣ n) (hm : 0 < n / K)
    (globalReference localReference : ℕ →
      CStarMatrix (TripleIndex (Fin (2 ^ n)))
          (TripleIndex (Fin (2 ^ n))) ℂ →CP
        CStarMatrix (TripleIndex (Fin (2 ^ n)))
          (TripleIndex (Fin (2 ^ n))) ℂ)
    (error localError referenceError : ℕ → ℝ)
    (Haar : CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ →CP
      CStarMatrix (TripleIndex (Fin (2 ^ n)))
        (TripleIndex (Fin (2 ^ n))) ℂ)
    (herrorBounds : ∀ i ≤ 2 * (n / K) - 1,
      0 ≤ error i ∧ error i ≤ 1)
    (hlocalBounds : ∀ i < 2 * (n / K) - 1,
      0 ≤ localError i ∧ localError i ≤ 1)
    (hreferenceError : ∀ i < 2 * (n / K) - 1,
      0 ≤ referenceError i)
    (hbase : RelativeCPApproximation (error 0)
      (alternatingCPPrefix
        (alternatingCPGateList
          (fun j ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j))
          (fun j ↦ finiteUnitaryThirdTwirlCP
            (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j))) 0).toLinearMap
      (globalReference 0).toLinearMap)
    (hlocal : ∀ i < 2 * (n / K) - 1,
      RelativeCPApproximation (localError i)
        (alternatingCPGateAt
          (alternatingCPGateList
            (fun j ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j))
            (fun j ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j)))
          (i + 1)).2.toLinearMap
        (localReference i).toLinearMap)
    (hreference : ∀ i < 2 * (n / K) - 1,
      RelativeCPApproximation (referenceError i)
        (if (alternatingCPGateAt
          (alternatingCPGateList
            (fun j ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j))
            (fun j ↦ finiteUnitaryThirdTwirlCP
              (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j)))
          (i + 1)).1 then CompletelyPositiveMap.comp
            (localReference i) (globalReference i)
          else CompletelyPositiveMap.comp
            (globalReference i) (localReference i)).toLinearMap
        (globalReference (i + 1)).toLinearMap)
    (hrecurrence : ∀ i < 2 * (n / K) - 1,
      error (i + 1) =
        (1 + error i) * (1 + localError i) *
          (1 + referenceError i) - 1)
    (hfinalReference : globalReference (2 * (n / K) - 1) = Haar) :
    RelativeCPApproximation (error (2 * (n / K) - 1))
      (finiteUnitaryThirdTwirlCP
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)).toLinearMap
      Haar.toLinearMap := by
  let gates := alternatingCPGateList
    (fun j ↦ finiteUnitaryThirdTwirlCP
      (choKimEmbeddedBlockPauliCosetCliffordUnitaryFin hdiv j))
    (fun j ↦ finiteUnitaryThirdTwirlCP
      (choKimEmbeddedShiftedBlockPauliCosetCliffordUnitaryFin hdiv j))
  let ensemble := alternatingCPPrefix gates
  let left := fun i ↦ (alternatingCPGateAt gates (i + 1)).1
  let localEnsemble := fun i ↦ (alternatingCPGateAt gates (i + 1)).2
  have hprefix : ∀ i < 2 * (n / K) - 1,
      ensemble (i + 1) = if left i then
        CompletelyPositiveMap.comp (localEnsemble i) (ensemble i)
      else CompletelyPositiveMap.comp (ensemble i) (localEnsemble i) := by
    intro i hi
    apply alternatingCPPrefix_succ
    rw [length_alternatingCPGateList]
    omega
  have hiter := relativeCPApproximation_iterate_twoUnitary_mixed
    (r := 2 * (n / K) - 1) left ensemble globalReference
    localEnsemble localReference error localError referenceError
    hprefix herrorBounds hlocalBounds hreferenceError hbase hlocal hreference
    hrecurrence
  rw [show ensemble (2 * (n / K) - 1) =
      finiteUnitaryThirdTwirlCP
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) by
      exact alternatingCPPrefix_choKim_eq_literal hdiv hm,
    hfinalReference] at hiter
  exact hiter

end

end TomographyOracleCore
