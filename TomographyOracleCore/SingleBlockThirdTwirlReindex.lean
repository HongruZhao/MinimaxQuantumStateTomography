import TomographyOracleCore.ChoKimPeriodicThirdTwirlFactorizationBridge
import TomographyOracleCore.FiniteUnitaryThirdTwirlFactorCP
import TomographyOracleCore.FiniteUnitaryThirdTwirlReindex

namespace TomographyOracleCore

universe u v

open scoped BigOperators CStarAlgebra Kronecker

noncomputable section

local instance singleBlockReindexSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance singleBlockReindexStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Reindexing one embedded block as a local tensor factor

The periodic circuit is built in the canonical binary-word basis.  This file
isolates one block coordinate without using a cardinality-only equivalence and
shows that its embedded unitary, and hence its finite third twirl, is literally
the local operation tensored with the identity on all other block coordinates.
The result is independent of the Cho--Kim traversal and is reusable for any
block-tensor circuit.
-/

/-- Split one distinguished coordinate from a finite function. -/
def piSplitAtEquiv {I : Type u} {X : Type v} [DecidableEq I] (j : I) :
    (I → X) ≃ X × ({i : I // i ≠ j} → X) where
  toFun f := (f j, fun i ↦ f i.1)
  invFun p i := if h : i = j then p.1 else p.2 ⟨i, h⟩
  left_inv f := by
    funext i
    by_cases h : i = j
    · subst i
      simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext i
      simp [i.2]

@[simp] theorem piSplitAtEquiv_apply_fst
    {I : Type u} {X : Type v} [DecidableEq I]
    (j : I) (f : I → X) :
    (piSplitAtEquiv j f).1 = f j := rfl

@[simp] theorem piSplitAtEquiv_apply_snd
    {I : Type u} {X : Type v} [DecidableEq I]
    (j : I) (f : I → X) (i : {i : I // i ≠ j}) :
    (piSplitAtEquiv j f).2 i = f i.1 := rfl

@[simp] theorem piSplitAtEquiv_symm_apply_at
    {I : Type u} {X : Type v} [DecidableEq I]
    (j : I) (x : X) (r : {i : I // i ≠ j} → X) :
    (piSplitAtEquiv j).symm (x, r) j = x := by
  simp [piSplitAtEquiv]

@[simp] theorem piSplitAtEquiv_symm_apply_away
    {I : Type u} {X : Type v} [DecidableEq I]
    (j : I) (x : X) (r : {i : I // i ≠ j} → X)
    (i : I) (hi : i ≠ j) :
    (piSplitAtEquiv j).symm (x, r) i = r ⟨i, hi⟩ := by
  simp [piSplitAtEquiv, hi]

/-- Canonical support-compatible decomposition into block `j` and all other
blocks. -/
def singleBlockBinaryWordEquiv (m K : ℕ) (j : Fin m) :
    PauliBinaryWord (m * K) ≃
      PauliBinaryWord K ×
        ({i : Fin m // i ≠ j} → PauliBinaryWord K) :=
  (binaryWordBlockEquiv m K).trans (piSplitAtEquiv j)

@[simp] theorem singleBlockBinaryWordEquiv_apply_fst
    (m K : ℕ) (j : Fin m) (x : PauliBinaryWord (m * K)) :
    (singleBlockBinaryWordEquiv m K j x).1 =
      binaryWordBlockEquiv m K x j := rfl

@[simp] theorem singleBlockBinaryWordEquiv_apply_snd
    (m K : ℕ) (j : Fin m) (x : PauliBinaryWord (m * K))
    (i : {i : Fin m // i ≠ j}) :
    (singleBlockBinaryWordEquiv m K j x).2 i =
      binaryWordBlockEquiv m K x i.1 := rfl

private theorem singleBlock_identity_product
    (m K : ℕ) (j : Fin m)
    (x y : PauliBinaryWord (m * K)) :
    (∏ i ∈ (Finset.univ : Finset (Fin m)) \ {j},
        (1 : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
          (binaryWordBlockEquiv m K x i)
          (binaryWordBlockEquiv m K y i)) =
      if (singleBlockBinaryWordEquiv m K j x).2 =
          (singleBlockBinaryWordEquiv m K j y).2 then 1 else 0 := by
  classical
  by_cases hrest : (singleBlockBinaryWordEquiv m K j x).2 =
      (singleBlockBinaryWordEquiv m K j y).2
  · rw [if_pos hrest]
    apply Finset.prod_eq_one
    intro i hi
    rw [Matrix.one_apply]
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton] at hi
    rw [if_pos]
    have hcoord := congrFun hrest ⟨i, hi⟩
    exact hcoord
  · rw [if_neg hrest]
    have hdiff : ∃ i : {i : Fin m // i ≠ j},
        (singleBlockBinaryWordEquiv m K j x).2 i ≠
          (singleBlockBinaryWordEquiv m K j y).2 i := by
      by_contra h
      push Not at h
      exact hrest (funext h)
    obtain ⟨i, hi⟩ := hdiff
    apply Finset.prod_eq_zero
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ i.1, by simpa using i.2⟩
    · rw [Matrix.one_apply, if_neg]
      simpa using hi

/-- Reindexing one block-tensor embedding by the actual block coordinates
produces the local unitary tensored with identity on the complement. -/
theorem factorizationReindexUnitary_singleBlockEmbeddedUnitary
    (m K : ℕ) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    factorizationReindexUnitary (singleBlockBinaryWordEquiv m K j)
        (singleBlockEmbeddedUnitary m K j U) =
      finiteUnitaryTensorId
        (J := {i : Fin m // i ≠ j} → PauliBinaryWord K) U := by
  classical
  apply Subtype.ext
  ext x y
  rcases x with ⟨xj, xr⟩
  rcases y with ⟨yj, yr⟩
  let x' := (singleBlockBinaryWordEquiv m K j).symm (xj, xr)
  let y' := (singleBlockBinaryWordEquiv m K j).symm (yj, yr)
  change blockTensorMatrix m K
      (fun i ↦ (((Pi.mulSingle j U :
        Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ)) i).1) x' y' =
    U.1 xj yj * (if xr = yr then 1 else 0)
  rw [blockTensorMatrix]
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
    (Finset.mem_univ j)]
  have hxj : binaryWordBlockEquiv m K x' j = xj := by
    change (singleBlockBinaryWordEquiv m K j x').1 = xj
    simp [x']
  have hyj : binaryWordBlockEquiv m K y' j = yj := by
    change (singleBlockBinaryWordEquiv m K j y').1 = yj
    simp [y']
  rw [Pi.mulSingle_eq_same, hxj, hyj]
  congr 1
  have hrest := singleBlock_identity_product m K j x' y'
  simp only [x', y', Equiv.apply_symm_apply] at hrest
  let W : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ :=
    Pi.mulSingle j U
  change (∏ i ∈ (Finset.univ : Finset (Fin m)) \ {j},
      (W i).1 (binaryWordBlockEquiv m K x' i)
        (binaryWordBlockEquiv m K y' i)) = _
  calc
    (∏ i ∈ (Finset.univ : Finset (Fin m)) \ {j},
        (W i).1
          (binaryWordBlockEquiv m K x' i)
          (binaryWordBlockEquiv m K y' i)) =
      ∏ i ∈ (Finset.univ : Finset (Fin m)) \ {j},
        (1 : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
          (binaryWordBlockEquiv m K x' i)
          (binaryWordBlockEquiv m K y' i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hij : i ≠ j := by
          simpa only [Finset.mem_sdiff, Finset.mem_univ, true_and,
            Finset.mem_singleton] using hi
        simp [W, hij]
    _ = if xr = yr then 1 else 0 := hrest

/-- Tensor cubes commute with arbitrary finite coordinate reindexing. -/
theorem finiteUnitaryTensorCube_factorizationReindex
    {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (e : I ≃ J) (U : Matrix.unitaryGroup I ℂ) :
    CStarMatrix.reindexₐ ℂ ℂ (tripleIndexCongr e)
        (finiteUnitaryTensorCube U) =
      finiteUnitaryTensorCube (factorizationReindexUnitary e U) := by
  apply CStarMatrix.ext
  intro x y
  change Matrix.reindexAlgEquiv ℂ ℂ (tripleIndexCongr e)
      (matrixTensorThree U.1 U.1 U.1) x y = _
  rw [reindexAlgEquiv_matrixTensorThree]
  rfl

/-- Coordinate transport intertwines a normalized finite third-twirl CP map
with pointwise unitary reindexing. -/
theorem finiteUnitaryThirdTwirlCP_reindexEquiv
    {I : Type u} {J : Type v} {E : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype E] [Nonempty E]
    (e : I ≃ J) (U : E → Matrix.unitaryGroup I ℂ) :
    CompletelyPositiveMap.reindexEquiv (tripleIndexCongr e)
        (finiteUnitaryThirdTwirlCP U) =
      finiteUnitaryThirdTwirlCP
        (fun a ↦ factorizationReindexUnitary e (U a)) := by
  classical
  apply DFunLike.coe_injective
  funext X
  change CStarMatrix.reindexₐ ℂ ℂ (tripleIndexCongr e)
      ((finiteUnitaryThirdTwirlCP U).toLinearMap
        (CStarMatrix.reindexₐ ℂ ℂ (tripleIndexCongr e).symm X)) =
    (finiteUnitaryThirdTwirlCP
      (fun a ↦ factorizationReindexUnitary e (U a))).toLinearMap X
  rw [finiteUnitaryThirdTwirlCP_apply,
    finiteUnitaryThirdTwirlCP_apply]
  rw [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  rw [map_mul, map_mul, map_star,
    finiteUnitaryTensorCube_factorizationReindex]
  rw [CStarMatrix.reindexₐ_symm,
    (CStarMatrix.reindexₐ ℂ ℂ (tripleIndexCongr e)).apply_symm_apply]

/-- Exact CP-map form of the single-block tensor-factor identity. -/
theorem finiteUnitaryThirdTwirlCP_singleBlock_reindex
    (m K : ℕ) (j : Fin m) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (singleBlockBinaryWordEquiv m K j))
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            singleBlockEmbeddedUnitary m K j
              (pauliCosetCliffordUnitary K a))) =
      finiteUnitaryThirdTwirlTensorIdCP
        (J := {i : Fin m // i ≠ j} → PauliBinaryWord K)
        (pauliCosetCliffordUnitary K) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  exact factorizationReindexUnitary_singleBlockEmbeddedUnitary
    m K j (pauliCosetCliffordUnitary K a)

/-- Conjugating a block embedding by a qubit permutation is exactly unitary
reindexing by the induced binary-word equivalence. -/
theorem shiftedSingleBlockEmbeddedUnitary_eq_reindex
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    shiftedSingleBlockEmbeddedUnitary m K σ j U =
      factorizationReindexUnitary (permuteBinaryWord σ)
        (singleBlockEmbeddedUnitary m K j U) := by
  classical
  apply Subtype.ext
  ext x y
  rw [shiftedSingleBlockEmbeddedUnitary_eq]
  change
    (permutationMatrix (permuteBinaryWord σ) *
        ((singleBlockEmbeddedUnitary m K j U).1 *
          permutationMatrix (permuteBinaryWord σ.symm))) x y = _
  rw [permutationMatrix_mul_apply, mul_permutationMatrix_apply]
  rfl

/-- Support-compatible split for a shifted block.  It first undoes the
physical qubit permutation and then isolates the original block coordinate. -/
def shiftedSingleBlockBinaryWordEquiv
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) (j : Fin m) :
    PauliBinaryWord (m * K) ≃
      PauliBinaryWord K ×
        ({i : Fin m // i ≠ j} → PauliBinaryWord K) :=
  (permuteBinaryWord σ).symm.trans (singleBlockBinaryWordEquiv m K j)

/-- After the shifted support split, a shifted block unitary is again the
local unitary tensored with identity. -/
theorem factorizationReindexUnitary_shiftedSingleBlockEmbeddedUnitary
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) (j : Fin m)
    (U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    factorizationReindexUnitary
        (shiftedSingleBlockBinaryWordEquiv m K σ j)
        (shiftedSingleBlockEmbeddedUnitary m K σ j U) =
      finiteUnitaryTensorId
        (J := {i : Fin m // i ≠ j} → PauliBinaryWord K) U := by
  rw [shiftedSingleBlockEmbeddedUnitary_eq_reindex]
  rw [factorizationReindexUnitary_trans]
  have htrans : (permuteBinaryWord σ).trans
      (shiftedSingleBlockBinaryWordEquiv m K σ j) =
        singleBlockBinaryWordEquiv m K j := by
    apply Equiv.ext
    intro x
    change singleBlockBinaryWordEquiv m K j
        ((permuteBinaryWord σ).symm (permuteBinaryWord σ x)) = _
    rw [Equiv.symm_apply_apply]
  rw [htrans]
  exact factorizationReindexUnitary_singleBlockEmbeddedUnitary m K j U

/-- Exact CP-map form of the shifted single-block tensor-factor identity. -/
theorem finiteUnitaryThirdTwirlCP_shiftedSingleBlock_reindex
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K))) (j : Fin m) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (shiftedSingleBlockBinaryWordEquiv m K σ j))
        (finiteUnitaryThirdTwirlCP
          (fun a : PauliCosetCliffordEnsemble K ↦
            shiftedSingleBlockEmbeddedUnitary m K σ j
              (pauliCosetCliffordUnitary K a))) =
      pauliHaarThirdTwirlTensorIdCP K
        ({i : Fin m // i ≠ j} → PauliBinaryWord K) := by
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  unfold pauliHaarThirdTwirlTensorIdCP
    finiteUnitaryThirdTwirlTensorIdCP
  congr 1
  funext a
  exact factorizationReindexUnitary_shiftedSingleBlockEmbeddedUnitary
    m K σ j (pauliCosetCliffordUnitary K a)

end

end TomographyOracleCore
