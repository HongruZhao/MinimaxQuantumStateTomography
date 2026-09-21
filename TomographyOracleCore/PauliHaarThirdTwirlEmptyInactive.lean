import TomographyOracleCore.ChoKimPeriodicActiveSupportGeometry

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

local instance emptyInactiveSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance emptyInactiveStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Removing an empty inactive register

The full-prefix split writes an `N`-qubit binary word as an `N`-qubit
active word and a zero-qubit inactive word.  This module proves that
transporting a local unitary (or its third twirl) back through that literal
split removes the empty tensor factor exactly.
-/

/-- The active coordinate of the literal full-prefix split is unchanged. -/
@[simp] theorem binaryWordPrefixEquiv_full_fst
    (N : ℕ) (x : PauliBinaryWord N) :
    (binaryWordPrefixEquiv N N le_rfl x).1 = x := by
  funext i
  apply congrArg x
  apply Fin.ext
  simp [finPrefixSumEquiv]

/-- Reindexing a unitary tensored with the zero-qubit identity back through
the literal full-prefix split gives the original unitary. -/
theorem factorizationReindexUnitary_binaryWordPrefix_full_tensorId
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ) :
    factorizationReindexUnitary
        (binaryWordPrefixEquiv N N le_rfl).symm
        (finiteUnitaryTensorId (J := PauliBinaryWord (N - N)) U) =
      U := by
  apply Subtype.ext
  ext x y
  change
    U.1 (binaryWordPrefixEquiv N N le_rfl x).1
          (binaryWordPrefixEquiv N N le_rfl y).1 *
        (if (binaryWordPrefixEquiv N N le_rfl x).2 =
          (binaryWordPrefixEquiv N N le_rfl y).2 then 1 else 0) =
      U.1 x y
  have htail : (binaryWordPrefixEquiv N N le_rfl x).2 =
      (binaryWordPrefixEquiv N N le_rfl y).2 := by
    funext p
    exact Fin.elim0 (Fin.cast (Nat.sub_self N) p)
  rw [binaryWordPrefixEquiv_full_fst,
    binaryWordPrefixEquiv_full_fst]
  simp [htail]

/-- Generic finite-third-twirl form of empty-inactive normalization. -/
theorem finiteUnitaryThirdTwirlTensorIdCP_reindex_fullPrefix
    {N : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup (PauliBinaryWord N) ℂ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (binaryWordPrefixEquiv N N le_rfl).symm)
        (finiteUnitaryThirdTwirlTensorIdCP
          (J := PauliBinaryWord (N - N)) U) =
      finiteUnitaryThirdTwirlCP U := by
  unfold finiteUnitaryThirdTwirlTensorIdCP
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  exact factorizationReindexUnitary_binaryWordPrefix_full_tensorId N (U a)

/-- Haar/Pauli-coset specialization in the exact orientation used by the
last non-closing active-prefix step. -/
theorem pauliHaarThirdTwirlTensorIdCP_reindex_fullPrefix
    (N : ℕ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr
          (binaryWordPrefixEquiv N N le_rfl).symm)
        (pauliHaarThirdTwirlTensorIdCP N
          (PauliBinaryWord (N - N))) =
      pauliHaarThirdTwirlCP N := by
  simpa only [pauliHaarThirdTwirlTensorIdCP,
    pauliHaarThirdTwirlCP, finitePauliCosetThirdTwirlCP] using
    finiteUnitaryThirdTwirlTensorIdCP_reindex_fullPrefix
      (pauliCosetCliffordUnitary N)

/-- Syntactic alias with the inverse taken after triple replication. -/
theorem pauliHaarThirdTwirlTensorIdCP_reindex_fullPrefix_exact
    (N : ℕ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (binaryWordPrefixEquiv N N le_rfl)).symm
        (pauliHaarThirdTwirlTensorIdCP N
          (PauliBinaryWord (N - N))) =
      pauliHaarThirdTwirlCP N := by
  let e := binaryWordPrefixEquiv N N le_rfl
  have he : (tripleIndexCongr e).symm = tripleIndexCongr e.symm := by
    apply Equiv.ext
    rintro ⟨x₀, x₁, x₂⟩
    rfl
  rw [he]
  exact pauliHaarThirdTwirlTensorIdCP_reindex_fullPrefix N

/-- Full-prefix split with its propositionally empty tail normalized to the
literal type `PauliBinaryWord 0`. -/
def binaryWordFullPrefixEquiv (N : ℕ) :
    PauliBinaryWord N ≃ PauliBinaryWord N × PauliBinaryWord 0 :=
  (binaryWordPrefixEquiv N N le_rfl).trans <|
    (Equiv.refl (PauliBinaryWord N)).prodCongr
      (Equiv.cast (congrArg PauliBinaryWord (Nat.sub_self N)))

/-- Literal-zero-tail version of the unitary normalization. -/
theorem factorizationReindexUnitary_binaryWordFullPrefix_tensorId
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ) :
    factorizationReindexUnitary (binaryWordFullPrefixEquiv N).symm
        (finiteUnitaryTensorId (J := PauliBinaryWord 0) U) =
      U := by
  apply Subtype.ext
  ext x y
  change
    U.1 (binaryWordFullPrefixEquiv N x).1
          (binaryWordFullPrefixEquiv N y).1 *
        (if (binaryWordFullPrefixEquiv N x).2 =
          (binaryWordFullPrefixEquiv N y).2 then 1 else 0) =
      U.1 x y
  have hfst (z : PauliBinaryWord N) :
      (binaryWordFullPrefixEquiv N z).1 = z := by
    simp [binaryWordFullPrefixEquiv]
  have htail : (binaryWordFullPrefixEquiv N x).2 =
      (binaryWordFullPrefixEquiv N y).2 := Subsingleton.elim _ _
  rw [hfst, hfst]
  simp [htail]

/-- Exact literal-zero-tail Haar normalization. -/
theorem pauliHaarThirdTwirlTensorIdCP_reindex_binaryWordFullPrefix
    (N : ℕ) :
    CompletelyPositiveMap.reindexEquiv
        (tripleIndexCongr (binaryWordFullPrefixEquiv N)).symm
        (pauliHaarThirdTwirlTensorIdCP N (PauliBinaryWord 0)) =
      pauliHaarThirdTwirlCP N := by
  let e := binaryWordFullPrefixEquiv N
  have he : (tripleIndexCongr e).symm = tripleIndexCongr e.symm := by
    apply Equiv.ext
    rintro ⟨x₀, x₁, x₂⟩
    rfl
  rw [he]
  unfold pauliHaarThirdTwirlTensorIdCP pauliHaarThirdTwirlCP
    finitePauliCosetThirdTwirlCP finiteUnitaryThirdTwirlTensorIdCP
  rw [finiteUnitaryThirdTwirlCP_reindexEquiv]
  congr 1
  funext a
  exact factorizationReindexUnitary_binaryWordFullPrefix_tensorId N
    (pauliCosetCliffordUnitary N a)

end

end TomographyOracleCore
