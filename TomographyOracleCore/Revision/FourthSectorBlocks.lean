import TomographyOracleCore.Revision.PauliOmegaBlocks

namespace TomographyOracleCore.Revision.FourthSectorBlocks

open PauliOmegaBlocks FourthSectorDecomposition MatrixTensorPi
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

theorem wordBlocksEquiv_apply_site (K : ℕ) (x : J → PauliBinaryWord K) (j : J) (a : Fin K) :
    wordBlocksEquiv J K x (finProdFinEquiv (Fintype.equivFin J j, a)) = x j a := by
  change x ((Fintype.equivFin J).symm
    (finProdFinEquiv.symm (finProdFinEquiv (Fintype.equivFin J j, a))).1)
      (finProdFinEquiv.symm (finProdFinEquiv (Fintype.equivFin J j, a))).2 = x j a
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem fourthIndex_wordBlocks_site (K : ℕ)
    (x : FourthIndex (J → PauliBinaryWord K)) (j : J) (a : Fin K) :
    fourthIndexPauliBinaryWordEquiv (Fintype.card J * K)
      (fourthMapEquiv (wordBlocksEquiv J K) x)
        (finProdFinEquiv (Fintype.equivFin J j, a)) =
      fourthIndexPauliBinaryWordEquiv K (fourthPiEquiv J (PauliBinaryWord K) x j) a := by
  change zmodTwoFourthEquivBitVecFour
    (wordBlocksEquiv J K x.1 (finProdFinEquiv (Fintype.equivFin J j, a)),
      wordBlocksEquiv J K x.2.1 (finProdFinEquiv (Fintype.equivFin J j, a)),
      wordBlocksEquiv J K x.2.2.1 (finProdFinEquiv (Fintype.equivFin J j, a)),
      wordBlocksEquiv J K x.2.2.2 (finProdFinEquiv (Fintype.equivFin J j, a))) = _
  simp_rw [wordBlocksEquiv_apply_site]
  rfl

/-- Every literal sector tensorizes over an arbitrary partition into equal
blocks, with the same label on each block. -/
theorem wordSector_union_eq_fourthTensorPi (K : ℕ) (i : Fin 30) :
    (wordSector (Fintype.card J * K) i).submatrix
      (fourthMapEquiv (wordBlocksEquiv J K)) (fourthMapEquiv (wordBlocksEquiv J K)) =
      fourthTensorPi (J := J) (fun _ => wordSector K i) := by
  classical
  ext x y
  simp only [Matrix.submatrix_apply, fourthTensorPi, tensorPi, wordSector_apply,
    prod_indicator_eq_ite_forall]
  have hiff : (∀ a : Fin (Fintype.card J * K),
      fourthIndexPauliBinaryWordEquiv (Fintype.card J * K)
        (fourthMapEquiv (wordBlocksEquiv J K) x) a ++
      fourthIndexPauliBinaryWordEquiv (Fintype.card J * K)
        (fourthMapEquiv (wordBlocksEquiv J K) y) a ∈ qubitFourthSector i) ↔
      ∀ j : J, ∀ a : Fin K,
        fourthIndexPauliBinaryWordEquiv K (fourthPiEquiv J (PauliBinaryWord K) x j) a ++
          fourthIndexPauliBinaryWordEquiv K (fourthPiEquiv J (PauliBinaryWord K) y j) a ∈
            qubitFourthSector i := by
    constructor
    · intro h j a
      simpa only [fourthIndex_wordBlocks_site] using
        h (finProdFinEquiv (Fintype.equivFin J j, a))
    · intro h a
      let j := (Fintype.equivFin J).symm (finProdFinEquiv.symm a).1
      let b := (finProdFinEquiv.symm a).2
      have ha : finProdFinEquiv (Fintype.equivFin J j, b) = a := by
        dsimp [j, b]
        rw [Equiv.apply_symm_apply]
        exact finProdFinEquiv.apply_symm_apply a
      rw [← ha, fourthIndex_wordBlocks_site, fourthIndex_wordBlocks_site]
      exact h j b
  simp only [hiff]

/-- The ordered binary-word partition used by the actual circuit. -/
theorem wordSector_binary_blocks (m K : ℕ) (i : Fin 30)
    (x y : FourthIndex (PauliBinaryWord (m * K))) :
    wordSector (m * K) i x y =
      ∏ j : Fin m, wordSector K i
        (fourthPiEquiv (Fin m) (PauliBinaryWord K)
          (fourthMapEquiv (binaryWordBlockEquiv m K) x) j)
        (fourthPiEquiv (Fin m) (PauliBinaryWord K)
          (fourthMapEquiv (binaryWordBlockEquiv m K) y) j) := by
  classical
  simp only [wordSector_apply, prod_indicator_eq_ite_forall]
  have hx (j : Fin m) (a : Fin K) :
      fourthIndexPauliBinaryWordEquiv (m * K) x (finProdFinEquiv (j, a)) =
        fourthIndexPauliBinaryWordEquiv K
          (fourthPiEquiv (Fin m) (PauliBinaryWord K)
            (fourthMapEquiv (binaryWordBlockEquiv m K) x) j) a := rfl
  have hy (j : Fin m) (a : Fin K) :
      fourthIndexPauliBinaryWordEquiv (m * K) y (finProdFinEquiv (j, a)) =
        fourthIndexPauliBinaryWordEquiv K
          (fourthPiEquiv (Fin m) (PauliBinaryWord K)
            (fourthMapEquiv (binaryWordBlockEquiv m K) y) j) a := rfl
  have hiff : (∀ a : Fin (m * K),
      fourthIndexPauliBinaryWordEquiv (m * K) x a ++
        fourthIndexPauliBinaryWordEquiv (m * K) y a ∈ qubitFourthSector i) ↔
      ∀ j : Fin m, ∀ a : Fin K,
        fourthIndexPauliBinaryWordEquiv K
          (fourthPiEquiv (Fin m) (PauliBinaryWord K)
            (fourthMapEquiv (binaryWordBlockEquiv m K) x) j) a ++
        fourthIndexPauliBinaryWordEquiv K
          (fourthPiEquiv (Fin m) (PauliBinaryWord K)
            (fourthMapEquiv (binaryWordBlockEquiv m K) y) j) a ∈ qubitFourthSector i := by
    constructor
    · intro h j a
      simpa only [hx, hy] using h (finProdFinEquiv (j, a))
    · intro h a
      have ha := h (finProdFinEquiv.symm a).1 (finProdFinEquiv.symm a).2
      simpa only [← hx, ← hy, Prod.mk.eta, Equiv.apply_symm_apply] using ha
  simp only [hiff]
  split_ifs <;> rfl

end
end TomographyOracleCore.Revision.FourthSectorBlocks
