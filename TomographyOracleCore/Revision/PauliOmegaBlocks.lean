import TomographyOracleCore.Revision.FourthLocalEmbedding
import TomographyOracleCore.Revision.MatrixTensorPi

namespace TomographyOracleCore.Revision.PauliOmegaBlocks

open MatrixTensorPi CliffordFourthOmega FourthSectorDecomposition FourthLocalEmbedding
open scoped BigOperators
noncomputable section

variable {J : Type*} [Fintype J] [DecidableEq J]

def fourthMapEquiv {α β : Type*} (e : α ≃ β) : FourthIndex α ≃ FourthIndex β :=
  Equiv.prodCongr e (Equiv.prodCongr e (Equiv.prodCongr e e))

def wordBlocksEquiv (J : Type*) [Fintype J] (K : ℕ) :
    (J → PauliBinaryWord K) ≃ PauliBinaryWord (Fintype.card J * K) :=
  (Equiv.arrowCongr (Fintype.equivFin J) (Equiv.refl (PauliBinaryWord K))).trans
    (binaryWordBlockEquiv (Fintype.card J) K).symm

theorem wordBlocksEquiv_add (K : ℕ) (x y : J → PauliBinaryWord K) :
    wordBlocksEquiv J K (x + y) = wordBlocksEquiv J K x + wordBlocksEquiv J K y := rfl

theorem wordBlocksEquiv_zero (K : ℕ) :
    wordBlocksEquiv J K (0 : J → PauliBinaryWord K) = 0 := rfl

theorem fourthWordSum_map_blocks (K : ℕ)
    (x : FourthIndex (J → PauliBinaryWord K)) :
    fourthWordSum (fourthMapEquiv (wordBlocksEquiv J K) x) =
      wordBlocksEquiv J K (x.1 + x.2.1 + x.2.2.1 + x.2.2.2) := rfl

theorem fourthOmegaSupport_map_blocks (K : ℕ)
    (x y : FourthIndex (J → PauliBinaryWord K)) :
    fourthOmegaSupport (fourthMapEquiv (wordBlocksEquiv J K) x)
      (fourthMapEquiv (wordBlocksEquiv J K) y) ↔
        ∀ j, fourthOmegaSupport (fourthPiEquiv J (PauliBinaryWord K) x j)
          (fourthPiEquiv J (PauliBinaryWord K) y j) := by
  unfold fourthOmegaSupport fourthPauliShiftMatches
  rw [fourthWordSum_map_blocks]
  change (wordBlocksEquiv J K (y.1 + y.2.1 + y.2.2.1 + y.2.2.2) = 0 ∧
    wordBlocksEquiv J K x.1 = wordBlocksEquiv J K (y.1 + (x.1 + y.1)) ∧
    wordBlocksEquiv J K x.2.1 = wordBlocksEquiv J K (y.2.1 + (x.1 + y.1)) ∧
    wordBlocksEquiv J K x.2.2.1 = wordBlocksEquiv J K (y.2.2.1 + (x.1 + y.1)) ∧
    wordBlocksEquiv J K x.2.2.2 = wordBlocksEquiv J K (y.2.2.2 + (x.1 + y.1))) ↔ _
  rw [← wordBlocksEquiv_zero (J := J) K]
  simp only [(wordBlocksEquiv J K).injective.eq_iff, funext_iff,
    fourthPiEquiv, fourthWordSum, Equiv.coe_fn_mk, Pi.add_apply, Pi.zero_apply,
    forall_and]

/-- Tensor products of local Omegas are the literal Omega on their union. -/
theorem fourthTensorPi_omega_eq_union (K : ℕ) :
    fourthTensorPi (J := J) (fun _ => pauliFourthOmega K) =
      (pauliFourthOmega (Fintype.card J * K)).submatrix
        (fourthMapEquiv (wordBlocksEquiv J K)) (fourthMapEquiv (wordBlocksEquiv J K)) := by
  classical
  ext x y
  simp only [fourthTensorPi, tensorPi, Matrix.submatrix_apply, pauliFourthOmega_apply,
    prod_indicator_eq_ite_forall, fourthOmegaSupport_map_blocks]

def selectedWordEquiv (p : J → Prop) [DecidablePred p] (K : ℕ) :
    (J → PauliBinaryWord K) ≃
      PauliBinaryWord (Fintype.card {j // p j} * K) × ({j // ¬p j} → PauliBinaryWord K) :=
  (Equiv.piEquivPiSubtypeProd p (fun _ => PauliBinaryWord K)).trans
    (Equiv.prodCongr (wordBlocksEquiv {j // p j} K) (Equiv.refl _))

def selectedOmega (p : J → Prop) [DecidablePred p] (K : ℕ) :
    Matrix (FourthIndex (J → PauliBinaryWord K)) (FourthIndex (J → PauliBinaryWord K)) ℂ :=
  fourthTensorPi (fun j => if p j then pauliFourthOmega K else 1)

theorem selectedOmega_apply (p : J → Prop) [DecidablePred p] (K : ℕ)
    (x y : FourthIndex (J → PauliBinaryWord K)) :
    selectedOmega p K x y = if
      (∀ j, p j → fourthOmegaSupport (fourthPiEquiv J (PauliBinaryWord K) x j)
        (fourthPiEquiv J (PauliBinaryWord K) y j)) ∧
      (∀ j, ¬p j → fourthPiEquiv J (PauliBinaryWord K) x j =
        fourthPiEquiv J (PauliBinaryWord K) y j) then 1 else 0 := by
  classical
  change (∏ j, (if p j then pauliFourthOmega K else 1)
    (fourthPiEquiv J (PauliBinaryWord K) x j)
    (fourthPiEquiv J (PauliBinaryWord K) y j)) = _
  have hentry (j : J) : (if p j then pauliFourthOmega K else 1)
      (fourthPiEquiv J (PauliBinaryWord K) x j)
      (fourthPiEquiv J (PauliBinaryWord K) y j) =
      if (p j → fourthOmegaSupport (fourthPiEquiv J (PauliBinaryWord K) x j)
        (fourthPiEquiv J (PauliBinaryWord K) y j)) ∧
      (¬p j → fourthPiEquiv J (PauliBinaryWord K) x j =
        fourthPiEquiv J (PauliBinaryWord K) y j) then 1 else 0 := by
    by_cases hj : p j <;> simp [hj, pauliFourthOmega_apply, Matrix.one_apply]
  simp_rw [hentry]
  split_ifs with h
  · apply Finset.prod_eq_one
    intro j _
    exact if_pos ⟨h.1 j, h.2 j⟩
  · have hn : ¬∀ j, (p j → fourthOmegaSupport
        (fourthPiEquiv J (PauliBinaryWord K) x j)
        (fourthPiEquiv J (PauliBinaryWord K) y j)) ∧
        (¬p j → fourthPiEquiv J (PauliBinaryWord K) x j =
          fourthPiEquiv J (PauliBinaryWord K) y j) := by
      simpa only [forall_and] using h
    obtain ⟨j, hj⟩ := not_forall.mp hn
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

def restrictFourth (p : J → Prop) (K : ℕ)
    (x : FourthIndex (J → PauliBinaryWord K)) :
    FourthIndex ({j // p j} → PauliBinaryWord K) :=
  (fun j => x.1 j, fun j => x.2.1 j, fun j => x.2.2.1 j, fun j => x.2.2.2 j)

theorem restrictFourth_eq_iff (p : J → Prop) (K : ℕ)
    (x y : FourthIndex (J → PauliBinaryWord K)) :
    restrictFourth p K x = restrictFourth p K y ↔
      ∀ j, p j → fourthPiEquiv J (PauliBinaryWord K) x j =
        fourthPiEquiv J (PauliBinaryWord K) y j := by
  simp only [restrictFourth, fourthPiEquiv, Equiv.coe_fn_mk, Prod.mk.injEq,
    funext_iff, Subtype.forall, forall_and]

/-- Grouping all selected blocks gives the concrete subsystem operator,
including the identity on every unselected register. -/
theorem selectedOmega_eq_local_union (p : J → Prop) [DecidablePred p] (K : ℕ) :
    selectedOmega p K =
      (localPauliFourthOmega (β := {j // ¬p j} → PauliBinaryWord K)
        (Fintype.card {j // p j} * K)).submatrix
          (fourthMapEquiv (selectedWordEquiv p K)) (fourthMapEquiv (selectedWordEquiv p K)) := by
  classical
  ext x y
  rw [selectedOmega_apply]
  rw [Matrix.submatrix_apply, localPauliFourthOmega_apply]
  change _ = (pauliFourthOmega (Fintype.card {j // p j} * K)
    (fourthMapEquiv (wordBlocksEquiv {j // p j} K) (restrictFourth p K x))
    (fourthMapEquiv (wordBlocksEquiv {j // p j} K) (restrictFourth p K y))) *
      (if restrictFourth (fun j => ¬p j) K x = restrictFourth (fun j => ¬p j) K y
        then 1 else 0)
  rw [pauliFourthOmega_apply]
  simp only [fourthOmegaSupport_map_blocks, restrictFourth_eq_iff]
  have hsel : (∀ j : {j // p j},
      fourthOmegaSupport (fourthPiEquiv {j // p j} (PauliBinaryWord K)
        (restrictFourth p K x) j) (fourthPiEquiv {j // p j} (PauliBinaryWord K)
          (restrictFourth p K y) j)) ↔
      ∀ j, p j → fourthOmegaSupport (fourthPiEquiv J (PauliBinaryWord K) x j)
        (fourthPiEquiv J (PauliBinaryWord K) y j) := by
    simp only [Subtype.forall, restrictFourth, fourthPiEquiv, Equiv.coe_fn_mk]
  simp only [hsel]
  split_ifs <;> simp_all

end
end TomographyOracleCore.Revision.PauliOmegaBlocks
