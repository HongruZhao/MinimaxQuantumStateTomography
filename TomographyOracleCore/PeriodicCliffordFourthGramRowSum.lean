import TomographyOracleCore.PeriodicCliffordFourthGramMatrix

namespace TomographyOracleCore

noncomputable section

/-!
# Exact row sum of the certified fourth-copy Gram matrix

The proof below separates a generic four-value power-sum identity from the
already certified `8,14,7,1` intersection profile.  It is purely finite
arithmetic and does not identify the scalar matrix with a concrete Clifford
operator Gram matrix.
-/

/-- A list whose entries lie in `{1,2,3,4}` has a power sum determined by
the four Boolean counts. -/
private theorem listSum_pow_eq_countP_one_to_four
    (l : List ℕ) (x : ℝ)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) :
    (l.map fun a ↦ x ^ a).sum =
      ((l.countP (fun a ↦ a == 1) : ℕ) : ℝ) * x +
      ((l.countP (fun a ↦ a == 2) : ℕ) : ℝ) * x ^ 2 +
      ((l.countP (fun a ↦ a == 3) : ℕ) : ℝ) * x ^ 3 +
      ((l.countP (fun a ↦ a == 4) : ℕ) : ℝ) * x ^ 4 := by
  induction l with
  | nil => simp
  | cons a l ih =>
      have ha : a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 :=
        hl a (by simp)
      have htail : ∀ b ∈ l, b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
        intro b hb
        exact hl b (by simp [hb])
      have hi := ih htail
      rcases ha with rfl | rfl | rfl | rfl <;>
        simp [hi] <;> ring

/-- Re-indexing the finite row sum by `List.finRange`. -/
private theorem qubitFourthGramPowerSum_eq_listSum
    (i : Fin 30) (x : ℝ) :
    (∑ j : Fin 30, x ^ qubitFourthIntersectionEntry i j) =
      ((List.finRange 30).map fun j ↦
        x ^ qubitFourthIntersectionEntry i j).sum := by
  rw [← List.sum_ofFn, List.ofFn_eq_map]

/-- Before inserting the numerical row profile, the Gram row sum is exactly
the polynomial whose coefficients are the four certified row counts. -/
theorem qubitFourthGramMatrix_rowSum_eq_rowCountPolynomial
    (i : Fin 30) (x : ℝ) :
    (∑ j, qubitFourthGramMatrix x i j) =
      qubitFourthRowCount i 1 * x +
        qubitFourthRowCount i 2 * x ^ 2 +
        qubitFourthRowCount i 3 * x ^ 3 +
        qubitFourthRowCount i 4 * x ^ 4 := by
  have hall : ∀ a ∈
      (List.finRange 30).map
        (fun j ↦ qubitFourthIntersectionEntry i j),
      a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
    intro a ha
    obtain ⟨j, _hj, rfl⟩ := List.mem_map.mp ha
    have hb := qubitFourthIntersectionEntry_bounds i j
    omega
  have hlist := listSum_pow_eq_countP_one_to_four
    ((List.finRange 30).map
      (fun j ↦ qubitFourthIntersectionEntry i j)) x hall
  have hprofile :
      ((List.finRange 30).map fun j ↦
          x ^ qubitFourthIntersectionEntry i j).sum =
        qubitFourthRowCount i 1 * x +
          qubitFourthRowCount i 2 * x ^ 2 +
          qubitFourthRowCount i 3 * x ^ 3 +
          qubitFourthRowCount i 4 * x ^ 4 := by
    simpa only [List.map_map, Function.comp_def, List.countP_map,
      qubitFourthRowCount] using hlist
  calc
    (∑ j, qubitFourthGramMatrix x i j) =
        ∑ j : Fin 30, x ^ qubitFourthIntersectionEntry i j := by rfl
    _ = ((List.finRange 30).map fun j ↦
          x ^ qubitFourthIntersectionEntry i j).sum :=
      qubitFourthGramPowerSum_eq_listSum i x
    _ = qubitFourthRowCount i 1 * x +
          qubitFourthRowCount i 2 * x ^ 2 +
          qubitFourthRowCount i 3 * x ^ 3 +
          qubitFourthRowCount i 4 * x ^ 4 := hprofile

/-- Exact constant row sum required by the abstract periodic trace-cycle
endpoint. -/
theorem qubitFourthGramMatrix_rowSum
    (i : Fin 30) (x : ℝ) :
    ∑ j, qubitFourthGramMatrix x i j =
      cliffordFourthGramRowSum x := by
  rw [qubitFourthGramMatrix_rowSum_eq_rowCountPolynomial]
  exact qubitFourthGramRowPolynomial_eq i x

/-- Quantified form matching the `hrow` argument of
`periodicCliffordFourthU4_of_concreteExpansion`. -/
theorem qubitFourthGramMatrix_all_rowSums
    (x : ℝ) :
    ∀ i, ∑ j, qubitFourthGramMatrix x i j =
      cliffordFourthGramRowSum x := by
  intro i
  exact qubitFourthGramMatrix_rowSum i x

end

end TomographyOracleCore
