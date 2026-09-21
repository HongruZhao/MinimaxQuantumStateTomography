import TomographyOracleCore.HardSpectrum
import TomographyOracleCore.ExactTargets

namespace TomographyOracleCore

open MatrixReduction
open scoped ComplexOrder

/-!
# Diagonal realization of the finite hard spectrum

This file realizes `hardSpectrumList m b` as an actual density operator on
`Fin (m + 2)`.  The construction is entirely internal: positivity and trace
normalization are proved from the scalar spectrum lemmas in `HardSpectrum`.
-/

/-- The coordinate function obtained by reading the finite hard-spectrum
list at an index of its (proved) length. -/
noncomputable def hardSpectrumEntry (m : ℕ) (b : ℝ)
    (i : Fin (m + 2)) : ℝ :=
  (hardSpectrumList m b)[i.val]'(by
    simpa only [hardSpectrumList_length] using i.isLt)

/-- Reading all coordinates of `hardSpectrumEntry` reconstructs the original
hard-spectrum list exactly. -/
theorem hardSpectrumEntry_ofFn (m : ℕ) (b : ℝ) :
    List.ofFn (hardSpectrumEntry m b) = hardSpectrumList m b := by
  simpa [hardSpectrumEntry, hardSpectrumList] using
    (List.ofFn_getElem (xs := hardSpectrumList m b))

theorem hardSpectrumEntry_nonnegative
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (i : Fin (m + 2)) :
    0 ≤ hardSpectrumEntry m b i := by
  apply hardSpectrumList_nonnegative m b hm hb0 hb1
  exact List.getElem_mem _

/-- The diagonal matrix whose diagonal is the hard spectrum. -/
noncomputable def hardDiagonalMatrix (m : ℕ) (b : ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ :=
  Matrix.diagonal fun i ↦ (hardSpectrumEntry m b i : ℂ)

@[simp] theorem hardDiagonalMatrix_apply
    (m : ℕ) (b : ℝ) (i j : Fin (m + 2)) :
    hardDiagonalMatrix m b i j =
      if i = j then (hardSpectrumEntry m b i : ℂ) else 0 := by
  simp [hardDiagonalMatrix, Matrix.diagonal_apply]

@[simp] theorem hardDiagonalMatrix_diagonal
    (m : ℕ) (b : ℝ) (i : Fin (m + 2)) :
    hardDiagonalMatrix m b i i = (hardSpectrumEntry m b i : ℂ) := by
  simp

theorem hardDiagonalMatrix_offDiagonal
    (m : ℕ) (b : ℝ) {i j : Fin (m + 2)} (hij : i ≠ j) :
    hardDiagonalMatrix m b i j = 0 := by
  simp [hij]

theorem hardSpectrumEntry_sum
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) :
    ∑ i : Fin (m + 2), hardSpectrumEntry m b i = 1 := by
  rw [← List.sum_ofFn, hardSpectrumEntry_ofFn,
    hardSpectrumList_sum m b hm]

theorem hardDiagonalMatrix_posSemidef
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) :
    (hardDiagonalMatrix m b).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  show ∀ i, (0 : ℂ) ≤ (hardSpectrumEntry m b i : ℂ)
  intro i
  rw [Complex.nonneg_iff]
  constructor
  · simpa using hardSpectrumEntry_nonnegative m b hm hb0 (by linarith) i
  · simp

theorem hardDiagonalMatrix_isHermitian
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) :
    (hardDiagonalMatrix m b).IsHermitian :=
  (hardDiagonalMatrix_posSemidef m b hm hb0 hbquarter).isHermitian

theorem hardDiagonalMatrix_trace_eq_one
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) :
    (hardDiagonalMatrix m b).trace = 1 := by
  rw [hardDiagonalMatrix, Matrix.trace_diagonal]
  rw [← Complex.ofReal_sum, hardSpectrumEntry_sum m b hm]
  norm_num

/-- The hard spectrum bundled as a genuine density operator. -/
noncomputable def hardDiagonalDensityOperator
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) : DensityOperator (Fin (m + 2)) where
  matrix := hardDiagonalMatrix m b
  posSemidef := hardDiagonalMatrix_posSemidef m b hm hb0 hbquarter
  trace_eq_one := hardDiagonalMatrix_trace_eq_one m b hm

@[simp] theorem hardDiagonalDensityOperator_matrix
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) :
    (hardDiagonalDensityOperator m b hm hb0 hbquarter).matrix =
      hardDiagonalMatrix m b := rfl

theorem hardSpectrumList_sortedGE
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hbquarter : b ≤ 1 / 4) :
    (hardSpectrumList m b).SortedGE := by
  rw [List.sortedGE_iff_pairwise]
  simp [hardSpectrumList, hardSpectrum_head_ge_tail m b hm hbquarter]

/-- The real parts of the characteristic roots of the diagonal matrix are
exactly the scalar hard spectrum, including multiplicities. -/
theorem hardDiagonalMatrix_roots_re_eq_spectrum (m : ℕ) (b : ℝ) :
    (hardDiagonalMatrix m b).charpoly.roots.map RCLike.re =
      (hardSpectrumList m b : Multiset ℝ) := by
  rw [hardDiagonalMatrix, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.map_bind,
      Multiset.map_singleton]
    rw [Multiset.bind_singleton, Fin.univ_val_map]
    exact congrArg (↑· : List ℝ → Multiset ℝ)
      (hardSpectrumEntry_ofFn m b)
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

/-- Mathlib's antitone ordered-eigenvalue list for the hard density operator
is literally `hardSpectrumList`.  Thus no spectral-ordering premise remains
external. -/
theorem hardDiagonalDensityOperator_orderedEigenvalues
    (m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) :
    List.ofFn
        (hardDiagonalDensityOperator m b hm hb0 hbquarter).isHermitian.eigenvalues₀ =
      hardSpectrumList m b := by
  let hA : (hardDiagonalMatrix m b).IsHermitian :=
    hardDiagonalMatrix_isHermitian m b hm hb0 hbquarter
  have hs := Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ hA
  rw [hardDiagonalMatrix_roots_re_eq_spectrum] at hs
  have hp : List.Pairwise (fun x y : ℝ ↦ decide (x ≥ y) = true)
      (hardSpectrumList m b) := by
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using
      hardSpectrumList_sortedGE m b hm hbquarter
  rw [Multiset.coe_sort, List.mergeSort_of_pairwise hp] at hs
  simpa [hA, hardDiagonalDensityOperator] using hs.symm

/-- A generic bridge between suffix sums of `List.ofFn` and the indexed
indicator sum used by `orderedSpectralTail`. -/
theorem sum_drop_ofFn_eq_sum_ite {n : ℕ} (f : Fin n → ℝ) (s : ℕ) :
    ((List.ofFn f).drop s).sum =
      ∑ i : Fin n, if s ≤ i.val then f i else 0 := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
      cases s with
      | zero =>
          simp only [List.drop_zero, List.sum_ofFn]
          apply Finset.sum_congr rfl
          intro i hi
          simp
      | succ s =>
          have hzero : ¬ s + 1 ≤ (0 : Fin (n + 1)).val := by simp
          rw [List.ofFn_succ, List.drop_succ_cons, Fin.sum_univ_succ]
          rw [if_neg hzero, zero_add]
          simp only [Fin.val_succ, Nat.succ_le_succ_iff]
          exact ih (fun i ↦ f i.succ) s

/-- The ordered spectral tail of the realized density operator is exactly
the suffix sum of the scalar hard spectrum. -/
theorem hardDiagonalDensityOperator_orderedSpectralTail
    (m s : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) :
    orderedSpectralTail
        (hardDiagonalDensityOperator m b hm hb0 hbquarter) s =
      hardSpectrumTailSum m b s := by
  unfold orderedSpectralTail hardSpectrumTailSum
  rw [← sum_drop_ofFn_eq_sum_ite]
  rw [hardDiagonalDensityOperator_orderedEigenvalues]

/-- Exact piecewise tail formula for the realized hard density operator. -/
theorem hardDiagonalDensityOperator_tail_eq_hardFamilyTail
    (m s : ℕ) (b : ℝ) (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    orderedSpectralTail
        (hardDiagonalDensityOperator m b hm hb0 hbquarter) s =
      hardFamilyTail m b s := by
  rw [hardDiagonalDensityOperator_orderedSpectralTail,
    hardSpectrumTailSum_eq_hardFamilyTail m s b hm hs]

/-- The realized hard density operator belongs to the manuscript's exact
spectral-decay class under the scalar hard-mass restriction. -/
theorem hardDiagonalDensityOperator_mem_spectralDecayClass
    (m : ℕ) (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    hardDiagonalDensityOperator m b hm hb0 hbquarter ∈
      spectralDecayClass (m + 2) alpha L := by
  rw [mem_spectralDecayClass_iff]
  intro s hs hsd
  rw [hardDiagonalDensityOperator_tail_eq_hardFamilyTail m s b hm hs]
  exact hardFamilyTail_le_decay_envelope m s alpha L b hm halpha hL
    hb0 hbquarter hbscaled hs

end TomographyOracleCore
