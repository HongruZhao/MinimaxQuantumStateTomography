import TomographyOracleCore.PeriodicCliffordFourthCycle
import Mathlib.Logic.Equiv.Fin.Rotate

namespace TomographyOracleCore.Revision.FourthCycleContraction

open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pathWeight (G : Matrix ι ι ℝ) :
    (n : ℕ) → ι → (Fin n → ι) → ι → ℝ
  | 0, a, _, b => G a b
  | n + 1, a, v, b => G a (v 0) * pathWeight G n (v 0) (fun j => v j.succ) b

theorem sum_pathWeight (G : Matrix ι ι ℝ) (n : ℕ) (a b : ι) :
    (∑ v : Fin n → ι, pathWeight G n a v b) = (G ^ (n + 1)) a b := by
  induction n generalizing a b with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).sum_comp]
    rw [Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, pathWeight, Fin.cons_zero, Fin.cons_succ]
    simp_rw [← Finset.mul_sum, ih]
    rw [pow_succ' G (n + 1), Matrix.mul_apply]

theorem pathWeight_eq_product (G : Matrix ι ι ℝ) (n : ℕ)
    (v : Fin (n + 1) → ι) (b : ι) :
    pathWeight G n (v 0) (fun j => v j.succ) b =
      (∏ j : Fin n, G (v j.castSucc) (v j.succ)) * G (v (Fin.last n)) b := by
  induction n with
  | zero => simp [pathWeight]
  | succ n ih =>
    rw [pathWeight, ih (fun j => v j.succ), Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.succ_last, mul_assoc]

theorem cycle_product_eq_pathWeight (G : Matrix ι ι ℝ) (n : ℕ)
    (v : Fin (n + 1) → ι) :
    (∏ j : Fin (n + 1), G (v j) (v (finRotate (n + 1) j))) =
      pathWeight G n (v 0) (fun j => v j.succ) (v 0) := by
  rw [pathWeight_eq_product, Fin.prod_univ_castSucc, finRotate_last]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hr : finRotate (n + 1) j.castSucc = j.succ := finRotate_of_lt j.isLt
  rw [hr]

def cyclePartition (G : Matrix ι ι ℝ) (m : ℕ) : ℝ :=
  ∑ v : Fin m → ι, ∏ j : Fin m, G (v j) (v (finRotate m j))

/-- The exact closed-chain partition function is the trace of a matrix
power. The positive-length condition also covers the one-block cycle. -/
theorem cyclePartition_eq_trace (G : Matrix ι ι ℝ) {m : ℕ} (hm : 0 < m) :
    cyclePartition G m = (G ^ m).trace := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  unfold cyclePartition
  simp_rw [cycle_product_eq_pathWeight]
  rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => ι)).sum_comp]
  rw [Fintype.sum_prod_type]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
  simp_rw [sum_pathWeight]
  rfl

def overlapPartition (G : Matrix ι ι ℝ) (m : ℕ) : ℝ :=
  ∑ tau : Fin m → ι, ∑ sigma : Fin m → ι,
    ∏ j : Fin m, G (sigma j) (tau j) * G (sigma j) (tau (finRotate m j))

/-- Summing the shared sector labels gives ordinary matrix multiplication,
followed by the exact cyclic trace. -/
theorem overlapPartition_eq_trace (G : Matrix ι ι ℝ)
    (hG : ∀ i j, G i j = G j i) {m : ℕ} (hm : 0 < m) :
    overlapPartition G m = (G ^ (2 * m)).trace := by
  have hinner (tau : Fin m → ι) :
      (∑ sigma : Fin m → ι, ∏ j : Fin m,
        G (sigma j) (tau j) * G (sigma j) (tau (finRotate m j))) =
        ∏ j : Fin m, (G * G) (tau j) (tau (finRotate m j)) := by
    calc
      _ = ∏ j : Fin m, ∑ s : ι, G s (tau j) * G s (tau (finRotate m j)) :=
        (Fintype.prod_sum (fun j s => G s (tau j) * G s (tau (finRotate m j)))).symm
      _ = _ := by
        apply Finset.prod_congr rfl
        intro j _
        rw [Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro s _
        rw [hG s (tau j)]
  unfold overlapPartition
  simp_rw [hinner]
  change cyclePartition (G * G) m = _
  rw [cyclePartition_eq_trace _ hm, ← pow_two, ← pow_mul]

end
end TomographyOracleCore.Revision.FourthCycleContraction
