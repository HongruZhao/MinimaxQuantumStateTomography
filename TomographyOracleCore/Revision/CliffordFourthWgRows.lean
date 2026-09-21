import TomographyOracleCore.PeriodicCliffordFourthSectorSynthesis

namespace TomographyOracleCore.Revision.CliffordFourthWgRows

open scoped BigOperators
noncomputable section

private theorem list_weighted_sum
    {R : Type*} [CommSemiring R] (l : List ℕ) (f : ℕ → R)
    (hl : ∀ a ∈ l, a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4) :
    (l.map f).sum =
      (l.countP (fun a => a == 1) : R) * f 1 +
      (l.countP (fun a => a == 2) : R) * f 2 +
      (l.countP (fun a => a == 3) : R) * f 3 +
      (l.countP (fun a => a == 4) : R) * f 4 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ht : ∀ b ∈ l, b = 1 ∨ b = 2 ∨ b = 3 ∨ b = 4 := by
      intro b hb
      exact hl b (by simp [hb])
    have hi := ih ht
    rcases ha with rfl | rfl | rfl | rfl <;> simp [hi] <;> ring

theorem intersection_entry_weighted_sum
    {R : Type*} [CommSemiring R] (f : ℕ → R) (i : Fin 30) :
    (∑ j : Fin 30, f (qubitFourthIntersectionEntry i j)) =
      8 * f 1 + 14 * f 2 + 7 * f 3 + f 4 := by
  have hl : ∀ a ∈ (List.finRange 30).map (qubitFourthIntersectionEntry i),
      a = 1 ∨ a = 2 ∨ a = 3 ∨ a = 4 := by
    intro a ha
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    have hb := qubitFourthIntersectionEntry_bounds i j
    omega
  have h := list_weighted_sum ((List.finRange 30).map (qubitFourthIntersectionEntry i)) f hl
  simp only [List.map_map, Function.comp_def, List.countP_map] at h
  change ((List.finRange 30).map (fun j => f (qubitFourthIntersectionEntry i j))).sum =
    (qubitFourthRowCount i 1 : R) * f 1 + (qubitFourthRowCount i 2 : R) * f 2 +
      (qubitFourthRowCount i 3 : R) * f 3 + (qubitFourthRowCount i 4 : R) * f 4 at h
  rw [qubitFourthRowCount_one, qubitFourthRowCount_two,
    qubitFourthRowCount_three, qubitFourthRowCount_four] at h
  simpa only [← List.ofFn_eq_map, List.sum_ofFn, Nat.cast_ofNat, Nat.cast_one, one_mul] using h

/-- The exact four-value row profile, with arbitrary scalar weights. -/
theorem intersection_class_weighted_sum
    {R : Type*} [CommSemiring R] (f : Fin 5 → R) (i : Fin 30) :
    (∑ j : Fin 30, f (qubitFourthIntersectionClass i j)) =
      8 * f 1 + 14 * f 2 + 7 * f 3 + f 4 := by
  let g : ℕ → R := fun a => if h : a < 5 then f ⟨a, h⟩ else 0
  have hg (j : Fin 30) : g (qubitFourthIntersectionEntry i j) =
      f (qubitFourthIntersectionClass i j) := by
    dsimp [g]
    have hb : qubitFourthIntersectionEntry i j < 5 := by
      have h := qubitFourthIntersectionEntry_bounds i j
      omega
    rw [dif_pos hb]
    rfl
  have h := intersection_entry_weighted_sum g i
  simp only [hg] at h
  simpa [g] using h

theorem complexWg_signed_row_sum (x : ℝ) (i : Fin 30) :
    (∑ j : Fin 30, qubitFourthComplexWgMatrix x i j) =
      (cliffordFourthWgSignedRowSum x : ℂ) := by
  have h := intersection_class_weighted_sum
    (fun a : Fin 5 => (qubitFourthWgCoefficient a x : ℂ)) i
  simpa [qubitFourthComplexWgMatrix, qubitFourthWgCoefficient,
    cliffordFourthWgSignedRowSum] using h

theorem complexWg_absolute_row_sum (x : ℝ) (i : Fin 30) :
    (∑ j : Fin 30, ‖qubitFourthComplexWgMatrix x i j‖) =
      cliffordFourthWgAbsoluteRowSum x := by
  have h := intersection_class_weighted_sum
    (fun a : Fin 5 => |qubitFourthWgCoefficient a x|) i
  simpa [qubitFourthComplexWgMatrix, Complex.norm_real, Real.norm_eq_abs,
    qubitFourthWgCoefficient, cliffordFourthWgAbsoluteRowSum] using h

end
end TomographyOracleCore.Revision.CliffordFourthWgRows
