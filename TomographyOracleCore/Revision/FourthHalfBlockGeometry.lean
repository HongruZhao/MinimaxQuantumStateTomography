import TomographyOracleCore.Revision.FourthSectorBlocks
import TomographyOracleCore.ChoKimPeriodicNonclosingStepGeometry

namespace TomographyOracleCore.Revision.FourthHalfBlockGeometry

open scoped BigOperators
noncomputable section

def halfBlockCoordinateEquiv (m h : ℕ) : (Fin m × Fin 2) × Fin h ≃ Fin (m * (2 * h)) :=
  (Equiv.prodAssoc (Fin m) (Fin 2) (Fin h)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin m)) finProdFinEquiv).trans finProdFinEquiv)

theorem halfBlockCoordinateEquiv_val (m h : ℕ) (j : Fin m) (c : Fin 2) (a : Fin h) :
    (halfBlockCoordinateEquiv m h ((j, c), a)).val = j.val * (2 * h) + c.val * h + a.val := by
  change (a.val + h * c.val) + (2 * h) * j.val = _
  ring

def halfBlockRotation (m : ℕ) : Equiv.Perm (Fin m × Fin 2) where
  toFun x := if x.2 = 0 then (x.1, 1) else (finRotate m x.1, 0)
  invFun x := if x.2 = 0 then ((finRotate m).symm x.1, 1) else (x.1, 0)
  left_inv x := by
    rcases x with ⟨j, c⟩
    fin_cases c
    · rfl
    · change ((finRotate m).symm (finRotate m j), (1 : Fin 2)) = (j, 1)
      rw [Equiv.symm_apply_apply]
  right_inv x := by
    rcases x with ⟨j, c⟩
    fin_cases c
    · change (finRotate m ((finRotate m).symm j), (0 : Fin 2)) = (j, 0)
      rw [Equiv.apply_symm_apply]
    · rfl

theorem halfBlockRotation_zero (m : ℕ) (j : Fin m) :
    halfBlockRotation m (j, 0) = (j, 1) := by simp [halfBlockRotation]

theorem halfBlockRotation_one (m : ℕ) (j : Fin m) :
    halfBlockRotation m (j, 1) = (finRotate m j, 0) := by simp [halfBlockRotation]

/-- The actual cyclic qubit shift moves exactly one half-block. The final
half-block wraps around to the first, also when there is only one block. -/
theorem cyclicQubitShift_halfBlock
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (jc : Fin m × Fin 2) (a : Fin h) :
    cyclicQubitShift (m * (2 * h)) h (halfBlockCoordinateEquiv m h (jc, a)) =
      halfBlockCoordinateEquiv m h (halfBlockRotation m jc, a) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  rcases jc with ⟨j, c⟩
  have hN : 0 < (r + 1) * (2 * h) := by positivity
  have hs : h < (r + 1) * (2 * h) := by nlinarith
  apply Fin.ext
  rw [cyclicQubitShift_val hN hs, halfBlockCoordinateEquiv_val]
  by_cases hc : c = 0
  · subst c
    rw [halfBlockRotation_zero, halfBlockCoordinateEquiv_val]
    norm_num only [Fin.val_zero, Fin.val_one]
    have hmul := Nat.mul_le_mul_right (2 * h) (show j.val + 1 ≤ r + 1 from j.isLt)
    have hlt : j.val * (2 * h) + 0 * h + a.val + h < (r + 1) * (2 * h) := by
      have ha := a.isLt
      nlinarith
    rw [Nat.mod_eq_of_lt hlt]
    simp
    omega
  · have hc' : c = 1 := by
      have hcval : c.val ≠ 0 := fun he => hc (Fin.ext he)
      apply Fin.ext
      have hlt := c.isLt
      omega
    rw [hc', halfBlockRotation_one, halfBlockCoordinateEquiv_val]
    norm_num only [Fin.val_zero, Fin.val_one]
    by_cases hj : j = Fin.last r
    · subst j
      rw [finRotate_last]
      simp only [Fin.val_last, Fin.val_zero, one_mul, zero_mul, zero_add]
      have hsum : r * (2 * h) + h + a.val + h = (r + 1) * (2 * h) + a.val := by ring
      rw [hsum, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (a.isLt.trans hs)]
      exact Nat.mod_eq_of_lt (a.isLt.trans hs)
    · rw [coe_finRotate_of_ne_last hj]
      have hjlt : j.val < r := by
        have hjbound := j.isLt
        have hne : j.val ≠ r := fun he => hj (Fin.ext he)
        omega
      have hmul := Nat.mul_le_mul_right (2 * h) (show j.val + 1 ≤ r from hjlt)
      have hlt : j.val * (2 * h) + 1 * h + a.val + h < (r + 1) * (2 * h) := by
        have ha := a.isLt
        nlinarith
      rw [Nat.mod_eq_of_lt hlt]
      simp only [one_mul, zero_mul, add_zero]
      ring

def halfWordEquiv (m h : ℕ) :
    PauliBinaryWord (m * (2 * h)) ≃ ((Fin m × Fin 2) → PauliBinaryWord h) where
  toFun x jc a := x (halfBlockCoordinateEquiv m h (jc, a))
  invFun x i := x ((halfBlockCoordinateEquiv m h).symm i).1
    ((halfBlockCoordinateEquiv m h).symm i).2
  left_inv x := by
    funext i
    exact congrArg x ((halfBlockCoordinateEquiv m h).apply_symm_apply i)
  right_inv x := by
    funext jc a
    simp

theorem halfWordEquiv_shift_symm
    {m h : ℕ} (hm : 0 < m) (hh : 0 < h)
    (x : PauliBinaryWord (m * (2 * h))) (jc : Fin m × Fin 2) (a : Fin h) :
    halfWordEquiv m h ((permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h)).symm x) jc a =
      halfWordEquiv m h x (halfBlockRotation m jc) a := by
  change x (cyclicQubitShift (m * (2 * h)) h (halfBlockCoordinateEquiv m h (jc, a))) = _
  rw [cyclicQubitShift_halfBlock hm hh]
  rfl

end
end TomographyOracleCore.Revision.FourthHalfBlockGeometry
