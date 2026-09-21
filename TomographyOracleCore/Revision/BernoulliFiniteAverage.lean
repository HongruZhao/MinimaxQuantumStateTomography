import TomographyOracleCore.Revision.FiniteProbabilityAverage

namespace TomographyOracleCore.Revision.BernoulliFiniteAverage

open FiniteProbabilityAverage
open scoped BigOperators
noncomputable section

def coinWeight (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

def bernoulliLaw (p : ℝ) (hp : p ∈ Set.Icc 0 1) (k : ℕ) : Law (Fin k → Bool) where
  weight omega := ∏ i, coinWeight p (omega i)
  nonneg omega := Finset.prod_nonneg fun i _ => by
    cases h : omega i <;> simp [coinWeight, h] <;> linarith [hp.1, hp.2]
  total := by
    rw [← Fintype.prod_sum]
    simp [Fintype.sum_bool, coinWeight]

def consEquiv (k : ℕ) : (Bool × (Fin k → Bool)) ≃ (Fin (k + 1) → Bool) where
  toFun z := Fin.cons z.1 z.2
  invFun omega := (omega 0, fun i => omega i.succ)
  left_inv z := by cases z; rfl
  right_inv omega := by funext i; cases i using Fin.cases <;> rfl

@[simp] theorem average_zero (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    (f : (Fin 0 → Bool) → ℝ) :
    average (bernoulliLaw p hp 0) f = f Fin.elim0 := by
  have hf : f = fun _ => f Fin.elim0 := by
    funext omega
    exact congrArg f (Subsingleton.elim omega Fin.elim0)
  rw [hf, average_const]

theorem average_succ (p : ℝ) (hp : p ∈ Set.Icc 0 1) (k : ℕ)
    (f : (Fin (k + 1) → Bool) → ℝ) :
    average (bernoulliLaw p hp (k + 1)) f =
      p * average (bernoulliLaw p hp k) (fun omega => f (Fin.cons true omega)) +
        (1 - p) * average (bernoulliLaw p hp k) (fun omega => f (Fin.cons false omega)) := by
  unfold average
  rw [← (consEquiv k).sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, consEquiv, Equiv.coe_fn_mk,
    bernoulliLaw, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, coinWeight,
    Bool.false_eq_true, if_false, if_true, mul_assoc, ← Finset.mul_sum]

theorem average_succ_inside (p : ℝ) (hp : p ∈ Set.Icc 0 1) (k : ℕ)
    (f : (Fin (k + 1) → Bool) → ℝ) :
    average (bernoulliLaw p hp (k + 1)) f =
      average (bernoulliLaw p hp k) (fun omega =>
        p * f (Fin.cons true omega) + (1 - p) * f (Fin.cons false omega)) := by
  rw [average_add, average_const_mul, average_const_mul, average_succ]

def bitValue (b : Bool) : ℝ := if b then 1 else 0

def selectedSum {k : ℕ} (a : Fin k → ℝ) (omega : Fin k → Bool) : ℝ :=
  ∑ i, a i * bitValue (omega i)

def centeredSum {k : ℕ} (p : ℝ) (a : Fin k → ℝ) (omega : Fin k → Bool) : ℝ :=
  ∑ i, a i * (bitValue (omega i) - p)

@[simp] theorem selectedSum_cons {k : ℕ} (a : Fin (k + 1) → ℝ)
    (b : Bool) (omega : Fin k → Bool) :
    selectedSum a (Fin.cons b omega) =
      a 0 * bitValue b + selectedSum (fun i => a i.succ) omega := by
  simp only [selectedSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

@[simp] theorem centeredSum_cons {k : ℕ} (p : ℝ) (a : Fin (k + 1) → ℝ)
    (b : Bool) (omega : Fin k → Bool) :
    centeredSum p a (Fin.cons b omega) =
      a 0 * (bitValue b - p) + centeredSum p (fun i => a i.succ) omega := by
  simp only [centeredSum, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem selectedSum_eq_centeredSum_add {k : ℕ} (p : ℝ) (a : Fin k → ℝ)
    (omega : Fin k → Bool) :
    selectedSum a omega = centeredSum p a omega + p * ∑ i, a i := by
  simp only [selectedSum, centeredSum, mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  ring

theorem average_centeredSum (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) : average (bernoulliLaw p hp k) (centeredSum p a) = 0 := by
  induction k with
  | zero => simp [centeredSum]
  | succ k ih =>
    rw [average_succ_inside]
    calc
      _ = average (bernoulliLaw p hp k) (centeredSum p (fun i => a i.succ)) := by
        apply average_congr
        intro omega
        simp only [centeredSum_cons, bitValue, if_true, Bool.false_eq_true, if_false]
        ring
      _ = 0 := ih _

theorem average_selectedSum (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {k : ℕ} (a : Fin k → ℝ) :
    average (bernoulliLaw p hp k) (selectedSum a) = p * ∑ i, a i := by
  rw [show selectedSum a = (fun omega => centeredSum p a omega + p * ∑ i, a i)
    from funext (selectedSum_eq_centeredSum_add p a)]
  rw [average_add, average_const, average_centeredSum, zero_add]

end
end TomographyOracleCore.Revision.BernoulliFiniteAverage
