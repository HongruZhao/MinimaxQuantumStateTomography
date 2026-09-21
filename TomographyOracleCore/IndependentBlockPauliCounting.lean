import TomographyOracleCore.CliffordPauliCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Independent finite-block action counting

This module turns the one-block uniform-orbit ratio into the exact product
ratio for independent block actions.  An `Option Ω` label records whether a
block is inactive (`none`) or carries a nontrivial label (`some q`).
-/

namespace TomographyOracleCore

open scoped BigOperators

section IndependentBlocks

variable {C Ω : Type*} [Group C] [Fintype C] [Fintype Ω]
  [DecidableEq C] [DecidableEq Ω] [MulAction C Ω]

/-- A local action succeeds automatically on an inactive block and must hit
`A` on an active block. -/
def blockActionHits (A : Finset Ω) (q : Option Ω) (c : C) : Prop :=
  match q with
  | none => True
  | some x => c • x ∈ A

instance instDecidableBlockActionHits
    (A : Finset Ω) (q : Option Ω) (c : C) :
    Decidable (blockActionHits A q c) := by
  cases q with
  | none => exact isTrue trivial
  | some x => exact Finset.decidableMem (c • x) A

/-- Number of active blocks in an optional block-label family. -/
noncomputable def activeBlockCount {m : ℕ} (Q : Fin m → Option Ω) : ℕ :=
  (Finset.univ.filter fun i ↦ Q i ≠ none).card

/-- Independent block choices satisfying every local hit condition. -/
abbrev IndependentBlockActionEvent {m : ℕ}
    (Q : Fin m → Option Ω) (A : Finset Ω) :=
  {c : Fin m → C // ∀ i, blockActionHits A (Q i) (c i)}

/-- A global block event is the dependent product of its local event
fibers. -/
noncomputable def independentBlockActionEventEquivPi {m : ℕ}
    (Q : Fin m → Option Ω) (A : Finset Ω) :
    IndependentBlockActionEvent (C := C) Q A ≃
      (∀ i, {c : C // blockActionHits A (Q i) c}) where
  toFun c i := ⟨c.1 i, c.2 i⟩
  invFun c := ⟨fun i ↦ (c i).1, fun i ↦ (c i).2⟩
  left_inv c := by ext i; rfl
  right_inv c := by funext i; exact Subtype.ext rfl

/-- One inactive block contributes probability one; one active block
contributes the uniform orbit fraction `|A| / |Ω|`. -/
theorem local_blockActionHits_ratio [MulAction.IsPretransitive C Ω]
    (q : Option Ω) (A : Finset Ω) :
    ((Fintype.card {c : C // blockActionHits A q c} : ℕ) : ℝ) /
        Fintype.card C =
      match q with
      | none => 1
      | some x => (A.card : ℝ) / Fintype.card Ω := by
  cases q with
  | none =>
      change
        ((Fintype.card {c : C // blockActionHits A (none : Option Ω) c} : ℕ) : ℝ) /
            Fintype.card C = 1
      let e : {c : C // blockActionHits A (none : Option Ω) c} ≃ C :=
        { toFun := fun c ↦ c.1
          invFun := fun c ↦ ⟨c, by simp [blockActionHits]⟩
          left_inv := fun c ↦ Subtype.ext rfl
          right_inv := fun c ↦ rfl }
      rw [Fintype.card_congr e]
      exact div_self (by positivity)
  | some x =>
      change
        ((Fintype.card {c : C // blockActionHits A (some x) c} : ℕ) : ℝ) /
            Fintype.card C = (A.card : ℝ) / Fintype.card Ω
      let e : {c : C // blockActionHits A (some x) c} ≃
          {c : C // c • x ∈ A} :=
        Equiv.subtypeEquivProp (by rfl)
      rw [Fintype.card_congr e]
      exact uniform_action_event_ratio (G := C) (x := x) A

/-- Exact product-uniformity formula for independent finite block actions. -/
theorem independentBlockActionEvent_ratio [MulAction.IsPretransitive C Ω]
    {m : ℕ} (Q : Fin m → Option Ω) (A : Finset Ω) :
    ((Fintype.card (IndependentBlockActionEvent (C := C) Q A) : ℕ) : ℝ) /
        Fintype.card (Fin m → C) =
      ((A.card : ℝ) / Fintype.card Ω) ^ activeBlockCount Q := by
  classical
  rw [Fintype.card_congr (independentBlockActionEventEquivPi Q A),
    Fintype.card_pi, Fintype.card_pi]
  push_cast
  rw [← Finset.prod_div_distrib]
  calc
    ∏ i : Fin m,
        ((Fintype.card {c : C // blockActionHits A (Q i) c} : ℕ) : ℝ) /
          Fintype.card C =
        ∏ i : Fin m, match Q i with
          | none => 1
          | some _ => (A.card : ℝ) / Fintype.card Ω := by
            apply Finset.prod_congr rfl
            intro i hi
            exact local_blockActionHits_ratio (C := C) (q := Q i) A
    _ = ∏ i : Fin m,
          if Q i ≠ none then (A.card : ℝ) / Fintype.card Ω else 1 := by
            apply Finset.prod_congr rfl
            intro i hi
            cases hq : Q i with
            | none => simp [hq]
            | some q => simp [hq]
    _ = ((A.card : ℝ) / Fintype.card Ω) ^ activeBlockCount Q := by
      rw [Finset.prod_ite]
      simp [activeBlockCount]
      rw [div_pow]

end IndependentBlocks

end TomographyOracleCore
