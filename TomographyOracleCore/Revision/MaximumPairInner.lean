import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.MaximumPairInner

open scoped BigOperators InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairValue (X : ι → E) : Option (ι × ι) → ℝ
  | none => 0
  | some (i, j) => if i = j then 0 else |⟪X i, X j⟫_ℝ|

def maximumPair (X : ι → E) : ℝ := Finset.univ.sup' Finset.univ_nonempty (pairValue X)

theorem pairValue_nonneg (X : ι → E) (p : Option (ι × ι)) : 0 ≤ pairValue X p := by
  cases p with
  | none => rfl
  | some p => dsimp [pairValue]; split_ifs <;> positivity

theorem pairValue_le_maximumPair (X : ι → E) (p : Option (ι × ι)) : pairValue X p ≤ maximumPair X :=
  Finset.le_sup' (pairValue X) (Finset.mem_univ p)

theorem maximumPair_nonneg (X : ι → E) : 0 ≤ maximumPair X :=
  pairValue_le_maximumPair X none

theorem abs_inner_le_maximumPair (X : ι → E) (i j : ι) (hij : i ≠ j) :
    |⟪X i, X j⟫_ℝ| ≤ maximumPair X := by
  simpa [pairValue, hij] using pairValue_le_maximumPair X (some (i, j))

theorem abs_inner_le_of_fixedNorm {x y : E} {q : ℝ}
    (hx : ‖x‖ ^ 2 = q) (hy : ‖y‖ ^ 2 = q) : |⟪x, y⟫_ℝ| ≤ q := by
  have hn : ‖x‖ = ‖y‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hx.trans hy.symm)
  calc
    _ ≤ ‖x‖ * ‖y‖ := abs_real_inner_le_norm _ _
    _ = q := by rw [← hn]; nlinarith [hx]

theorem pairValue_le_fixedNorm (X : ι → E) {q : ℝ} (hq : 0 ≤ q)
    (hfixed : ∀ i, ‖X i‖ ^ 2 = q) (p : Option (ι × ι)) : pairValue X p ≤ q := by
  cases p with
  | none => exact hq
  | some p =>
    dsimp [pairValue]
    split_ifs
    · exact hq
    · exact abs_inner_le_of_fixedNorm (hfixed p.1) (hfixed p.2)

theorem maximumPair_le_fixedNorm (X : ι → E) {q : ℝ} (hq : 0 ≤ q)
    (hfixed : ∀ i, ‖X i‖ ^ 2 = q) : maximumPair X ≤ q := by
  apply Finset.sup'_le
  intro p hp
  exact pairValue_le_fixedNorm X hq hfixed p

theorem continuous_pairValue (p : Option (ι × ι)) : Continuous (fun X : ι → E => pairValue X p) := by
  cases p with
  | none => exact continuous_const
  | some p =>
    dsimp [pairValue]
    split_ifs
    · exact continuous_const
    · have h : Continuous (fun X : ι → E => ⟪X p.1, X p.2⟫_ℝ) := by fun_prop
      simpa only [Real.norm_eq_abs] using h.norm

theorem continuous_maximumPair : Continuous (maximumPair : (ι → E) → ℝ) := by
  unfold maximumPair
  exact Continuous.finset_sup'_apply Finset.univ_nonempty (fun p _ => continuous_pairValue p)

theorem maximumPair_sixth_le_sum (X : ι → E) :
    maximumPair X ^ 6 ≤ ∑ p : Option (ι × ι), pairValue X p ^ 6 := by
  obtain ⟨p, hp, heq⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (pairValue X)
  change maximumPair X = pairValue X p at heq
  rw [heq]
  exact Finset.single_le_sum (f := fun p => pairValue X p ^ 6) (fun p _ => by positivity) hp

end
end TomographyOracleCore.Revision.MaximumPairInner
