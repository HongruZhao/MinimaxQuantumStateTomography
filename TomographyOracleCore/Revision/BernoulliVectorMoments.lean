import TomographyOracleCore.Revision.BernoulliFiniteAverage
import Mathlib.Analysis.InnerProductSpace.Basic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace TomographyOracleCore.Revision.BernoulliVectorMoments

open FiniteProbabilityAverage BernoulliFiniteAverage
open scoped BigOperators InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def selectedVectorSum {N : ℕ} (U : Fin N → E) (omega : Fin N → Bool) : E :=
  ∑ i, bitValue (omega i) • U i

theorem selectedVectorSum_cons {N : ℕ} (U : Fin (N + 1) → E) (b : Bool) (omega : Fin N → Bool) :
    selectedVectorSum U (Fin.cons b omega) =
      bitValue b • U 0 + selectedVectorSum (fun i => U i.succ) omega := by
  simp [selectedVectorSum, Fin.sum_univ_succ]

theorem inner_selectedVectorSum {N : ℕ} (U : Fin N → E) (v : E) (omega : Fin N → Bool) :
    ⟪selectedVectorSum U omega, v⟫_ℝ = selectedSum (fun i => ⟪U i, v⟫_ℝ) omega := by
  simp [selectedVectorSum, selectedSum, sum_inner, real_inner_smul_left, mul_comm]

theorem average_selected_inner (p : ℝ) (hp : p ∈ Set.Icc 0 1) {N : ℕ} (U : Fin N → E) (v : E) :
    average (bernoulliLaw p hp N) (fun omega => ⟪selectedVectorSum U omega, v⟫_ℝ) =
      p * ⟪∑ i, U i, v⟫_ℝ := by
  simp_rw [inner_selectedVectorSum]
  rw [average_selectedSum, ← sum_inner]

theorem average_inner_selected (p : ℝ) (hp : p ∈ Set.Icc 0 1) {N : ℕ} (U : Fin N → E) (v : E) :
    average (bernoulliLaw p hp N) (fun omega => ⟪v, selectedVectorSum U omega⟫_ℝ) =
      p * ⟪v, ∑ i, U i⟫_ℝ := by
  calc
    _ = average (bernoulliLaw p hp N) (fun omega => ⟪selectedVectorSum U omega, v⟫_ℝ) :=
      average_congr _ (fun _ => real_inner_comm _ _)
    _ = p * ⟪∑ i, U i, v⟫_ℝ := average_selected_inner p hp U v
    _ = _ := congrArg (fun z : ℝ => p * z) (real_inner_comm _ _)

/-- The exact second moment of a Bernoulli-selected vector sum. -/
theorem average_selectedVector_norm_sq (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {N : ℕ} (U : Fin N → E) :
    average (bernoulliLaw p hp N) (fun omega => ‖selectedVectorSum U omega‖ ^ 2) =
      p ^ 2 * ‖∑ i, U i‖ ^ 2 + p * (1 - p) * ∑ i, ‖U i‖ ^ 2 := by
  induction N with
  | zero => simp [selectedVectorSum]
  | succ N ih =>
    rw [average_succ]
    simp only [selectedVectorSum_cons, bitValue, if_true, Bool.false_eq_true, if_false,
      one_smul, zero_smul, zero_add]
    have ht : average (bernoulliLaw p hp N)
        (fun omega => ‖U 0 + selectedVectorSum (fun i => U i.succ) omega‖ ^ 2) =
        ‖U 0‖ ^ 2 + 2 * (p * ⟪U 0, ∑ i : Fin N, U i.succ⟫_ℝ) +
          average (bernoulliLaw p hp N)
            (fun omega => ‖selectedVectorSum (fun i => U i.succ) omega‖ ^ 2) := by
      simp_rw [norm_add_sq_real]
      rw [average_add, average_add, average_const, average_const_mul, average_inner_selected]
    rw [ht, ih, Fin.sum_univ_succ, Fin.sum_univ_succ, norm_add_sq_real]
    ring

/-- Averaging over partitions recovers one quarter of the off-diagonal
quadratic form when p=1/2. This identity holds in every real Hilbert space. -/
theorem average_selected_complement_inner (p : ℝ) (hp : p ∈ Set.Icc 0 1)
    {N : ℕ} (U : Fin N → E) :
    average (bernoulliLaw p hp N)
      (fun omega => ⟪selectedVectorSum U omega, (∑ i, U i) - selectedVectorSum U omega⟫_ℝ) =
      p * (1 - p) * (‖∑ i, U i‖ ^ 2 - ∑ i, ‖U i‖ ^ 2) := by
  simp_rw [inner_sub_right, real_inner_self_eq_norm_sq]
  rw [average_sub, average_selected_inner, real_inner_self_eq_norm_sq,
    average_selectedVector_norm_sq]
  ring

end
end TomographyOracleCore.Revision.BernoulliVectorMoments
