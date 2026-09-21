import TomographyOracleCore.Revision.FourthCycleContraction
import TomographyOracleCore.Revision.CliffordFourthWgRows
import TomographyOracleCore.PeriodicCliffordFourthU4Abstract

namespace TomographyOracleCore.Revision.FourthSectorExpansionBound

open FourthCycleContraction
open scoped BigOperators
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem productWeights_boundary_bound
    (W : Matrix ι ι ℂ) (a : ℝ) (hrow : ∀ i, ∑ j, ‖W i j‖ = a)
    (m : ℕ) (sigma : Fin m → ι) (c : (Fin m → ι) → ℂ)
    (hc : ∀ zeta, ‖c zeta‖ ≤ 1) :
    ‖∑ zeta : Fin m → ι, (∏ j : Fin m, W (sigma j) (zeta j)) * c zeta‖ ≤ a ^ m := by
  calc
    _ ≤ ∑ zeta : Fin m → ι, ∏ j : Fin m, ‖W (sigma j) (zeta j)‖ := by
      apply norm_sum_le_of_le
      intro zeta _
      rw [norm_mul, norm_prod]
      exact (mul_le_mul_of_nonneg_left (hc zeta)
        (Finset.prod_nonneg fun _ _ => norm_nonneg _)).trans_eq (mul_one _)
    _ = ∏ j : Fin m, ∑ z : ι, ‖W (sigma j) z‖ :=
      (Fintype.prod_sum (fun j z => ‖W (sigma j) z‖)).symm
    _ = a ^ m := by simp only [hrow, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def sectorExpansion (G : Matrix ι ι ℝ) (W : Matrix ι ι ℂ) (m : ℕ)
    (c : (Fin m → ι) → ℂ) : ℂ :=
  ∑ tau : Fin m → ι, ∑ sigma : Fin m → ι,
    ((∏ j : Fin m, G (sigma j) (tau j) * G (sigma j) (tau (finRotate m j)) : ℝ) : ℂ) *
      ∑ zeta : Fin m → ι, (∏ j : Fin m, W (sigma j) (zeta j)) * c zeta

/-- Taking absolute values only after the exact overlap expansion gives the
absolute Weingarten row sum times the nonnegative cycle partition. -/
theorem norm_sectorExpansion_le
    (G : Matrix ι ι ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (W : Matrix ι ι ℂ) (a : ℝ) (hrow : ∀ i, ∑ j, ‖W i j‖ = a)
    (m : ℕ) (c : (Fin m → ι) → ℂ) (hc : ∀ zeta, ‖c zeta‖ ≤ 1) :
    ‖sectorExpansion G W m c‖ ≤ a ^ m * overlapPartition G m := by
  unfold sectorExpansion overlapPartition
  rw [Finset.mul_sum]
  apply norm_sum_le_of_le
  intro tau _
  rw [Finset.mul_sum]
  apply norm_sum_le_of_le
  intro sigma _
  have hp : 0 ≤ ∏ j : Fin m, G (sigma j) (tau j) * G (sigma j) (tau (finRotate m j)) :=
    Finset.prod_nonneg fun _ _ => mul_nonneg (hG _ _) (hG _ _)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp]
  calc
    _ ≤ (∏ j : Fin m, G (sigma j) (tau j) * G (sigma j) (tau (finRotate m j))) * a ^ m :=
      mul_le_mul_of_nonneg_left (productWeights_boundary_bound W a hrow m sigma c hc) hp
    _ = _ := mul_comm _ _

theorem norm_sectorExpansion_le_trace
    (G : Matrix ι ι ℝ) (hG : ∀ i j, 0 ≤ G i j)
    (hSymm : ∀ i j, G i j = G j i)
    (W : Matrix ι ι ℂ) (a : ℝ) (hrow : ∀ i, ∑ j, ‖W i j‖ = a)
    {m : ℕ} (hm : 0 < m) (c : (Fin m → ι) → ℂ) (hc : ∀ zeta, ‖c zeta‖ ≤ 1) :
    ‖sectorExpansion G W m c‖ ≤ a ^ m * (G ^ (2 * m)).trace := by
  have h := norm_sectorExpansion_le G hG W a hrow m c hc
  rwa [overlapPartition_eq_trace G hSymm hm] at h

end
end TomographyOracleCore.Revision.FourthSectorExpansionBound
