import TomographyOracleCore.OrderedSpectral
namespace TomographyOracleCore.MatrixReduction
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1000000

theorem eigenvalues_orderedIndex_symm (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (j : Fin (Fintype.card ι)) :
    hA.eigenvalues (orderedEigenIndex.symm j) = hA.eigenvalues₀ j := by
  change hA.eigenvalues₀ (orderedEigenIndex (orderedEigenIndex.symm j)) = _
  rw [Equiv.apply_symm_apply]

/-- Matrix rank bounds force the actual ordered eigenvalue tail to vanish. -/
theorem orderedSpectralTail_eq_zero_of_rank_le (rho : DensityOperator ι)
    (s : ℕ) (hrank : rho.matrix.rank ≤ s) : orderedSpectralTail rho s = 0 := by
  have heigen : ∀ j : Fin (Fintype.card ι), s ≤ j.val → rho.isHermitian.eigenvalues₀ j = 0 := by
    intro j hsj
    by_contra hne
    have hjpos : 0 < rho.isHermitian.eigenvalues₀ j :=
      lt_of_le_of_ne (density_eigenvalues₀_nonneg rho j) (Ne.symm hne)
    let f : Fin (j.val + 1) → {i : ι // rho.isHermitian.eigenvalues i ≠ 0} := fun i =>
      ⟨orderedEigenIndex.symm ⟨i.val, by omega⟩, by
        rw [eigenvalues_orderedIndex_symm]
        have hi : (⟨i.val, by omega⟩ : Fin (Fintype.card ι)) ≤ j := by
          change i.val ≤ j.val
          exact Nat.le_of_lt_succ i.isLt
        have hp := rho.isHermitian.eigenvalues₀_antitone hi
        exact ne_of_gt (hjpos.trans_le hp)⟩
    have hf : Function.Injective f := by
      intro i k hik
      have hi : i.val = k.val := by
        simpa only [f, Equiv.apply_symm_apply] using
          congrArg (fun z => (orderedEigenIndex z.val).val) hik
      exact Fin.ext hi
    have hc := Fintype.card_le_of_injective f hf
    rw [Fintype.card_fin, ← rho.isHermitian.rank_eq_card_non_zero_eigs] at hc
    omega
  unfold orderedSpectralTail
  apply Finset.sum_eq_zero
  intro j hj
  split_ifs with hsj
  · exact heigen j hsj
  · rfl

end
end TomographyOracleCore.MatrixReduction
