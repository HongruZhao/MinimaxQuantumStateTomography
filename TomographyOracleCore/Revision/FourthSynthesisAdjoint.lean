import TomographyOracleCore.Revision.CliffordFourthProductProjection

namespace TomographyOracleCore.Revision.FourthSynthesisAdjoint

open CliffordFourthProductProjection
open scoped BigOperators
noncomputable section

theorem hilbertSchmidt_star {ι : Type*} [Fintype ι] (A B : Matrix ι ι ℂ) :
    star (qubitFourthComplexHilbertSchmidt A B) = qubitFourthComplexHilbertSchmidt B A := by
  simp only [qubitFourthComplexHilbertSchmidt_eq_entrywise, star_sum, star_mul, star_star]

theorem familySynthesis_selfAdjoint
    {ι L : Type*} [Fintype ι] [Fintype L]
    (S : L → Matrix ι ι ℂ) (W : Matrix L L ℂ)
    (hW : ∀ i j, star (W i j) = W j i) (X Y : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt Y (familySynthesis S W X) =
      qubitFourthComplexHilbertSchmidt (familySynthesis S W Y) X := by
  simp only [familySynthesis_apply, qubitFourthComplexHilbertSchmidt_sum_right,
    qubitFourthComplexHilbertSchmidt_sum_left, qubitFourthComplexHilbertSchmidt_smul_right,
    qubitFourthComplexHilbertSchmidt_smul_left, star_mul, hilbertSchmidt_star, hW]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem complexWg_star (x : ℝ) (i j : Fin 30) :
    star (qubitFourthComplexWgMatrix x i j) = qubitFourthComplexWgMatrix x j i := by
  calc
    _ = qubitFourthComplexWgMatrix x i j := by simp [qubitFourthComplexWgMatrix]
    _ = _ := qubitFourthComplexWgMatrix_comm x i j

theorem blockWg_star {J : Type*} [Fintype J] [DecidableEq J]
    (K : ℕ) (i j : J → Fin 30) :
    star (blockWgMatrix K i j) = blockWgMatrix K j i := by
  simp only [blockWgMatrix, star_prod, complexWg_star]

/-- The exact physical block average is self-adjoint. This is proved from
the Hermitian inverse-Gram formula, without an assumption that a chosen
section of Clifford gates is closed under inversion. -/
theorem blockFourthAverage_selfAdjoint
    {J : Type*} [Fintype J] [DecidableEq J] {K : ℕ} (hK : 3 ≤ K)
    (X Y : Matrix (FourthIndex (J → PauliBinaryWord K)) (FourthIndex (J → PauliBinaryWord K)) ℂ) :
    qubitFourthComplexHilbertSchmidt Y (blockFourthAverage K X) =
      qubitFourthComplexHilbertSchmidt (blockFourthAverage K Y) X := by
  rw [blockFourthAverage_eq_synthesis hK]
  exact familySynthesis_selfAdjoint _ _ (blockWg_star K) X Y

end
end TomographyOracleCore.Revision.FourthSynthesisAdjoint
