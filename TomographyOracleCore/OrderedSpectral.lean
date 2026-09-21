import TomographyOracleCore.MatrixReduction

namespace TomographyOracleCore.MatrixReduction

open scoped ComplexOrder InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
# Ordered spectral tails

This file constructs the leading spectral projection using Mathlib's ordered
eigenvalue indexing `eigenvalues₀`.  It then identifies the complementary
block trace with the ordered eigenvalue tail and discharges every structural
premise of `density_projection_cone`.
-/

/-- Convert the ambient matrix index into Mathlib's ordered eigenvalue index. -/
noncomputable def orderedEigenIndex : ι ≃ Fin (Fintype.card ι) :=
  (Fintype.equivOfCardEq (Fintype.card_fin _)).symm

/-- Indicator of the first `s` ordered eigenvectors. -/
noncomputable def leadingSpectralCoeff (s : ℕ) (i : ι) : ℂ :=
  if (orderedEigenIndex i).val < s then 1 else 0

/-- Orthogonal projection onto the first `s` ordered eigenvectors of `rho`. -/
noncomputable def leadingSpectralProjection
    (ρ : DensityOperator ι) (s : ℕ) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ ρ.isHermitian.eigenvectorUnitary
    (Matrix.diagonal (leadingSpectralCoeff s))

/-- Sum of the ordered eigenvalues with index at least `s`. -/
noncomputable def orderedSpectralTail
    (ρ : DensityOperator ι) (s : ℕ) : ℝ :=
  ∑ j : Fin (Fintype.card ι),
    if s ≤ j.val then ρ.isHermitian.eigenvalues₀ j else 0

theorem leadingSpectralCoeff_isSelfAdjoint (s : ℕ) (i : ι) :
    IsSelfAdjoint (leadingSpectralCoeff s i) := by
  unfold leadingSpectralCoeff
  split_ifs <;> simp

theorem leadingSpectralProjection_isHermitian
    (ρ : DensityOperator ι) (s : ℕ) :
    (leadingSpectralProjection ρ s).IsHermitian := by
  let e := Unitary.conjStarAlgAut ℂ _ ρ.isHermitian.eigenvectorUnitary
  have hd : (Matrix.diagonal (leadingSpectralCoeff s) : Matrix ι ι ℂ).IsHermitian :=
    Matrix.isHermitian_diagonal_iff.mpr
      (leadingSpectralCoeff_isSelfAdjoint s)
  rw [Matrix.IsHermitian]
  change star (e (Matrix.diagonal (leadingSpectralCoeff s))) =
    e (Matrix.diagonal (leadingSpectralCoeff s))
  rw [← map_star]
  exact congrArg e hd.eq

theorem leadingSpectralCoeff_mul_self (s : ℕ) (i : ι) :
    leadingSpectralCoeff s i * leadingSpectralCoeff s i =
      leadingSpectralCoeff s i := by
  unfold leadingSpectralCoeff
  split_ifs <;> simp

theorem leadingSpectralProjection_isIdempotent
    (ρ : DensityOperator ι) (s : ℕ) :
    IsIdempotentElem (leadingSpectralProjection ρ s) := by
  let e := Unitary.conjStarAlgAut ℂ _ ρ.isHermitian.eigenvectorUnitary
  change e (Matrix.diagonal (leadingSpectralCoeff s)) *
      e (Matrix.diagonal (leadingSpectralCoeff s)) =
    e (Matrix.diagonal (leadingSpectralCoeff s))
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [leadingSpectralCoeff_mul_self]
  · simp [hij]

theorem leadingSpectralProjection_operatorNorm_le_one
    (ρ : DensityOperator ι) (s : ℕ) :
    matrixOperatorNorm (leadingSpectralProjection ρ s) ≤ 1 := by
  open scoped Matrix.Norms.L2Operator in
    change ‖leadingSpectralProjection ρ s‖ ≤ 1
    simp only [leadingSpectralProjection, Unitary.conjStarAlgAut_apply,
      ← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
      CStarRing.norm_coe_unitary_mul, Matrix.l2_opNorm_diagonal]
    apply pi_norm_le_iff_of_nonneg zero_le_one |>.2
    intro i
    unfold leadingSpectralCoeff
    split_ifs <;> norm_num

theorem leadingSpectralProjection_rank_eq_card
    (ρ : DensityOperator ι) (s : ℕ) :
    (leadingSpectralProjection ρ s).rank =
      Fintype.card {i : ι // leadingSpectralCoeff s i ≠ 0} := by
  let U := ρ.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (leadingSpectralCoeff s)
  have hU : IsUnit (U : Matrix ι ι ℂ) := Unitary.isUnit_coe
  have hUdet : IsUnit (U : Matrix ι ι ℂ).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hSU : IsUnit (star (U : Matrix ι ι ℂ)) := hU.star
  have hSUdet : IsUnit (star (U : Matrix ι ι ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSU
  change (U * D * star (U : Matrix ι ι ℂ)).rank = _
  calc
    (U * D * star (U : Matrix ι ι ℂ)).rank = (U * D).rank :=
      Matrix.rank_mul_eq_left_of_isUnit_det _ _ hSUdet
    _ = D.rank := Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUdet
    _ = _ := Matrix.rank_diagonal _

theorem leadingSpectralCoeff_ne_zero_iff (s : ℕ) (i : ι) :
    leadingSpectralCoeff s i ≠ 0 ↔ (orderedEigenIndex i).val < s := by
  unfold leadingSpectralCoeff
  split_ifs with h
  · simp [h]
  · simp [h]

theorem leadingSpectralProjection_rank_le
    (ρ : DensityOperator ι) (s : ℕ) :
    (leadingSpectralProjection ρ s).rank ≤ s := by
  rw [leadingSpectralProjection_rank_eq_card]
  let f : {i : ι // leadingSpectralCoeff s i ≠ 0} → Fin s := fun i =>
    ⟨(orderedEigenIndex i.1).val,
      (leadingSpectralCoeff_ne_zero_iff s i.1).mp i.2⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply orderedEigenIndex.injective
    apply Fin.ext
    simpa [f] using congrArg Fin.val hij
  simpa using Fintype.card_le_of_injective f hf

theorem leadingSpectralProjection_complement_trace_eq_reindexed_tail
    (ρ : DensityOperator ι) (s : ℕ) :
    let P := leadingSpectralProjection ρ s
    let Q := 1 - P
    (Q * ρ.matrix * Q).trace.re =
      ∑ i : ι, if s ≤ (orderedEigenIndex i).val then
        ρ.isHermitian.eigenvalues i else 0 := by
  dsimp
  let e := Unitary.conjStarAlgAut ℂ _ ρ.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (leadingSpectralCoeff s)
  let E : Matrix ι ι ℂ :=
    Matrix.diagonal (RCLike.ofReal ∘ ρ.isHermitian.eigenvalues)
  have hidP := leadingSpectralProjection_isIdempotent ρ s
  rw [trace_sandwich_of_isIdempotent (1 - leadingSpectralProjection ρ s)
    ρ.matrix (isIdempotentElem_one_sub _ hidP)]
  conv_lhs => rw [ρ.isHermitian.spectral_theorem]
  change ((1 - e D) * e E).trace.re = _
  have hsub : 1 - e D = e (1 - D) := by
    simpa using (e.map_sub (1 : Matrix ι ι ℂ) D).symm
  rw [hsub]
  have hprod : e (1 - D) * e E = e ((1 - D) * E) := by
    exact (e.map_mul (1 - D) E).symm
  rw [hprod]
  change (e ((1 - D) * E)).trace.re = _
  simp only [e, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul]
  simp only [D, E, Matrix.trace_sub, Matrix.trace_diagonal, sub_mul,
    one_mul, Matrix.diagonal_mul_diagonal, Function.comp_apply]
  rw [← Finset.sum_sub_distrib]
  change Complex.reCLM (∑ i, ((ρ.isHermitian.eigenvalues i : ℂ) -
    leadingSpectralCoeff s i * (ρ.isHermitian.eigenvalues i : ℂ))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hlt : (orderedEigenIndex i).val < s
  · have hnle : ¬s ≤ (orderedEigenIndex i).val := Nat.not_le_of_lt hlt
    simp [leadingSpectralCoeff, hlt, hnle]
  · have hle' : s ≤ (orderedEigenIndex i).val := Nat.le_of_not_gt hlt
    simp [leadingSpectralCoeff, hlt, hle']

theorem reindexedSpectralTail_eq_orderedSpectralTail
    (ρ : DensityOperator ι) (s : ℕ) :
    (∑ i : ι, if s ≤ (orderedEigenIndex i).val then
        ρ.isHermitian.eigenvalues i else 0) =
      orderedSpectralTail ρ s := by
  unfold orderedSpectralTail
  rw [← Equiv.sum_comp orderedEigenIndex (fun j =>
    if s ≤ j.val then ρ.isHermitian.eigenvalues₀ j else 0)]
  apply Finset.sum_congr rfl
  intro i hi
  unfold Matrix.IsHermitian.eigenvalues orderedEigenIndex
  rfl

/-- The complementary trace of the ordered leading spectral projection is
exactly the ordered eigenvalue tail. -/
theorem leadingSpectralProjection_complement_trace_eq_tail
    (ρ : DensityOperator ι) (s : ℕ) :
    let P := leadingSpectralProjection ρ s
    let Q := 1 - P
    (Q * ρ.matrix * Q).trace.re = orderedSpectralTail ρ s := by
  dsimp
  rw [leadingSpectralProjection_complement_trace_eq_reindexed_tail,
    reindexedSpectralTail_eq_orderedSpectralTail]

theorem density_eigenvalues₀_nonneg
    (ρ : DensityOperator ι) (j : Fin (Fintype.card ι)) :
    0 ≤ ρ.isHermitian.eigenvalues₀ j := by
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin _)
  have h := ρ.posSemidef.eigenvalues_nonneg (e j)
  simpa [Matrix.IsHermitian.eigenvalues, e] using h

theorem orderedSpectralTail_nonneg
    (ρ : DensityOperator ι) (s : ℕ) :
    0 ≤ orderedSpectralTail ρ s := by
  unfold orderedSpectralTail
  apply Finset.sum_nonneg
  intro j hj
  split_ifs
  · exact density_eigenvalues₀_nonneg ρ j
  · exact le_rfl

/-- Fully automatic ordered spectral-tail cone inequality. -/
theorem density_orderedSpectralTail_cone
    (σ ρ : DensityOperator ι) (s : ℕ) :
    hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) ≤
      2 * orderedSpectralTail ρ s +
        4 * Real.sqrt s *
          hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
            (σ.sub_isHermitian ρ) := by
  let P := leadingSpectralProjection ρ s
  have hcone := density_projection_cone σ ρ P s
    (leadingSpectralProjection_isHermitian ρ s)
    (leadingSpectralProjection_isIdempotent ρ s)
    (leadingSpectralProjection_operatorNorm_le_one ρ s)
    (leadingSpectralProjection_rank_le ρ s)
  have htail := leadingSpectralProjection_complement_trace_eq_tail ρ s
  dsimp [P] at hcone
  rw [htail] at hcone
  exact hcone

/-- Ordered spectral-tail curvature reduction with the entire deterministic
matrix argument discharged. -/
theorem density_orderedSpectralTail_reduction_of_matrix_bounds
    (σ ρ : DensityOperator ι) (s : ℕ)
    (a h energy : ℝ)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hlower :
      a * hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
          (σ.sub_isHermitian ρ) ^ 2 ≤ energy)
    (hupper :
      energy ≤ hermitianTraceNorm (σ.matrix - ρ.matrix)
          (σ.sub_isHermitian ρ) * h) :
    hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) ≤
      2 * orderedSpectralTail ρ s +
        4 * Real.sqrt ((s : ℝ) * h / a) *
          Real.sqrt (hermitianTraceNorm (σ.matrix - ρ.matrix)
            (σ.sub_isHermitian ρ)) := by
  exact density_hermitianTrace_reduction_of_matrix_bounds σ ρ s a
    (orderedSpectralTail ρ s) h energy ha hh
    (density_orderedSpectralTail_cone σ ρ s) hlower hupper

end TomographyOracleCore.MatrixReduction
