import TomographyOracleCore.HardDiagonalState
import TomographyOracleCore.GrassmannStatement
import TomographyOracleCore.TraceNormBridge

namespace TomographyOracleCore

open MatrixReduction
open scoped ComplexOrder

/-!
# Projector-rotated hard density states

The two head eigenvalues live on `Fin 2`; a rank-`m` orthogonal projector on
`Fin k` carries total tail mass `b`.  A final reindex identifies the block
space `Fin 2 ⊕ Fin k` with the manuscript space `Fin (k + 2)`.
-/

/-- Canonical identification of the head/tail block index with `Fin (k+2)`. -/
noncomputable def hardProjectorBlockEquiv (k : ℕ) :
    Fin 2 ⊕ Fin k ≃ Fin (k + 2) :=
  finSumFinEquiv.trans (Equiv.cast (congrArg Fin (Nat.add_comm 2 k)))

/-- The two equal head eigenvalues. -/
noncomputable def hardProjectorHeadBlock (b : ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal fun _ ↦ (hardSpectrumHead b : ℂ)

/-- The projector-supported tail block, with total intended mass `b`. -/
noncomputable def hardProjectorTailBlock {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    Matrix (Fin k) (Fin k) ℂ :=
  (b / (m : ℝ)) • P.matrix

/-- The unreindexed head/tail block matrix. -/
noncomputable def hardProjectorBlockMatrix {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    Matrix (Fin 2 ⊕ Fin k) (Fin 2 ⊕ Fin k) ℂ :=
  Matrix.fromBlocks (hardProjectorHeadBlock b) 0 0
    (hardProjectorTailBlock P b)

/-- The hard-state matrix on the manuscript ambient dimension `k+2`. -/
noncomputable def hardProjectorMatrix {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
    (hardProjectorBlockMatrix P b)

/-- An orthogonal projector is positive semidefinite, proved from
`P = Pᴴ P`. -/
theorem rankMOrthogonalProjector_posSemidef {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) : P.matrix.PosSemidef := by
  have hfactor : P.matrix = P.matrix.conjTranspose * P.matrix := by
    calc
      P.matrix = P.matrix * P.matrix := P.isIdempotent.symm
      _ = P.matrix.conjTranspose * P.matrix := by rw [P.isHermitian.eq]
  rw [hfactor]
  exact Matrix.posSemidef_conjTranspose_mul_self P.matrix

/-- Every eigenvalue of an orthogonal projector is exactly zero or one. -/
theorem rankMOrthogonalProjector_eigenvalue_zero_or_one {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (i : Fin k) :
    P.isHermitian.eigenvalues i = 0 ∨
      P.isHermitian.eigenvalues i = 1 := by
  have hi := P.isIdempotent.spectrum_subset ℝ
    (P.isHermitian.eigenvalues_mem_spectrum_real i)
  simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hi

/-- The trace of a rank-`m` orthogonal projector is `m`. -/
theorem rankMOrthogonalProjector_trace_eq_rank {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    P.matrix.trace = (m : ℂ) := by
  rw [P.isHermitian.trace_eq_sum_eigenvalues]
  have hsum :
      (∑ i : Fin k, P.isHermitian.eigenvalues i) = (m : ℝ) := by
    calc
      (∑ i : Fin k, P.isHermitian.eigenvalues i) =
          ∑ i : Fin k,
            if P.isHermitian.eigenvalues i ≠ 0 then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        rcases rankMOrthogonalProjector_eigenvalue_zero_or_one P i with hzero | hone
        · simp [hzero]
        · simp [hone]
      _ = ((Finset.univ.filter fun i : Fin k ↦
          P.isHermitian.eigenvalues i ≠ 0).card : ℝ) := by
        simpa using (Finset.sum_boole (R := ℝ)
          (fun i : Fin k ↦ P.isHermitian.eigenvalues i ≠ 0)
          Finset.univ)
      _ = (Fintype.card
          {i : Fin k // P.isHermitian.eigenvalues i ≠ 0} : ℝ) := by
        norm_cast
        exact (Fintype.card_subtype
          (fun i : Fin k ↦ P.isHermitian.eigenvalues i ≠ 0)).symm
      _ = (P.matrix.rank : ℝ) := by
        rw [P.isHermitian.rank_eq_card_non_zero_eigs]
      _ = (m : ℝ) := by rw [P.rank_eq]
  calc
    (∑ i : Fin k, (P.isHermitian.eigenvalues i : ℂ)) =
        Complex.ofReal (∑ i : Fin k, P.isHermitian.eigenvalues i) :=
      (Complex.ofReal_sum (Finset.univ : Finset (Fin k))
        P.isHermitian.eigenvalues).symm
    _ = (m : ℂ) := by
      simpa using congrArg Complex.ofReal hsum

theorem hardProjectorHeadBlock_posSemidef
    (b : ℝ) (hbquarter : b ≤ 1 / 4) :
    (hardProjectorHeadBlock b).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  show ∀ i, (0 : ℂ) ≤ (hardSpectrumHead b : ℂ)
  intro i
  rw [Complex.nonneg_iff]
  constructor
  · simpa using hardSpectrumHead_nonnegative b (by linarith)
  · simp

theorem hardProjectorTailBlock_posSemidef {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) :
    (hardProjectorTailBlock P b).PosSemidef := by
  apply (rankMOrthogonalProjector_posSemidef P).smul
  exact div_nonneg hb0 (Nat.cast_nonneg m)

theorem hardProjectorBlockMatrix_isHermitian {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    (hardProjectorBlockMatrix P b).IsHermitian := by
  apply Matrix.IsHermitian.fromBlocks
  · apply Matrix.isHermitian_diagonal_iff.mpr
    intro i
    exact isSelfAdjoint_iff.mpr (by simp)
  · simp
  · unfold hardProjectorTailBlock
    exact P.isHermitian.smul (isSelfAdjoint_iff.mpr (by simp))

theorem hardProjectorBlockMatrix_posSemidef {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (hardProjectorBlockMatrix P b).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hardProjectorBlockMatrix_isHermitian P b)
  intro x
  have hstar : star x = Sum.elim (star (x ∘ Sum.inl))
      (star (x ∘ Sum.inr)) := by
    funext i
    cases i <;> simp
  rw [hardProjectorBlockMatrix, Matrix.fromBlocks_mulVec, hstar,
    sumElim_dotProduct_sumElim]
  simp only [Matrix.zero_mulVec, Pi.zero_apply, add_zero, zero_add]
  exact add_nonneg
    ((hardProjectorHeadBlock_posSemidef b hbquarter).dotProduct_mulVec_nonneg
      (x ∘ Sum.inl))
    ((hardProjectorTailBlock_posSemidef P b hm hb0).dotProduct_mulVec_nonneg
      (x ∘ Sum.inr))

/-- Positive semidefiniteness survives the canonical block reindexing. -/
theorem hardProjectorMatrix_posSemidef {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (hardProjectorMatrix P b).PosSemidef := by
  rw [hardProjectorMatrix, Matrix.reindex_apply]
  exact (hardProjectorBlockMatrix_posSemidef P b hm hb0 hbquarter).submatrix
    (hardProjectorBlockEquiv k).symm

/-- Reindexing both axes by an equivalence preserves matrix trace. -/
theorem matrix_trace_reindex_self
    {n n' : Type*} [Fintype n] [Fintype n']
    (e : n ≃ n') (A : Matrix n n ℂ) :
    (Matrix.reindex e e A).trace = A.trace := by
  unfold Matrix.trace
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i ↦ A i i)

/-- The unreindexed hard block has trace one. -/
theorem hardProjectorBlockMatrix_trace_eq_one {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) (hm : 1 ≤ m) :
    (hardProjectorBlockMatrix P b).trace = 1 := by
  unfold Matrix.trace hardProjectorBlockMatrix
  rw [Fintype.sum_sum_type]
  change (∑ i : Fin 2, (hardProjectorHeadBlock b) i i) +
      ∑ i : Fin k, (hardProjectorTailBlock P b) i i = 1
  change (hardProjectorHeadBlock b).trace +
      (hardProjectorTailBlock P b).trace = 1
  rw [hardProjectorHeadBlock, Matrix.trace_diagonal]
  simp only [Fin.sum_univ_two]
  rw [hardProjectorTailBlock, Matrix.trace_smul,
    rankMOrthogonalProjector_trace_eq_rank P]
  have hmne : (m : ℝ) ≠ 0 := by
    positivity
  push_cast
  unfold hardSpectrumHead
  simp only [Algebra.smul_def]
  apply Complex.ext <;> simp [hmne]

theorem hardProjectorMatrix_trace_eq_one {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) (hm : 1 ≤ m) :
    (hardProjectorMatrix P b).trace = 1 := by
  rw [hardProjectorMatrix, matrix_trace_reindex_self,
    hardProjectorBlockMatrix_trace_eq_one P b hm]

/-- The projector hard family bundled as genuine density operators. -/
noncomputable def hardProjectorDensityOperator {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    DensityOperator (Fin (k + 2)) where
  matrix := hardProjectorMatrix P b
  posSemidef := hardProjectorMatrix_posSemidef P b hm hb0 hbquarter
  trace_eq_one := hardProjectorMatrix_trace_eq_one P b hm

/-! ## Exact Hermitian trace-norm transport -/

/-- A characteristic-root formula for the Hermitian trace norm.  Unlike an
ordered eigenvalue formula, this is immediately invariant under reindexing
and adjoining zero blocks. -/
theorem hermitianTraceNorm_eq_roots_abs_sum
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm A hA =
      ((A.charpoly.roots.map RCLike.re).map abs).sum := by
  unfold hermitianTraceNorm
  rw [hA.roots_charpoly_eq_eigenvalues]
  simp only [Multiset.map_map, Function.comp_apply, RCLike.ofReal_re]
  rfl

/-- Exact Hermitian trace-norm invariance under simultaneous reindexing. -/
theorem hermitianTraceNorm_reindex
    {n n' : Type*} [Fintype n] [Fintype n'] [DecidableEq n]
    [DecidableEq n'] (e : n ≃ n') (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm (Matrix.reindex e e A) (hA.reindex e) =
      hermitianTraceNorm A hA := by
  rw [hermitianTraceNorm_eq_roots_abs_sum,
    hermitianTraceNorm_eq_roots_abs_sum, Matrix.charpoly_reindex]

/-- Adjoining a two-dimensional zero block leaves the Hermitian trace norm
unchanged. -/
theorem hermitianTraceNorm_zeroHeadBlock
    {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    let B : Matrix (Fin 2 ⊕ n) (Fin 2 ⊕ n) ℂ :=
      Matrix.fromBlocks 0 0 0 A
    hermitianTraceNorm B
        (Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) hA) =
      hermitianTraceNorm A hA := by
  dsimp
  rw [hermitianTraceNorm_eq_roots_abs_sum,
    hermitianTraceNorm_eq_roots_abs_sum,
    Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_zero]
  simp only [Fintype.card_fin]
  rw [Polynomial.roots_mul (mul_ne_zero
    (pow_ne_zero 2 Polynomial.X_ne_zero) A.charpoly_monic.ne_zero)]
  simp [two_nsmul]

/-- Explicit spectral decomposition after multiplication by a real scalar. -/
theorem real_smul_spectral
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (c : ℂ) • A =
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ fun i ↦ c * hA.eigenvalues i)) := by
  conv_lhs => rw [hA.spectral_theorem]
  let e := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  change (c : ℂ) • e (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) = _
  rw [← map_smul e]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Function.comp_apply]
  · simp [Matrix.diagonal, hij]

theorem real_smul_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    ((c : ℂ) • A).charpoly =
      ∏ i, (Polynomial.X -
        Polynomial.C ((c * hA.eigenvalues i : ℝ) : ℂ)) := by
  rw [real_smul_spectral c A hA]
  change ((hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (RCLike.ofReal ∘ fun i ↦ c * hA.eigenvalues i) *
      star (hA.eigenvectorUnitary : Matrix n n ℂ)).charpoly = _
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc]
  simp [Matrix.charpoly_diagonal, Function.comp_apply]

theorem real_smul_roots_re
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    (((c : ℂ) • A).charpoly.roots.map RCLike.re) =
      Multiset.map (fun i ↦ c * hA.eigenvalues i) Finset.univ.val := by
  rw [real_smul_charpoly c A hA, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.map_bind,
      Multiset.map_singleton]
    rw [Multiset.bind_singleton]
    simp
  · simp only [Finset.prod_ne_zero_iff]
    intro i hi
    exact Polynomial.X_sub_C_ne_zero
      ((c * hA.eigenvalues i : ℝ) : ℂ)

/-- Exact absolute homogeneity of the Hermitian trace norm. -/
theorem hermitianTraceNorm_real_smul
    {n : Type*} [Fintype n] [DecidableEq n]
    (c : ℝ) (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm ((c : ℂ) • A)
        (hA.smul (isSelfAdjoint_iff.mpr (by simp))) =
      |c| * hermitianTraceNorm A hA := by
  rw [hermitianTraceNorm_eq_roots_abs_sum, real_smul_roots_re]
  unfold hermitianTraceNorm
  simp only [Multiset.map_map, Function.comp_apply, abs_mul]
  change (∑ i, |c| * |hA.eigenvalues i|) =
    |c| * ∑ i, |hA.eigenvalues i|
  rw [Finset.mul_sum]

/-! ## Exact Grassmann-distance scaling -/

theorem hardProjectorBlockMatrix_sub {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    hardProjectorBlockMatrix P b - hardProjectorBlockMatrix Q b =
      Matrix.fromBlocks 0 0 0
        (((b / (m : ℝ) : ℝ) : ℂ) • (P.matrix - Q.matrix)) := by
  ext i j
  cases i <;> cases j <;>
    simp [hardProjectorBlockMatrix, hardProjectorTailBlock] <;> ring

theorem hardProjectorMatrix_sub {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    hardProjectorMatrix P b - hardProjectorMatrix Q b =
      Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
        (Matrix.fromBlocks 0 0 0
          (((b / (m : ℝ) : ℝ) : ℂ) • (P.matrix - Q.matrix))) := by
  ext i j
  simp only [hardProjectorMatrix, Matrix.sub_apply, Matrix.reindex_apply]
  have hblock := congrArg (fun M ↦
      M ((hardProjectorBlockEquiv k).symm i)
        ((hardProjectorBlockEquiv k).symm j))
    (hardProjectorBlockMatrix_sub P Q b)
  simpa only [Matrix.sub_apply, Matrix.submatrix_apply] using hblock

/-- Exact trace-distance scaling from the Grassmann projector metric to the
physical hard density states. -/
theorem hardProjectorDensityOperator_traceDistance_eq {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    let rhoP := hardProjectorDensityOperator P b hm hb0 hbquarter
    let rhoQ := hardProjectorDensityOperator Q b hm hb0 hbquarter
    hermitianTraceNorm (rhoP.matrix - rhoQ.matrix)
        (rhoP.sub_isHermitian rhoQ) =
      (b / (m : ℝ)) * projectorHermitianTraceDistance P Q := by
  dsimp
  let A : Matrix (Fin k) (Fin k) ℂ := P.matrix - Q.matrix
  let hA : A.IsHermitian := P.isHermitian.sub Q.isHermitian
  let c : ℝ := b / (m : ℝ)
  let C : Matrix (Fin k) (Fin k) ℂ := (c : ℂ) • A
  let hC : C.IsHermitian := hA.smul (isSelfAdjoint_iff.mpr (by simp))
  let B : Matrix (Fin 2 ⊕ Fin k) (Fin 2 ⊕ Fin k) ℂ :=
    Matrix.fromBlocks 0 0 0 C
  let hB : B.IsHermitian :=
    Matrix.IsHermitian.fromBlocks Matrix.isHermitian_zero (by simp) hC
  have hdiff :
      hardProjectorMatrix P b - hardProjectorMatrix Q b =
        Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k) B := by
    change hardProjectorMatrix P b - hardProjectorMatrix Q b =
      Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
        (Matrix.fromBlocks 0 0 0
          (((b / (m : ℝ) : ℝ) : ℂ) • (P.matrix - Q.matrix)))
    exact hardProjectorMatrix_sub P Q b
  calc
    hermitianTraceNorm
        ((hardProjectorDensityOperator P b hm hb0 hbquarter).matrix -
          (hardProjectorDensityOperator Q b hm hb0 hbquarter).matrix)
        ((hardProjectorDensityOperator P b hm hb0 hbquarter).sub_isHermitian
          (hardProjectorDensityOperator Q b hm hb0 hbquarter)) =
      hermitianTraceNorm
        (Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k) B)
        (hB.reindex (hardProjectorBlockEquiv k)) := by
          apply hermitianTraceNorm_congr
          simpa [hardProjectorDensityOperator] using hdiff
    _ = hermitianTraceNorm B hB :=
      hermitianTraceNorm_reindex (hardProjectorBlockEquiv k) B hB
    _ = hermitianTraceNorm C hC := by
      exact hermitianTraceNorm_zeroHeadBlock C hC
    _ = |c| * hermitianTraceNorm A hA := by
      exact hermitianTraceNorm_real_smul c A hA
    _ = (b / (m : ℝ)) * projectorHermitianTraceDistance P Q := by
      have hc0 : 0 ≤ c := div_nonneg hb0 (Nat.cast_nonneg m)
      rw [abs_of_nonneg hc0]
      rfl

/-- A Grassmann separation of `m/2` becomes a physical state separation of
exactly at least `b/2`. -/
theorem hardProjectorDensityOperator_traceDistance_ge_half_mass {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hsep : (m : ℝ) / 2 ≤ projectorHermitianTraceDistance P Q) :
    b / 2 ≤
      hermitianTraceNorm
        ((hardProjectorDensityOperator P b hm hb0 hbquarter).matrix -
          (hardProjectorDensityOperator Q b hm hb0 hbquarter).matrix)
        ((hardProjectorDensityOperator P b hm hb0 hbquarter).sub_isHermitian
          (hardProjectorDensityOperator Q b hm hb0 hbquarter)) := by
  rw [hardProjectorDensityOperator_traceDistance_eq]
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast hm
  calc
    b / 2 = (b / (m : ℝ)) * ((m : ℝ) / 2) := by
      field_simp [hmpos.ne']
    _ ≤ (b / (m : ℝ)) * projectorHermitianTraceDistance P Q :=
      mul_le_mul_of_nonneg_left hsep (div_nonneg hb0 hmpos.le)

/-! ## Exact spectrum and spectral-decay membership -/

/-- The eigenvalue multiset of a rank-`m` orthogonal projector consists of
exactly `m` ones and `k-m` zeros. -/
theorem rankMOrthogonalProjector_eigenvalue_multiset {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    Multiset.map P.isHermitian.eigenvalues Finset.univ.val =
      Multiset.replicate m 1 + Multiset.replicate (k - m) 0 := by
  let M : Multiset ℝ :=
    Multiset.map P.isHermitian.eigenvalues Finset.univ.val
  let M1 := M.filter (fun x ↦ x ≠ 0)
  let M0 := M.filter (fun x ↦ ¬ x ≠ 0)
  have hcard1 : M1.card = m := by
    change (Multiset.filter (fun x : ℝ ↦ x ≠ 0)
      (Multiset.map P.isHermitian.eigenvalues Finset.univ.val)).card = m
    rw [Multiset.filter_map, Multiset.card_map]
    change (Finset.univ.filter (fun i : Fin k ↦
      P.isHermitian.eigenvalues i ≠ 0)).card = m
    calc
      _ = Fintype.card {i : Fin k // P.isHermitian.eigenvalues i ≠ 0} :=
        (Fintype.card_subtype _).symm
      _ = P.matrix.rank := P.isHermitian.rank_eq_card_non_zero_eigs.symm
      _ = m := P.rank_eq
  have hall1 : ∀ x ∈ M1, x = 1 := by
    intro x hx
    have hxM := (Multiset.mem_filter.mp hx).1
    have hxne := (Multiset.mem_filter.mp hx).2
    rcases Multiset.mem_map.mp hxM with ⟨i, hi, rfl⟩
    rcases rankMOrthogonalProjector_eigenvalue_zero_or_one P i with hz | ho
    · exact False.elim (hxne hz)
    · exact ho
  have hM1 : M1 = Multiset.replicate m 1 :=
    Multiset.eq_replicate.mpr ⟨hcard1, hall1⟩
  have hcardM : M.card = k := by
    simp [M]
  have hcard0 : M0.card = k - m := by
    have hadd := congrArg Multiset.card
      (Multiset.filter_add_not (p := fun x : ℝ ↦ x ≠ 0) M)
    simp only [Multiset.card_add] at hadd
    change M1.card + M0.card = M.card at hadd
    rw [hcard1, hcardM] at hadd
    omega
  have hall0 : ∀ x ∈ M0, x = 0 := by
    intro x hx
    exact not_ne_iff.mp (Multiset.mem_filter.mp hx).2
  have hM0 : M0 = Multiset.replicate (k - m) 0 :=
    Multiset.eq_replicate.mpr ⟨hcard0, hall0⟩
  change M = _
  rw [← hM1, ← hM0]
  exact (Multiset.filter_add_not (p := fun x : ℝ ↦ x ≠ 0) M).symm

/-- Scaling a rank-`m` projector produces `m` copies of the scale and only
zero eigenvalues off its range. -/
theorem rankMOrthogonalProjector_real_smul_roots_re {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (c : ℝ) :
    ((c • P.matrix).charpoly.roots.map RCLike.re) =
      Multiset.replicate m c + Multiset.replicate (k - m) 0 := by
  have hsmul : c • P.matrix = (c : ℂ) • P.matrix := by
    ext i j
    simp [Algebra.smul_def]
  rw [hsmul]
  rw [real_smul_roots_re c P.matrix P.isHermitian,
    show (fun i ↦ c * P.isHermitian.eigenvalues i) =
      (fun x : ℝ ↦ c * x) ∘ P.isHermitian.eigenvalues from rfl,
    ← Multiset.map_map, rankMOrthogonalProjector_eigenvalue_multiset P]
  simp

/-- The two-dimensional head block has its intended repeated eigenvalue. -/
theorem hardProjectorHeadBlock_roots_re_eq_spectrum (b : ℝ) :
    (hardProjectorHeadBlock b).charpoly.roots.map RCLike.re =
      Multiset.replicate 2 (hardSpectrumHead b) := by
  rw [hardProjectorHeadBlock, Matrix.charpoly_diagonal, Fin.prod_univ_two]
  change ((Polynomial.X - Polynomial.C (hardSpectrumHead b : ℂ)) *
      (Polynomial.X - Polynomial.C (hardSpectrumHead b : ℂ))).roots.map
        RCLike.re = _
  rw [← pow_two, Polynomial.roots_pow, Polynomial.roots_X_sub_C]
  simp [two_nsmul]

/-- The exact ordered spectrum expected for a rank-`m` hard projector state:
the scalar hard spectrum followed by the `k-m` null directions. -/
noncomputable def hardProjectorSpectrumList (k m : ℕ) (b : ℝ) : List ℝ :=
  hardSpectrumList m b ++ List.replicate (k - m) 0

/-- The characteristic roots of the full hard matrix are exactly its intended
spectrum, including every zero direction and every multiplicity. -/
theorem hardProjectorMatrix_roots_re_eq_spectrum {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ) :
    (hardProjectorMatrix P b).charpoly.roots.map RCLike.re =
      (hardProjectorSpectrumList k m b : Multiset ℝ) := by
  rw [hardProjectorMatrix, Matrix.charpoly_reindex,
    hardProjectorBlockMatrix, Matrix.charpoly_fromBlocks_zero₁₂,
    Polynomial.roots_mul]
  · simp only [Multiset.map_add,
      hardProjectorHeadBlock_roots_re_eq_spectrum,
      hardProjectorTailBlock]
    rw [rankMOrthogonalProjector_real_smul_roots_re]
    unfold hardProjectorSpectrumList hardSpectrumList hardSpectrumTailEntry
    rfl
  · exact mul_ne_zero (hardProjectorHeadBlock b).charpoly_monic.ne_zero
      (hardProjectorTailBlock P b).charpoly_monic.ne_zero

theorem hardProjectorSpectrumList_sortedGE
    (k m : ℕ) (b : ℝ) (hm : 1 ≤ m) (hb0 : 0 ≤ b)
    (hbquarter : b ≤ 1 / 4) :
    (hardProjectorSpectrumList k m b).SortedGE := by
  rw [List.sortedGE_iff_pairwise]
  unfold hardProjectorSpectrumList
  rw [List.pairwise_append]
  refine ⟨(List.sortedGE_iff_pairwise.mp
      (hardSpectrumList_sortedGE m b hm hbquarter)), ?_, ?_⟩
  · simp
  · intro a ha z hz
    rw [List.eq_of_mem_replicate hz]
    exact hardSpectrumList_nonnegative m b hm hb0 (by linarith) a ha

theorem hardProjectorSpectrumList_length
    (k m : ℕ) (b : ℝ) (hmk : m ≤ k) :
    (hardProjectorSpectrumList k m b).length = k + 2 := by
  unfold hardProjectorSpectrumList
  simp only [List.length_append, hardSpectrumList_length,
    List.length_replicate]
  omega

/-- The antitone ordered eigenvalue list of the projector hard state is
literally the hard spectrum, followed by the ambient null directions. -/
theorem hardProjectorDensityOperator_orderedEigenvalues {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    List.ofFn
        (hardProjectorDensityOperator P b hm hb0 hbquarter).isHermitian.eigenvalues₀ =
      hardProjectorSpectrumList k m b := by
  let hA : (hardProjectorMatrix P b).IsHermitian :=
    (hardProjectorMatrix_posSemidef P b hm hb0 hbquarter).isHermitian
  have hs := Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀ hA
  rw [hardProjectorMatrix_roots_re_eq_spectrum] at hs
  have hp : List.Pairwise (fun x y : ℝ ↦ decide (x ≥ y) = true)
      (hardProjectorSpectrumList k m b) := by
    simpa only [decide_eq_true_eq, ← List.sortedGE_iff_pairwise] using
      hardProjectorSpectrumList_sortedGE k m b hm hb0 hbquarter
  rw [Multiset.coe_sort, List.mergeSort_of_pairwise hp] at hs
  simpa [hA, hardProjectorDensityOperator] using hs.symm

/-- Appending null eigenvalues does not alter any suffix sum of a list. -/
theorem sum_drop_append_replicate_zero
    (l : List ℝ) (r s : ℕ) :
    ((l ++ List.replicate r 0).drop s).sum = (l.drop s).sum := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
      cases s with
      | zero => simp
      | succ s => simpa using ih s

/-- The ordered spectral tail of every projector-rotated hard state is
exactly the same scalar hard-spectrum tail. -/
theorem hardProjectorDensityOperator_orderedSpectralTail {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (s : ℕ) :
    orderedSpectralTail (hardProjectorDensityOperator P b hm hb0 hbquarter) s =
      hardSpectrumTailSum m b s := by
  unfold orderedSpectralTail hardSpectrumTailSum
  rw [← sum_drop_ofFn_eq_sum_ite]
  rw [hardProjectorDensityOperator_orderedEigenvalues P b hm hb0 hbquarter]
  unfold hardProjectorSpectrumList
  exact sum_drop_append_replicate_zero (hardSpectrumList m b) (k - m) s

/-- Exact manuscript tail formula for every projector-rotated hard state. -/
theorem hardProjectorDensityOperator_tail_eq_hardFamilyTail {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hs : 1 ≤ s)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    orderedSpectralTail (hardProjectorDensityOperator P b hm hb0 hbquarter) s =
      hardFamilyTail m b s := by
  rw [hardProjectorDensityOperator_orderedSpectralTail P b hm hb0 hbquarter,
    hardSpectrumTailSum_eq_hardFamilyTail m s b hm hs]

/-- Every projector-rotated hard state belongs to the exact spectral-decay
class under the same scalar hard-mass restriction as the diagonal model. -/
theorem hardProjectorDensityOperator_mem_spectralDecayClass {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    hardProjectorDensityOperator P b hm hb0 hbquarter ∈
      spectralDecayClass (k + 2) alpha L := by
  rw [mem_spectralDecayClass_iff]
  intro s hs hsd
  rw [hardProjectorDensityOperator_tail_eq_hardFamilyTail P b hm hs hb0
    hbquarter]
  exact hardFamilyTail_le_decay_envelope m s alpha L b hm halpha hL
    hb0 hbquarter hbscaled hs

end TomographyOracleCore
