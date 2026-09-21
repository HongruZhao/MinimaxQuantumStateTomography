import TomographyOracleCore.OrderedSpectral
import TomographyOracleCore.Revision.MatrixSolverChannel

namespace TomographyOracleCore.MatrixReduction
open scoped ComplexOrder InnerProductSpace
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
set_option maxHeartbeats 1000000

def negativeSpectralCoeff (A : Matrix ι ι ℂ) (hA : A.IsHermitian) (i : ι) : ℂ :=
  if hA.eigenvalues i < 0 then 1 else 0

def negativeSpectralProjection (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : Matrix ι ι ℂ :=
  Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary (Matrix.diagonal (negativeSpectralCoeff A hA))

def negativeEigenvalueCount (A : Matrix ι ι ℂ) (hA : A.IsHermitian) : ℕ :=
  Fintype.card {i : ι // hA.eigenvalues i < 0}

theorem negativeSpectralProjection_posSemidef (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (negativeSpectralProjection A hA).PosSemidef := by
  have hd : (Matrix.diagonal (negativeSpectralCoeff A hA)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun i => by
      unfold negativeSpectralCoeff
      split_ifs <;> simp
  change ((hA.eigenvectorUnitary : Matrix ι ι ℂ) * _ *
    (hA.eigenvectorUnitary : Matrix ι ι ℂ).conjTranspose).PosSemidef
  exact hd.mul_mul_conjTranspose_same (hA.eigenvectorUnitary : Matrix ι ι ℂ)

theorem negativeSpectralProjection_idempotent (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    IsIdempotentElem (negativeSpectralProjection A hA) := by
  let e := Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
  change e (Matrix.diagonal (negativeSpectralCoeff A hA)) *
    e (Matrix.diagonal (negativeSpectralCoeff A hA)) = _
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_mul_diagonal, negativeSpectralCoeff]
  · simp [Matrix.diagonal_mul_diagonal, hij]

theorem negativeSpectralProjection_trace (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (negativeSpectralProjection A hA).trace = (negativeEigenvalueCount A hA : ℂ) := by
  simp only [negativeSpectralProjection, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp [negativeSpectralCoeff, negativeEigenvalueCount, Fintype.card_subtype]

/-- The trace norm equals trace minus twice the negative spectral trace. -/
theorem traceNorm_eq_trace_sub_twice_negative_trace (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm A hA = A.trace.re - 2 * (negativeSpectralProjection A hA * A).trace.re := by
  have hn : (negativeSpectralProjection A hA * A).trace =
      ∑ i, negativeSpectralCoeff A hA i * (hA.eigenvalues i : ℂ) := by
    rw (occs := .pos [2]) [hA.spectral_theorem]
    change (Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (negativeSpectralCoeff A hA)) *
      Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues))).trace = _
    rw [← map_mul]
    simp only [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal,
      Matrix.diagonal_mul_diagonal, Function.comp_apply]
    rfl
  rw [hn, hA.trace_eq_sum_eigenvalues]
  simp only [Complex.re_sum, Complex.ofReal_re, Finset.mul_sum, ← Finset.sum_sub_distrib,
    hermitianTraceNorm]
  apply Finset.sum_congr rfl
  intro i hi
  unfold negativeSpectralCoeff
  split_ifs with h
  · simp [abs_of_neg h]
    ring
  · simp [abs_of_nonneg (le_of_not_gt h)]

/-- Subtracting a rank-r positive matrix from a PSD matrix creates at most r
negative eigenvalues. The proof compresses to the negative eigenspace. -/
theorem negativeEigenvalueCount_sub_le_rank (S R : Matrix ι ι ℂ)
    (hS : S.PosSemidef) (hR : R.PosSemidef) :
    negativeEigenvalueCount (S - R) (hS.isHermitian.sub hR.isHermitian) ≤ R.rank := by
  let hA := hS.isHermitian.sub hR.isHermitian
  let U := hA.eigenvectorUnitary
  let Sr : Matrix ι ι ℂ := star (U : Matrix ι ι ℂ) * S * U
  let Rr : Matrix ι ι ℂ := star (U : Matrix ι ι ℂ) * R * U
  let N := {i : ι // hA.eigenvalues i < 0}
  have hdiag : Sr - Rr = Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    dsimp [Sr, Rr]
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    conv_lhs => rw [hA.spectral_theorem]
    change star (U : Matrix ι ι ℂ) *
      (U * Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) * star (U : Matrix ι ι ℂ)) * U = _
    calc
      _ = (star (U : Matrix ι ι ℂ) * U) *
          Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) *
          (star (U : Matrix ι ι ℂ) * U) := by noncomm_ring
      _ = _ := by rw [Unitary.coe_star_mul_self]; simp
  have hSr : Sr.PosSemidef := by
    exact hS.conjTranspose_mul_mul_same (U : Matrix ι ι ℂ)
  have hSrN : (Sr.submatrix (fun i : N => i.val) (fun i : N => i.val)).PosSemidef :=
    hSr.submatrix _
  have hneg : (Matrix.diagonal (fun i : N => -(hA.eigenvalues i.val : ℂ))).PosDef := by
    apply Matrix.PosDef.diagonal
    intro i
    exact_mod_cast (neg_pos.mpr i.property)
  have hRr : Rr = Sr - Matrix.diagonal (fun i => (hA.eigenvalues i : ℂ)) := by
    rw [← hdiag]
    abel
  have hRrN : Rr.submatrix (fun i : N => i.val) (fun i : N => i.val) =
      Matrix.diagonal (fun i : N => -(hA.eigenvalues i.val : ℂ)) +
        Sr.submatrix (fun i : N => i.val) (fun i : N => i.val) := by
    rw [hRr]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply, sub_eq_add_neg, add_comm]
    · have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
      simp [Matrix.submatrix_apply, Matrix.diagonal_apply, hij, hij']
  have hPD : (Rr.submatrix (fun i : N => i.val) (fun i : N => i.val)).PosDef := by
    rw [hRrN]
    exact hneg.add_posSemidef hSrN
  have hrank := Matrix.rank_of_isUnit _ hPD.isUnit
  change Fintype.card N ≤ R.rank
  rw [← hrank]
  exact (Matrix.rank_submatrix_le Rr _ _).trans
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))

/-- Frobenius norm of the negative spectral projector is the square root of
its dimension. -/
theorem norm_encode_negativeSpectralProjection_sq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖Revision.MatrixSolver.encode (negativeSpectralProjection A hA)‖ ^ 2 =
      (negativeEigenvalueCount A hA : ℝ) := by
  rw [Revision.MatrixSolver.norm_encode_sq_eq_trace,
    (negativeSpectralProjection_posSemidef A hA).isHermitian.eq,
    negativeSpectralProjection_idempotent A hA, negativeSpectralProjection_trace]
  simp


theorem norm_encode_eq_hermitianFrobeniusNorm (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    ‖Revision.MatrixSolver.encode A‖ = hermitianFrobeniusNorm A hA := by
  apply (sq_eq_sq₀ (norm_nonneg _) (hermitianFrobeniusNorm_nonneg _ _)).mp
  rw [Revision.MatrixSolver.norm_encode_sq_eq_trace, hA.eq,
    trace_sq_eq_hermitianFrobeniusSq A hA, hermitianFrobeniusNorm_sq]
  simp

/-- PSD positivity gives a sqrt(s) cone coefficient, through the negative
eigenspace of the error relative to a rank-s positive approximation. -/
theorem density_cone_of_positive_split (sigma rho : DensityOperator ι)
    (R T : Matrix ι ι ℂ) (s : ℕ) (hR : R.PosSemidef) (hT : T.PosSemidef)
    (hsplit : R + T = rho.matrix) (hrank : R.rank ≤ s) :
    hermitianTraceNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) ≤
      2 * T.trace.re + 2 * Real.sqrt (s : ℝ) *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) := by
  let A := sigma.matrix - R
  have hA : A.IsHermitian := sigma.isHermitian.sub hR.isHermitian
  let P := negativeSpectralProjection A hA
  have hP : P.PosSemidef := negativeSpectralProjection_posSemidef A hA
  have hid : IsIdempotentElem P := negativeSpectralProjection_idempotent A hA
  have hDelta : A - T = sigma.matrix - rho.matrix := by
    dsimp [A]
    rw [← hsplit]
    abel
  have htriangle := hermitianTraceNorm_sub_triangle A T hA hT.isHermitian
  rw [hermitianTraceNorm_congr hDelta (hA.sub hT.isHermitian) (sigma.sub_isHermitian rho),
    hermitianTraceNorm_psd_eq_re_trace T hT] at htriangle
  have hAtr : A.trace.re = T.trace.re := by
    have ht := congrArg (fun X : Matrix ι ι ℂ => X.trace.re) hsplit
    simp only [Matrix.trace_add, Complex.add_re, rho.trace_eq_one, Complex.one_re] at ht
    dsimp [A]
    simp only [Matrix.trace_sub, Complex.sub_re, sigma.trace_eq_one, Complex.one_re]
    linarith
  have hpairT : 0 ≤ (P * T).trace.re := by
    have hp := (hT.mul_mul_conjTranspose_same P).trace_nonneg
    rw [hP.isHermitian.eq, trace_sandwich_of_isIdempotent P T hid] at hp
    exact (Complex.nonneg_iff.mp hp).1
  have hPA : (P * A).trace.re =
      (P * (sigma.matrix - rho.matrix)).trace.re + (P * T).trace.re := by
    have he : A = (sigma.matrix - rho.matrix) + T := by rw [← hDelta]; abel
    rw [he, Matrix.mul_add, Matrix.trace_add, Complex.add_re]
  have hnegativeRank : negativeEigenvalueCount A hA ≤ s :=
    (negativeEigenvalueCount_sub_le_rank sigma.matrix R sigma.posSemidef hR).trans hrank
  have hnormP : ‖Revision.MatrixSolver.encode P‖ ≤ Real.sqrt (s : ℝ) := by
    apply (Real.le_sqrt (norm_nonneg _) (Nat.cast_nonneg s)).mpr
    rw [norm_encode_negativeSpectralProjection_sq]
    exact_mod_cast hnegativeRank
  have hpair : -(P * (sigma.matrix - rho.matrix)).trace.re ≤
      Real.sqrt (s : ℝ) *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) := by
    have hc := abs_real_inner_le_norm (Revision.MatrixSolver.encode P)
      (Revision.MatrixSolver.encode (sigma.matrix - rho.matrix))
    rw [Revision.MatrixSolver.real_inner_encode_eq_trace_of_hermitian _ _ hP.isHermitian,
      Matrix.trace_mul_comm (sigma.matrix - rho.matrix) P,
      norm_encode_eq_hermitianFrobeniusNorm _ (sigma.sub_isHermitian rho)] at hc
    exact (neg_le_abs _).trans (hc.trans
      (mul_le_mul_of_nonneg_right hnormP (hermitianFrobeniusNorm_nonneg _ _)))
  have hnormA := traceNorm_eq_trace_sub_twice_negative_trace A hA
  change hermitianTraceNorm A hA = A.trace.re - 2 * (P * A).trace.re at hnormA
  rw [hAtr, hPA] at hnormA
  nlinarith

/-- The ordered spectral projection splits the state into two PSD blocks. -/
theorem leadingSpectralProjection_split (rho : DensityOperator ι) (s : ℕ) :
    let P := leadingSpectralProjection rho s
    P * rho.matrix * P + (1 - P) * rho.matrix * (1 - P) = rho.matrix := by
  dsimp only
  let e := Unitary.conjStarAlgAut ℂ _ rho.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℂ := Matrix.diagonal (leadingSpectralCoeff s)
  let E : Matrix ι ι ℂ := Matrix.diagonal (fun i => (rho.isHermitian.eigenvalues i : ℂ))
  have hdiag : D * E * D + (1 - D) * E * (1 - D) = E := by
    have hQ : (1 : Matrix ι ι ℂ) - D = Matrix.diagonal (fun i => 1 - leadingSpectralCoeff s i) := by
      ext i j
      by_cases hij : i = j
      · subst j; simp [D]
      · simp [D, hij]
    rw [hQ]
    simp only [D, E, Matrix.diagonal_mul_diagonal]
    rw [Matrix.diagonal_add]
    congr 1
    funext i
    change leadingSpectralCoeff s i * (rho.isHermitian.eigenvalues i : ℂ) * leadingSpectralCoeff s i +
      (1 - leadingSpectralCoeff s i) * (rho.isHermitian.eigenvalues i : ℂ) *
        (1 - leadingSpectralCoeff s i) = _
    unfold leadingSpectralCoeff
    split_ifs <;> simp
  have hrho : rho.matrix = e E := rho.isHermitian.spectral_theorem
  change e D * rho.matrix * e D + (1 - e D) * rho.matrix * (1 - e D) = rho.matrix
  conv_lhs => rw [hrho]
  conv_rhs => rw [hrho]
  simpa only [map_add, map_mul, map_sub, map_one] using congrArg e hdiag

/-- The improved ordered-tail cone uses sqrt(s), with no factor sqrt(2). -/
theorem density_orderedSpectralTail_cone_negative
    (sigma rho : DensityOperator ι) (s : ℕ) :
    hermitianTraceNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) ≤
      2 * orderedSpectralTail rho s + 2 * Real.sqrt (s : ℝ) *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix) (sigma.sub_isHermitian rho) := by
  let P := leadingSpectralProjection rho s
  have hP : P.IsHermitian := leadingSpectralProjection_isHermitian rho s
  have hQ : (1 - P).IsHermitian := Matrix.isHermitian_one.sub hP
  have hR : (P * rho.matrix * P).PosSemidef := by
    simpa only [hP.eq] using rho.posSemidef.mul_mul_conjTranspose_same P
  have hT : ((1 - P) * rho.matrix * (1 - P)).PosSemidef := by
    have ht := rho.posSemidef.mul_mul_conjTranspose_same (1 - P)
    rw [hQ.eq] at ht
    exact ht
  have hrank : (P * rho.matrix * P).rank ≤ s :=
    (Matrix.rank_mul_le_right _ _).trans (leadingSpectralProjection_rank_le rho s)
  have hc := density_cone_of_positive_split sigma rho _ _ s hR hT
    (leadingSpectralProjection_split rho s) hrank
  rw [leadingSpectralProjection_complement_trace_eq_tail rho s] at hc
  exact hc

end
end TomographyOracleCore.MatrixReduction
