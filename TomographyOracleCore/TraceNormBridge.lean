import TomographyOracleCore.MatrixReduction

namespace TomographyOracleCore.MatrixReduction

open scoped ComplexOrder InnerProductSpace

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-!
# Singular-value/Hermitian trace-norm bridge

For a Hermitian complex matrix, the singular values are the square roots of
the eigenvalues of its square.  Comparing characteristic-polynomial roots
shows that their sum is the sum of the absolute Hermitian eigenvalues.
-/

lemma traceNorm_eq_sum_singularValues_fin (A : Matrix ι ι ℂ) :
    traceNorm A = ∑ i : Fin (Fintype.card ι),
      A.toEuclideanLin.singularValues i := by
  rw [traceNorm, Finsupp.sum]
  rw [Fin.sum_univ_eq_sum_range]
  apply Finset.sum_subset
  · intro i hi
    rw [Finset.mem_range]
    by_contra hlt
    have hdim : Module.finrank ℂ (EuclideanSpace ℂ ι) ≤ i := by
      simpa [finrank_euclideanSpace] using Nat.le_of_not_gt hlt
    have hz := A.toEuclideanLin.singularValues_of_finrank_le hdim
    exact (Finsupp.mem_support_iff.mp hi) hz
  · intro i hi hnot
    exact Finsupp.notMem_support_iff.mp hnot

lemma square_isHermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (A * A).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [hA.eq]

lemma square_spectral_theorem (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    A * A = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
      (Matrix.diagonal (fun i => ((hA.eigenvalues i ^ 2 : ℝ) : ℂ))) := by
  rw (occs := .pos [1, 2]) [hA.spectral_theorem]
  rw [← map_mul]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [pow_two]
  · simp [hij]

lemma square_charpoly_eq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (A * A).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((hA.eigenvalues i ^ 2 : ℝ) : ℂ)) := by
  conv_lhs => rw [square_spectral_theorem A hA,
    Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
  simp [Matrix.charpoly_diagonal]

lemma square_roots_charpoly_eq (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (A * A).charpoly.roots =
      Multiset.map (fun i : ι => ((hA.eigenvalues i ^ 2 : ℝ) : ℂ))
        Finset.univ.val := by
  rw [square_charpoly_eq A hA, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton]
  · exact Finset.prod_ne_zero_iff.mpr fun i hi =>
      Polynomial.X_sub_C_ne_zero _

lemma sum_sqrt_square_eigenvalues₀_eq_sum_abs_eigenvalues
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (∑ i : Fin (Fintype.card ι),
      Real.sqrt ((square_isHermitian A hA).eigenvalues₀ i)) =
      ∑ i : ι, |hA.eigenvalues i| := by
  let hB := square_isHermitian A hA
  have hrootsB := hB.roots_charpoly_eq_eigenvalues₀
  have hrootsA := square_roots_charpoly_eq A hA
  have hm :
      Multiset.map (fun z : ℂ => Real.sqrt z.re)
          (Multiset.map (RCLike.ofReal ∘ hB.eigenvalues₀) Finset.univ.val) =
        Multiset.map (fun z : ℂ => Real.sqrt z.re)
          (Multiset.map (fun i : ι => ((hA.eigenvalues i ^ 2 : ℝ) : ℂ))
            Finset.univ.val) := by
    rw [← hrootsB, ← hrootsA]
  have hsum := congrArg Multiset.sum hm
  have hsqrt (x : ℝ) : Real.sqrt (((x : ℂ) ^ 2).re) = |x| := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re, Real.sqrt_sq_eq_abs]
  simpa [Multiset.map_map, Function.comp_def, List.sum_ofFn, hsqrt] using hsum

lemma adjoint_comp_self_toEuclideanLin_eq_square
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin =
      (A * A).toEuclideanLin := by
  calc
    A.toEuclideanLin.adjoint ∘ₗ A.toEuclideanLin =
        A.conjTranspose.toEuclideanLin ∘ₗ A.toEuclideanLin := by
      rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
    _ = (A.conjTranspose * A).toEuclideanLin := by
      exact (Matrix.toLpLin_mul 2 2 2 A.conjTranspose A).symm
    _ = (A * A).toEuclideanLin := by rw [hA.eq]

lemma singularValues_fin_eq_sqrt_square_eigenvalues₀
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian)
    (i : Fin (Fintype.card ι)) :
    A.toEuclideanLin.singularValues i =
      Real.sqrt ((square_isHermitian A hA).eigenvalues₀ i) := by
  let T := A.toEuclideanLin
  let B := A * A
  let hB : B.IsHermitian := square_isHermitian A hA
  let hTB : B.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr hB
  have hmap : T.adjoint ∘ₗ T = B.toEuclideanLin :=
    adjoint_comp_self_toEuclideanLin_eq_square A hA
  have hchar : (T.adjoint ∘ₗ T).charpoly = B.toEuclideanLin.charpoly :=
    congrArg LinearMap.charpoly hmap
  have heig :
      T.isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace =
        hTB.eigenvalues finrank_euclideanSpace := by
    exact (LinearMap.IsSymmetric.eigenvalues_eq_eigenvalues_iff
      T.isSymmetric_adjoint_comp_self finrank_euclideanSpace hTB
        finrank_euclideanSpace).mpr hchar
  rw [T.singularValues_fin finrank_euclideanSpace]
  change Real.sqrt
      (T.isSymmetric_adjoint_comp_self.eigenvalues finrank_euclideanSpace i) =
    Real.sqrt (hTB.eigenvalues finrank_euclideanSpace i)
  rw [heig]

/-- On the Hermitian subspace, the singular-value trace norm equals the sum
of the absolute eigenvalues. -/
theorem traceNorm_eq_hermitianTraceNorm
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    traceNorm A = hermitianTraceNorm A hA := by
  rw [traceNorm_eq_sum_singularValues_fin, hermitianTraceNorm]
  calc
    (∑ i : Fin (Fintype.card ι), A.toEuclideanLin.singularValues i) =
        ∑ i : Fin (Fintype.card ι),
          Real.sqrt ((square_isHermitian A hA).eigenvalues₀ i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact singularValues_fin_eq_sqrt_square_eigenvalues₀ A hA i
    _ = ∑ i : ι, |hA.eigenvalues i| :=
      sum_sqrt_square_eigenvalues₀_eq_sum_abs_eigenvalues A hA

end TomographyOracleCore.MatrixReduction
