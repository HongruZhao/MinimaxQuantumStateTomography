import TomographyOracleCore.PaperMatch.PureBinaryTesting

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction
open Revision.MatrixTensorPi
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000

section TensorAlgebra
variable {J ι : Type*} [Fintype J] [DecidableEq J] [Fintype ι] [DecidableEq ι]

def tensorVector (v : J → EuclideanSpace ℂ ι) : EuclideanSpace ℂ (J → ι) :=
  WithLp.toLp 2 (fun x => ∏ j, v j (x j))

@[simp] theorem tensorVector_apply (v : J → EuclideanSpace ℂ ι) (x : J → ι) :
    tensorVector v x = ∏ j, v j (x j) := rfl

theorem inner_tensorVector (u v : J → EuclideanSpace ℂ ι) :
    ⟪tensorVector u, tensorVector v⟫_ℂ = ∏ j, ⟪u j, v j⟫_ℂ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Pi.star_apply,
    tensorVector_apply, star_prod, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j x => v j x * star (u j x))).symm

theorem tensorVector_norm_one (v : J → EuclideanSpace ℂ ι) (hv : ∀ j, ‖v j‖ = 1) :
    ‖tensorVector v‖ = 1 := by
  have h := inner_tensorVector v v
  simp only [inner_self_eq_norm_sq_to_K, hv] at h
  have hr := congrArg (RCLike.re : ℂ → ℝ) h
  change ((‖tensorVector v‖ : ℂ) ^ 2).re = (∏ _j : J, (1 : ℂ) ^ 2).re at hr
  simp [← Complex.ofReal_pow] at hr
  rcases hr with hr | hr
  · exact hr
  · nlinarith [norm_nonneg (tensorVector v)]

theorem tensorPi_posSemidef (F : J → Matrix ι ι ℂ) (hF : ∀ j, (F j).PosSemidef) :
    (tensorPi F).PosSemidef := by
  open scoped MatrixOrder Matrix.Norms.L2Operator in
    choose B hB using fun j => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hF j).nonneg
    have heq : tensorPi F = star (tensorPi B) * tensorPi B := by
      calc
        _ = tensorPi (fun j => star (B j) * B j) := congrArg tensorPi (funext hB)
        _ = _ := by rw [tensorPi_mul]; congr 1; exact tensorPi_conjTranspose B
    rw [heq, Matrix.star_eq_conjTranspose]
    exact Matrix.posSemidef_conjTranspose_mul_self _

theorem tensorPi_inner (F : J → Matrix ι ι ℂ) (u v : J → EuclideanSpace ℂ ι) :
    ⟪tensorVector u, (tensorPi F).toEuclideanLin (tensorVector v)⟫_ℂ =
      ∏ j, ⟪u j, (F j).toEuclideanLin (v j)⟫_ℂ := by
  have hvec : (tensorPi F).toEuclideanLin (tensorVector v) =
      tensorVector (fun j => (F j).toEuclideanLin (v j)) := by
    ext x
    change (∑ y : J → ι, (∏ j, F j (x j) (y j)) * ∏ j, v j (y j)) =
      ∏ j, ∑ y, F j (x j) y * v j y
    simp only [← Finset.prod_mul_distrib]
    exact (Fintype.prod_sum (fun j (y : ι) => F j (x j) y * v j y)).symm
  rw [hvec, inner_tensorVector]
end TensorAlgebra

/-- The neighboring overlap is real and has an exact algebraic expression. -/
theorem cubeVector_neighbor_inner {m : ℕ} (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (θ : SignCube m) (j : Fin m) :
    ⟪cubeVector m a θ, cubeVector m a (cubeFlip j θ)⟫_ℂ = ((1 - 2 * a ^ 2 : ℝ) : ℂ) := by
  have hr := norm_sub_sq (𝕜 := ℂ) (cubeVector m a θ) (cubeVector m a (cubeFlip j θ))
  rw [cubeVector_norm a θ ha, cubeVector_norm a (cubeFlip j θ) ha,
    cubeVector_neighbor_norm_sq] at hr
  apply Complex.ext
  · simp only [Complex.ofReal_re]
    change 4 * a ^ 2 = 1 ^ 2 - 2 * (⟪cubeVector m a θ, cubeVector m a (cubeFlip j θ)⟫_ℂ).re + 1 ^ 2 at hr
    nlinarith
  · simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Complex.im_sum,
      Complex.ofReal_im]
    apply Finset.sum_eq_zero
    intro i hi
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [cubeVector_zero, Complex.star_def]
    · simp [cubeVector_succ, Complex.star_def]

/-- Tensorization of the elementary neighboring-vector distance. -/
theorem cubeTensor_neighbor_distance_sq {m T : ℕ} (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1)
    (θ : SignCube m) (j : Fin m) :
    ‖tensorVector (fun _ : Fin T => cubeVector m a θ) -
        tensorVector (fun _ : Fin T => cubeVector m a (cubeFlip j θ))‖ ^ 2 ≤
      4 * (T : ℝ) * a ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), tensorVector_norm_one _ (fun _ => cubeVector_norm a θ ha),
    tensorVector_norm_one _ (fun _ => cubeVector_norm a (cubeFlip j θ) ha),
    inner_tensorVector]
  simp only [cubeVector_neighbor_inner a ha θ j, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← Complex.ofReal_pow, RCLike.ofReal_re]
  simp only [RCLike.re_to_complex, Complex.ofReal_re]
  have hb := one_add_mul_le_pow (a := -(2 * a ^ 2)) (by nlinarith : -2 ≤ -(2 * a ^ 2)) T
  simp only [neg_mul, mul_neg, ← sub_eq_add_neg] at hb
  nlinarith

/-- Every binary effect has neighboring success-probability gap at most 1/2. -/
theorem cubeTensor_binary_gap {m T : ℕ} (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1)
    (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (θ : SignCube m) (j : Fin m)
    (E : Matrix (Fin T → Fin (m + 1)) (Fin T → Fin (m + 1)) ℂ)
    (hE : E.PosSemidef) (hEc : (1 - E).PosSemidef) :
    |(⟪tensorVector (fun _ : Fin T => cubeVector m a θ),
      E.toEuclideanLin (tensorVector (fun _ : Fin T => cubeVector m a θ))⟫_ℂ).re -
     (⟪tensorVector (fun _ : Fin T => cubeVector m a (cubeFlip j θ)),
      E.toEuclideanLin (tensorVector (fun _ : Fin T => cubeVector m a (cubeFlip j θ)))⟫_ℂ).re| ≤ 1 / 2 := by
  have hd := cubeTensor_neighbor_distance_sq (T := T) a ha ha1 θ j
  have hb := binary_effect_difference E hE hEc
    (tensorVector (fun _ : Fin T => cubeVector m a θ))
    (tensorVector (fun _ : Fin T => cubeVector m a (cubeFlip j θ)))
    (tensorVector_norm_one _ (fun _ => cubeVector_norm a θ ha))
    (tensorVector_norm_one _ (fun _ => cubeVector_norm a (cubeFlip j θ) ha))
  have hn := norm_nonneg (tensorVector (fun _ : Fin T => cubeVector m a θ) -
    tensorVector (fun _ : Fin T => cubeVector m a (cubeFlip j θ)))
  nlinarith

end
end TomographyOracleCore.PaperMatch.RankMinimax
