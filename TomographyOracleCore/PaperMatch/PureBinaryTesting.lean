import TomographyOracleCore.PaperMatch.PureHypercubeGeometry
import TomographyOracleCore.Revision.MatrixTensorPi
import TomographyOracleCore.Revision.GaussianChangeOfMeasure
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! Binary effects obtained by integrating arbitrary measurable randomized tests.
All analytic bounds below follow from positivity and normalization. -/
namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000

section MatrixIntegral
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

def entryIntegral (μ : Measure Ω) (F : Ω → Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, F x i j ∂μ

theorem entryIntegral_inner (μ : Measure Ω) (F : Ω → Matrix ι ι ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ)
    (u v : EuclideanSpace ℂ ι) :
    ⟪u, (entryIntegral μ F).toEuclideanLin v⟫_ℂ =
      ∫ x, ⟪u, (F x).toEuclideanLin v⟫_ℂ ∂μ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    Matrix.toLin'_apply, dotProduct, Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_finsetSum Finset.univ]
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [entryIntegral, integral_const_mul, integral_mul_const]
    · intro j hj
      exact ((hF i j).mul_const (v j)).mul_const (star (u i))
  · intro i hi
    apply integrable_finsetSum
    intro j hj
    exact ((hF i j).mul_const (v j)).mul_const (star (u i))

theorem entryIntegral_posSemidef (μ : Measure Ω) (F : Ω → Matrix ι ι ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ)
    (hpos : ∀ᵐ x ∂μ, (F x).PosSemidef) : (entryIntegral μ F).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    change star (∫ x, F x j i ∂μ) = ∫ x, F x i j ∂μ
    rw [Complex.star_def, ← integral_conj]
    apply integral_congr_ae
    filter_upwards [hpos] with x hx
    exact congrFun (congrFun hx.isHermitian i) j
  · intro v
    let u : EuclideanSpace ℂ ι := WithLp.toLp 2 v
    have heq : star v ⬝ᵥ (entryIntegral μ F).mulVec v =
        ⟪u, (entryIntegral μ F).toEuclideanLin u⟫_ℂ := by
      simp [u, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct, mul_comm]
    rw [heq]
    rw [entryIntegral_inner μ F hF]
    apply integral_nonneg_of_ae
    filter_upwards [hpos] with x hx
    simpa [u, EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin, Matrix.toLin'_apply, dotProduct, mul_comm] using hx.dotProduct_mulVec_nonneg v

/-- Every effect obtained by a randomized test satisfies 0 ≤ E ≤ I. -/
theorem randomized_binary_effect (μ : Measure Ω) (F : Ω → Matrix ι ι ℂ)
    (hF : ∀ i j, Integrable (fun x => F x i j) μ)
    (hpos : ∀ᵐ x ∂μ, (F x).PosSemidef) (hnorm : entryIntegral μ F = 1)
    (g : Ω → ℝ) (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1) :
    (entryIntegral μ (fun x => g x • F x)).PosSemidef ∧
      (1 - entryIntegral μ (fun x => g x • F x)).PosSemidef := by
  have hint (i j : ι) : Integrable (fun x => (g x : ℂ) * F x i j) μ :=
    (hF i j).bdd_mul (Complex.continuous_ofReal.measurable.comp hg).aestronglyMeasurable
      (ae_of_all _ fun x => by simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hg1 x)
  have hint' (i j : ι) : Integrable (fun x => ((1 - g x : ℝ) : ℂ) * F x i j) μ := by
    convert (hF i j).sub (hint i j) using 1
    ext x
    simp [sub_mul]
  constructor
  · apply entryIntegral_posSemidef μ _ hint
    filter_upwards [hpos] with x hx
    exact hx.smul (hg0 x)
  · have heq : 1 - entryIntegral μ (fun x => g x • F x) =
        entryIntegral μ (fun x => (1 - g x) • F x) := by
      rw [← hnorm]
      ext i j
      simp only [entryIntegral, Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
        Complex.ofReal_sub, Complex.ofReal_one, sub_mul, one_mul]
      exact (integral_sub (hF i j) (hint i j)).symm
    rw [heq]
    apply entryIntegral_posSemidef μ _ hint'
    filter_upwards [hpos] with x hx
    exact hx.smul (sub_nonneg.mpr (hg1 x))

/-- Elementary binary-testing contraction for two unit vectors. -/
theorem binary_effect_difference (E : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (hEc : (1 - E).PosSemidef)
    (u v : EuclideanSpace ℂ ι) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |(⟪u, E.toEuclideanLin u⟫_ℂ).re - (⟪v, E.toEuclideanLin v⟫_ℂ).re| ≤
      2 * ‖u - v‖ := by
  have hop : matrixOperatorNorm E ≤ 1 := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
      exact (CStarAlgebra.norm_le_one_iff_of_nonneg E hE.nonneg).mpr hEc
  have hbound (w : EuclideanSpace ℂ ι) : ‖E.toEuclideanLin w‖ ≤ ‖w‖ := by
    exact (E.toEuclideanLin.toContinuousLinearMap.le_opNorm w).trans
      (by simpa [matrixOperatorNorm] using mul_le_mul_of_nonneg_right hop (norm_nonneg w))
  have hid : ⟪u, E.toEuclideanLin u⟫_ℂ - ⟪v, E.toEuclideanLin v⟫_ℂ =
      ⟪u - v, E.toEuclideanLin u⟫_ℂ + ⟪v, E.toEuclideanLin (u - v)⟫_ℂ := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    ring
  calc
    _ ≤ ‖⟪u, E.toEuclideanLin u⟫_ℂ - ⟪v, E.toEuclideanLin v⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖u - v‖ * ‖E.toEuclideanLin u‖ + ‖v‖ * ‖E.toEuclideanLin (u - v)‖ := by
      rw [hid]
      exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖u - v‖ * 1 + 1 * ‖u - v‖ := by
      rw [hv]
      exact add_le_add (mul_le_mul_of_nonneg_left ((hbound u).trans_eq hu) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hbound _) zero_le_one)
    _ = _ := by ring
end MatrixIntegral

end
end TomographyOracleCore.PaperMatch.RankMinimax
