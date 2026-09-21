import TomographyOracleCore.DirectionalScores

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM DensityGrid
open scoped ComplexOrder InnerProductSpace ENNReal

noncomputable section

theorem haarDirectionProjector_overlap_bounds {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (x : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    0 <= ((haarDirectionProjector u * complexSphereProjector x).trace).re ∧
      ((haarDirectionProjector u * complexSphereProjector x).trace).re <= 1 := by
  have hx : ‖(x.1 : EuclideanSpace ℂ (Fin D))‖ = 1 := by
    simpa [Metric.mem_sphere, dist_zero_right] using x.2
  have hinner := norm_inner_le_norm (𝕜 := ℂ) u x.1
  rw [hu, hx, one_mul] at hinner
  simp only [haarDirectionProjector, complexSphereProjector,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm (star fun i : Fin D => u i)]
  rw [← EuclideanSpace.inner_eq_star_dotProduct u x.1]
  rw [← EuclideanSpace.inner_eq_star_dotProduct x.1 u]
  rw [← inner_conj_symm (𝕜 := ℂ) x.1 u]
  rw [Complex.mul_conj]
  simp only [Complex.ofReal_re]
  constructor
  · exact Complex.normSq_nonneg _
  · rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg ⟪u, x.1⟫_ℂ,
      sq_nonneg (1 - ‖⟪u, x.1⟫_ℂ‖)]

theorem haarDirectionScore_sphere_abs_le_dimension {D : ℕ} (hD : 1 <= D)
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (x : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    |haarDirectionScore u (complexSphereProjector x)| <= (D : Real) := by
  have hov := haarDirectionProjector_overlap_bounds u hu x
  unfold haarDirectionScore haarCalibratedRankOneScore
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one]
  rw [abs_le]
  constructor <;> nlinarith [show (1 : Real) <= D by exact_mod_cast hD]

theorem haarDirectionScore_born_ae_abs_le_dimension {D : ℕ}
    (hD : 1 <= D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    ∀ᵐ B ∂(projectiveHaarPOVM D (by omega)).bornMeasure rho,
      |haarDirectionScore u B| <= (D : Real) := by
  have hDpos : 0 < D := by omega
  let P : Matrix (Fin D) (Fin D) ℂ -> Prop :=
    fun B => |haarDirectionScore u B| <= (D : Real)
  have hPmeas : MeasurableSet {B | P B} := by
    exact measurableSet_le (measurable_haarDirectionScore u).abs measurable_const
  have hlaw : ∀ᵐ B ∂complexProjectiveHaarLaw (Fin D), P B := by
    unfold complexProjectiveHaarLaw
    rw [ae_map_iff
      (measurable_complexSphereProjector (ι := Fin D)).aemeasurable hPmeas]
    exact Filter.Eventually.of_forall (haarDirectionScore_sphere_abs_le_dimension hD u hu)
  have hbase : ∀ᵐ B ∂projectiveHaarPOVMBase (D := D), P B := by
    unfold projectiveHaarPOVMBase
    exact (Measure.ae_ennreal_smul_measure_iff (c := (D : ℝ≥0∞))
      (by simpa using Nat.ne_of_gt hDpos)).2 hlaw
  have hac :
      (projectiveHaarPOVM D hDpos).bornMeasure rho ≪
        projectiveHaarPOVMBase (D := D) := by
    change bornMeasureFrom (projectiveHaarPOVMBase (D := D))
        (projectiveHaarPOVMEffect (D := D)) rho ≪
      projectiveHaarPOVMBase (D := D)
    unfold bornMeasureFrom
    exact withDensity_absolutelyContinuous _ _
  exact hac.ae_le hbase

end
end TomographyOracleCore
