import TomographyOracleCore.HaarBornScoreMoments
import TomographyOracleCore.PhysicalHaarProductLaw
import TomographyOracleCore.ForwardGeometry
import TomographyOracleCore.DensityGrid
import TomographyOracleCore.ChannelPrediction

namespace TomographyOracleCore
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM
open scoped ComplexOrder InnerProductSpace
noncomputable section

/-! Rank-one directional projectors and their calibrated scalar scores. -/

/-- The (possibly unnormalised) rank-one matrix `|u><u|`.  Normalisation is
only used when a unit direction is required. -/
noncomputable def haarDirectionProjector {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) : Matrix (Fin D) (Fin D) ℂ :=
  Matrix.vecMulVec (fun i ↦ u i) (star fun i ↦ u i)

theorem haarDirectionProjector_posSemidef {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) :
    (haarDirectionProjector u).PosSemidef := by
  exact Matrix.posSemidef_vecMulVec_self_star _

theorem haarDirectionProjector_isHermitian {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) :
    (haarDirectionProjector u).IsHermitian :=
  (haarDirectionProjector_posSemidef u).isHermitian

theorem haarDirectionProjector_trace_eq_one {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    (haarDirectionProjector u).trace = 1 := by
  let x : Metric.sphere (0 : EuclideanSpace ℂ (Fin D)) 1 :=
    ⟨u, by simpa [Metric.mem_sphere, dist_zero_right] using hu⟩
  simpa [haarDirectionProjector, complexSphereProjector, x] using
    complexSphereProjector_trace_eq_one x

theorem haarDirectionProjector_mul_self {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    haarDirectionProjector u * haarDirectionProjector u =
      haarDirectionProjector u := by
  have hinner : ⟪u, u⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hu]
    norm_num
  have hdot :
      (star fun i : Fin D ↦ u i) ⬝ᵥ (fun i : Fin D ↦ u i) = 1 := by
    rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
    simpa [dotProduct_comm] using hinner
  rw [haarDirectionProjector, Matrix.vecMulVec_mul_vecMulVec, hdot]
  simp

/-- The matrix trace pairing with `|u><u|` is the usual quadratic form. -/
theorem trace_mul_haarDirectionProjector_re {D : ℕ}
    (A : Matrix (Fin D) (Fin D) ℂ)
    (u : EuclideanSpace ℂ (Fin D)) :
    (A * haarDirectionProjector u).trace.re =
      hermitianQuadraticValue A u := by
  simp only [haarDirectionProjector, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, hermitianQuadraticValue,
    EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin]
  rfl

/-- The one-shot calibrated Haar score in direction `u`. -/
noncomputable def haarDirectionScore {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D))
    (B : Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  haarCalibratedRankOneScore (haarDirectionProjector u) B

theorem measurable_haarDirectionScore {D : ℕ}
    (u : EuclideanSpace ℂ (Fin D)) :
    Measurable (haarDirectionScore u) := by
  unfold haarDirectionScore haarCalibratedRankOneScore
  fun_prop

theorem memLp_haarDirectionScore_two_of_norm_one {D : ℕ}
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    MemLp (haarDirectionScore u) 2
      ((projectiveHaarPOVM D hD).bornMeasure rho) := by
  exact memLp_projectiveHaarPOVM_born_calibratedScore_two
    hD rho (haarDirectionProjector u) (haarDirectionProjector_isHermitian u)

theorem integral_haarDirectionScore_eq_prediction_of_norm_one {D : ℕ}
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    (∫ B, haarDirectionScore u B
        ∂(projectiveHaarPOVM D hD).bornMeasure rho) =
      channelQuadraticPrediction haarCalibratedDensityChannel rho u := by
  change
    (∫ B, haarCalibratedRankOneScore (haarDirectionProjector u) B
        ∂(projectiveHaarPOVM D hD).bornMeasure rho) = _
  rw [integral_projectiveHaarPOVM_born_calibratedScore hD rho
    (haarDirectionProjector u) (haarDirectionProjector_isHermitian u)
    (haarDirectionProjector_trace_eq_one u hu)]
  simp [channelQuadraticPrediction,
    trace_mul_haarDirectionProjector_re]

theorem variance_haarDirectionScore_le_two_of_norm_one {D : ℕ}
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    variance (haarDirectionScore u)
        ((projectiveHaarPOVM D hD).bornMeasure rho) ≤ 2 := by
  exact variance_projectiveHaarPOVM_born_calibratedScore_le_two
    hD rho (haarDirectionProjector u) (haarDirectionProjector_isHermitian u)
    (haarDirectionProjector_trace_eq_one u hu)
    (haarDirectionProjector_mul_self u hu)

end
end TomographyOracleCore
