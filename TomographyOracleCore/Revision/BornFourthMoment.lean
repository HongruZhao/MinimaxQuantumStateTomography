import TomographyOracleCore.Candidate2FiniteBornMomentBridge
import TomographyOracleCore.PhysicalHaarOneCopySpectral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Jensen

/-!
# Elementary fourth-projector to sixth-Born moment calculation

This file proves the finite Born reweighting and convexity steps. The ensemble
is the literal family of measurement unitaries. A fourth-moment bound, when
used below, is an explicit intermediate hypothesis and is not a new axiom.
-/

namespace TomographyOracleCore.Revision.BornFourthMoment

open MeasureTheory MatrixReduction Candidate2FiniteBornVectorLaw
open Candidate2FiniteBornMomentBridge
open scoped BigOperators InnerProductSpace ComplexOrder ENNReal

noncomputable section

variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]

theorem trace_direction_projector_measurement_eq_inner_sq
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D)
    (u : EuclideanSpace ℂ (Fin D)) :
    (haarDirectionProjector u * finiteUnitaryMeasurementProjector U b).trace.re =
      ‖⟪finiteUnitaryMeasurementVector U b, u⟫_ℂ‖ ^ 2 := by
  rw [finiteUnitaryMeasurementProjector_eq_complexSphereProjector]
  simp only [haarDirectionProjector, complexSphereProjector,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec]
  rw [dotProduct_smul]
  simp only [smul_eq_mul]
  rw [dotProduct_comm (star fun i : Fin D => u i)]
  rw [← EuclideanSpace.inner_eq_star_dotProduct u (finiteUnitaryMeasurementVector U b)]
  rw [← EuclideanSpace.inner_eq_star_dotProduct (finiteUnitaryMeasurementVector U b) u]
  rw [← inner_conj_symm (𝕜 := ℂ) (finiteUnitaryMeasurementVector U b) u]
  rw [Complex.mul_conj]
  simp only [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [Complex.norm_conj]

theorem finiteUnitaryBornWeight_spectral
    (rho : DensityOperator (Fin D))
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    finiteUnitaryBornWeight rho U b =
      ∑ i : Fin D, rho.isHermitian.eigenvalues i *
        ‖⟪finiteUnitaryMeasurementVector U b, rho.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 2 := by
  rw [finiteUnitaryBornWeight, Matrix.trace_mul_comm]
  rw [trace_mul_re_eq_sum_eigenvalues_mul_quadratic _ _ rho.isHermitian]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← trace_mul_haarDirectionProjector_re, Matrix.trace_mul_comm]
  exact trace_direction_projector_measurement_eq_inner_sq U b _

theorem finiteUnitaryBornWeight_pow_four_le_spectral
    (rho : DensityOperator (Fin D))
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    finiteUnitaryBornWeight rho U b ^ 4 ≤
      ∑ i : Fin D, rho.isHermitian.eigenvalues i *
        ‖⟪finiteUnitaryMeasurementVector U b, rho.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 8 := by
  rw [finiteUnitaryBornWeight_spectral]
  have hj := (convexOn_pow (𝕜 := ℝ) 4).map_sum_le
    (t := Finset.univ) (w := rho.isHermitian.eigenvalues)
    (p := fun i : Fin D =>
      ‖⟪finiteUnitaryMeasurementVector U b, rho.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 2)
    (fun i _ => rho.posSemidef.eigenvalues_nonneg i)
    rho.sum_eigenvalues_eq_one (fun i _ => by
      change (0 : ℝ) ≤
        ‖⟪finiteUnitaryMeasurementVector U b, rho.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 2
      exact sq_nonneg _)
  simpa only [smul_eq_mul, ← pow_mul] using hj

theorem born_mixed_power_le_fourth_powers (a z : ℝ) (ha : 0 ≤ a) (hz : 0 ≤ z) :
    a * z ^ 3 ≤ (a ^ 4 + 3 * z ^ 4) / 4 := by
  have h := mul_nonneg (sq_nonneg (a - z))
    (show 0 ≤ a ^ 2 + 2 * a * z + 3 * z ^ 2 by positivity)
  nlinarith

/-- Eighth overlap moment under uniform circuit and uniform basis outcome. -/
def finiteUnitaryUniformEighthMoment
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (u : EuclideanSpace ℂ (Fin D)) : ℝ :=
  ((Fintype.card A : ℝ) * (D : ℝ))⁻¹ *
    ∑ e : A, ∑ b : Fin D, ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 8

/-- Fourth power of the Born weight, averaged under the uniform reference law. -/
def finiteUnitaryUniformBornFourthMoment
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) : ℝ :=
  ((Fintype.card A : ℝ) * (D : ℝ))⁻¹ *
    ∑ e : A, ∑ b : Fin D, finiteUnitaryBornWeight rho (U e) b ^ 4

theorem finiteUnitaryUniformBornFourthMoment_le_spectral
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    finiteUnitaryUniformBornFourthMoment U rho ≤
      ∑ i : Fin D, rho.isHermitian.eigenvalues i *
        finiteUnitaryUniformEighthMoment U (rho.isHermitian.eigenvectorBasis i) := by
  let c : ℝ := ((Fintype.card A : ℝ) * (D : ℝ))⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset A))
    (fun e _ => Finset.sum_le_sum (s := (Finset.univ : Finset (Fin D)))
      (fun b _ => finiteUnitaryBornWeight_pow_four_le_spectral rho (U e) b))
  unfold finiteUnitaryUniformBornFourthMoment finiteUnitaryUniformEighthMoment
  change c * _ ≤ ∑ i : Fin D, rho.isHermitian.eigenvalues i * (c * _)
  refine (mul_le_mul_of_nonneg_left hsum hc).trans_eq ?_
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  calc
    _ = ∑ e : A, ∑ i : Fin D, ∑ b : Fin D,
        c * (rho.isHermitian.eigenvalues i *
          ‖⟪finiteUnitaryMeasurementVector (U e) b, rho.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 8) := by
      apply Finset.sum_congr rfl
      intro e _
      exact Finset.sum_comm
    _ = ∑ i : Fin D, ∑ e : A, ∑ b : Fin D,
        c * (rho.isHermitian.eigenvalues i *
          ‖⟪finiteUnitaryMeasurementVector (U e) b, rho.isHermitian.eigenvectorBasis i⟫_ℂ‖ ^ 8) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro b _
      ring

/-- A uniform pure-direction eighth moment controls every mixed-state
fourth Born weight, with the same constant. -/
theorem finiteUnitaryUniformBornFourthMoment_le_of_eighth
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) {R : ℝ}
    (hR : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      finiteUnitaryUniformEighthMoment U u ≤ R) :
    finiteUnitaryUniformBornFourthMoment U rho ≤ R := by
  calc
    _ ≤ ∑ i : Fin D, rho.isHermitian.eigenvalues i *
        finiteUnitaryUniformEighthMoment U (rho.isHermitian.eigenvectorBasis i) :=
      finiteUnitaryUniformBornFourthMoment_le_spectral U rho
    _ ≤ ∑ i : Fin D, rho.isHermitian.eigenvalues i * R := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (hR _ (rho.isHermitian.eigenvectorBasis.orthonormal.norm_eq_one i))
        (rho.posSemidef.eigenvalues_nonneg i)
    _ = R := by rw [← Finset.sum_mul, rho.sum_eigenvalues_eq_one, one_mul]

/-- Exact finite Young-inequality bound for the sixth Born marginal. -/
theorem finiteUnitaryBornUnscaledSixthMarginal_le_fourth
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) :
    finiteUnitaryBornUnscaledSixthMarginal U rho u ≤
      (D : ℝ) * (finiteUnitaryUniformBornFourthMoment U rho +
        3 * finiteUnitaryUniformEighthMoment U u) / 4 := by
  let c : ℝ := ((Fintype.card A : ℝ) * (D : ℝ))⁻¹
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hdim : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hcard : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hnormalization :
      ((Fintype.card A : ℕ) : ℝ≥0∞)⁻¹.toReal = (D : ℝ) * c := by
    dsimp [c]
    simp only [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    field_simp
  have hpoint (e : A) (b : Fin D) :
      finiteUnitaryBornWeight rho (U e) b *
          ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 6 ≤
        (finiteUnitaryBornWeight rho (U e) b ^ 4 +
          3 * ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 8) / 4 := by
    simpa only [← pow_mul] using
      born_mixed_power_le_fourth_powers
        (finiteUnitaryBornWeight rho (U e) b)
        (‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 2)
        (finiteUnitaryBornWeight_nonneg hD rho (U e) b) (sq_nonneg _)
  unfold finiteUnitaryBornUnscaledSixthMarginal
    finiteUnitaryUniformBornFourthMoment finiteUnitaryUniformEighthMoment
  simp only [smul_eq_mul, hnormalization]
  change (D : ℝ) * c * _ ≤ (D : ℝ) * (c * _ + 3 * (c * _)) / 4
  calc
    _ ≤ (D : ℝ) * c * (∑ e : A, ∑ b : Fin D,
        (finiteUnitaryBornWeight rho (U e) b ^ 4 +
          3 * ‖⟪finiteUnitaryMeasurementVector (U e) b, u⟫_ℂ‖ ^ 8) / 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun b _ => hpoint e b
    _ = _ := by
      simp_rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum]
      ring

/-- Fourth-projector control implies sixth Born control for every density
matrix, without assuming a moment property of the Born law itself. -/
theorem finiteUnitaryBornUnscaledSixthMarginal_le_of_eighth
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) {R : ℝ}
    (hR : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      finiteUnitaryUniformEighthMoment U u ≤ R)
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    finiteUnitaryBornUnscaledSixthMarginal U rho u ≤ (D : ℝ) * R := by
  have hfour := finiteUnitaryUniformBornFourthMoment_le_of_eighth U rho hR
  have hu8 := hR u hu
  calc
    _ ≤ (D : ℝ) * (finiteUnitaryUniformBornFourthMoment U rho +
        3 * finiteUnitaryUniformEighthMoment U u) / 4 :=
      finiteUnitaryBornUnscaledSixthMarginal_le_fourth hD U rho u
    _ ≤ (D : ℝ) * (R + 3 * R) / 4 := by gcongr
    _ = (D : ℝ) * R := by ring

/-- The manuscript's constant 34 is preserved under Born reweighting and
the exact `sqrt(D+1)` vector scaling. -/
theorem integral_sixth_le_thirtyFour_of_uniform_eighth
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (hfourth : ∀ u : EuclideanSpace ℂ (Fin D), ‖u‖ = 1 →
      finiteUnitaryUniformEighthMoment U u ≤
        34 / ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2) * ((D : ℝ) + 3)))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1) :
    (∫ x, ‖⟪x, u⟫_ℂ‖ ^ 6 ∂finiteUnitaryBornVectorLaw U rho) ≤ 34 := by
  rw [integral_finiteUnitaryBornVectorLaw_inner_sixth hD]
  have hraw := finiteUnitaryBornUnscaledSixthMarginal_le_of_eighth hD U rho hfourth u hu
  refine (mul_le_mul_of_nonneg_left hraw (by positivity)).trans ?_
  have hdpos : (0 : ℝ) < D := by exact_mod_cast hD
  rw [← mul_assoc, ← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).2
  have hbase : ((D : ℝ) + 1) ^ 2 ≤ ((D : ℝ) + 2) * ((D : ℝ) + 3) := by
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hbase
    (show (0 : ℝ) ≤ 34 * (D : ℝ) * ((D : ℝ) + 1) by positivity)
  nlinarith

end

end TomographyOracleCore.Revision.BornFourthMoment
