import TomographyOracleCore.Revision.PhysicalFourthBoundary
import TomographyOracleCore.Revision.FourthTwirlTransport
import TomographyOracleCore.Revision.BornFourthMoment
import TomographyOracleCore.Revision.CliffordFourthBasisInput

namespace TomographyOracleCore.Revision.FourthMeasurementMoment

open FourthVectorBoundary FourthTwirlTensorization CliffordFourthBasisInput
open PhysicalFourthBoundary FourthBoundaryReindex PauliOmegaBlocks
open scoped BigOperators InnerProductSpace Matrix
noncomputable section

variable {α β E : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Fintype E]

def measurementVector (U : Matrix.unitaryGroup α ℂ) (b : α) : EuclideanSpace ℂ α :=
  WithLp.toLp 2 (fun i => star (U.val b i))

theorem measurementVector_inner (U : Matrix.unitaryGroup α ℂ) (b : α)
    (u : EuclideanSpace ℂ α) :
    ⟪measurementVector U b, u⟫_ℂ = U.val.toEuclideanLin u b := by
  simp only [measurementVector, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.toEuclideanLin_apply, Matrix.mulVec, dotProduct, starRingEnd_apply, star_star]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem conjugation_vectorProjector (U : Matrix.unitaryGroup α ℂ)
    (u : EuclideanSpace ℂ α) :
    unitaryMatrixConjugationLinearMap U (vectorProjector u) =
      vectorProjector (U.val.toEuclideanLin u) := by
  rw [unitaryMatrixConjugationLinearMap_apply, vectorProjector,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.star_mulVec]
  rfl

theorem fourthConjugation_tensor (U : Matrix.unitaryGroup α ℂ) (A : Matrix α α ℂ) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) (matrixTensorFour A A A A) =
      matrixTensorFour (unitaryMatrixConjugationLinearMap U A)
        (unitaryMatrixConjugationLinearMap U A) (unitaryMatrixConjugationLinearMap U A)
        (unitaryMatrixConjugationLinearMap U A) := by
  change (matrixTensorFour U.val U.val U.val U.val * matrixTensorFour A A A A) *
    (matrixTensorFour U.val U.val U.val U.val).conjTranspose = _
  rw [← matrixTensorFour_conjTranspose, ← matrixTensorFour_mul, ← matrixTensorFour_mul]
  rfl

theorem hilbertSchmidt_single_left (A : Matrix α α ℂ) (b : α) :
    qubitFourthComplexHilbertSchmidt (Matrix.single b b 1) A = A b b := by
  rw [← FourthSynthesisAdjoint.hilbertSchmidt_star, hilbertSchmidt_single_diagonal, star_star]

theorem fourthConjugation_diagonal (U : Matrix.unitaryGroup α ℂ) (b : α)
    (u : EuclideanSpace ℂ α) :
    qubitFourthComplexHilbertSchmidt
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
      (unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
        (vectorProjector (vectorFourth u))) =
      ((‖⟪measurementVector U b, u⟫_ℂ‖ ^ 8 : ℝ) : ℂ) := by
  rw [hilbertSchmidt_single_left, vectorProjector_fourth, fourthConjugation_tensor,
    conjugation_vectorProjector, matrixTensorFour_apply, measurementVector_inner]
  simp only [vectorProjector, Matrix.vecMulVec_apply, Pi.star_apply, repeatedFourth]
  simp only [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem fourthAverage_diagonal (U : E → Matrix.unitaryGroup α ℂ) (b : α)
    (u : EuclideanSpace ℂ α) :
    qubitFourthComplexHilbertSchmidt
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
      (fourthAverage U (vectorProjector (vectorFourth u))) =
      (((Fintype.card E : ℝ)⁻¹ *
        ∑ e : E, ‖⟪measurementVector (U e) b, u⟫_ℂ‖ ^ 8 : ℝ) : ℂ) := by
  simp only [fourthAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    qubitFourthComplexHilbertSchmidt_smul_right,
    qubitFourthComplexHilbertSchmidt_sum_right, fourthConjugation_diagonal,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]

theorem measurementVector_reindex (e : α ≃ β) (U : Matrix.unitaryGroup α ℂ) (b : α) :
    measurementVector (reindexUnitary e U) (e b) = vectorReindex e (measurementVector U b) := by
  ext x
  change star (U.val (e.symm (e b)) (e.symm x)) = star (U.val b (e.symm x))
  rw [Equiv.symm_apply_apply]

theorem measurement_inner_reindex (e : α ≃ β) (U : Matrix.unitaryGroup α ℂ)
    (b : α) (u : EuclideanSpace ℂ α) :
    ⟪measurementVector (reindexUnitary e U) (e b), vectorReindex e u⟫_ℂ =
      ⟪measurementVector U b, u⟫_ℂ := by
  rw [measurementVector_reindex]
  exact (vectorReindex e).inner_map_map _ _

theorem fourthAverage_diagonal_reindex (e : α ≃ β) (U : E → Matrix.unitaryGroup α ℂ)
    (b : α) (u : EuclideanSpace ℂ α) :
    qubitFourthComplexHilbertSchmidt
      (Matrix.single (repeatedFourth (e b)) (repeatedFourth (e b)) 1)
      (fourthAverage (fun t => reindexUnitary e (U t))
        (vectorProjector (vectorFourth (vectorReindex e u)))) =
      qubitFourthComplexHilbertSchmidt
        (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
        (fourthAverage U (vectorProjector (vectorFourth u))) := by
  rw [fourthAverage_diagonal, fourthAverage_diagonal]
  simp_rw [measurement_inner_reindex]

theorem uniformEighthMoment_le_of_basis_bound {D : ℕ} (hD : 0 < D) [Nonempty E]
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (u : EuclideanSpace ℂ (Fin D)) (R : ℝ)
    (hb : ∀ b : Fin D,
      ‖qubitFourthComplexHilbertSchmidt
        (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
        (fourthAverage U (vectorProjector (vectorFourth u)))‖ ≤ R) :
    BornFourthMoment.finiteUnitaryUniformEighthMoment U u ≤ R := by
  have hpoint (b : Fin D) : (Fintype.card E : ℝ)⁻¹ *
      ∑ t : E, ‖⟪measurementVector (U t) b, u⟫_ℂ‖ ^ 8 ≤ R := by
    have he := fourthAverage_diagonal U b u
    have hr := Complex.re_le_norm
      (qubitFourthComplexHilbertSchmidt
        (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
        (fourthAverage U (vectorProjector (vectorFourth u))))
    rw [he, Complex.ofReal_re] at hr
    exact hr.trans (by simpa only [he] using hb b)
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin D))) (fun b _ => hpoint b)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have heq : BornFourthMoment.finiteUnitaryUniformEighthMoment U u =
      (D : ℝ)⁻¹ * ∑ b : Fin D, (Fintype.card E : ℝ)⁻¹ *
        ∑ t : E, ‖⟪measurementVector (U t) b, u⟫_ℂ‖ ^ 8 := by
    unfold BornFourthMoment.finiteUnitaryUniformEighthMoment
    change ((Fintype.card E : ℝ) * (D : ℝ))⁻¹ *
      (∑ t : E, ∑ b : Fin D, ‖⟪measurementVector (U t) b, u⟫_ℂ‖ ^ 8) = _
    rw [Finset.sum_comm, ← Finset.mul_sum, mul_inv_rev, mul_assoc]
  rw [heq]
  calc
    _ ≤ (D : ℝ)⁻¹ * ((D : ℝ) * R) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = R := by rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hD.ne'), one_mul]

end
end TomographyOracleCore.Revision.FourthMeasurementMoment
