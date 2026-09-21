import TomographyOracleCore.ProjectiveHaarPOVM
import Mathlib.MeasureTheory.Constructions.Polish.EmbeddingReal

namespace TomographyOracleCore

open MeasureTheory
open scoped Classical

/-!
# Measurable real coding of finite complex matrices

The statistical decision interface currently codes seeds and outcomes by real
numbers.  This file supplies a zero-assumption Borel encoding of the actual
matrix-valued projective-Haar outcomes.
-/

section MatrixCoordinates

variable (ι : Type*) [Fintype ι]

/-- Coordinate flattening is a measurable equivalence for the coordinatewise
matrix measurable structure. -/
def complexMatrixCoordinatesMeasurableEquiv :
    Matrix ι ι ℂ ≃ᵐ (ι × ι → ℂ) where
  toEquiv := complexMatrixCoordinatesEquiv ι
  measurable_toFun := measurable_complexMatrixCoordinates ι
  measurable_invFun := by
    rw [complexMatrixMeasurableSpace, measurable_comap_iff]
    have hfun :
        complexMatrixCoordinates ι ∘ (complexMatrixCoordinatesEquiv ι).symm =
          id := by
      funext f
      exact (complexMatrixCoordinatesEquiv ι).apply_symm_apply f
    rw [hfun]
    exact measurable_id

/-- A canonical measurable embedding of complex matrices into the real line.
This also covers the empty-index, singleton-matrix case. -/
noncomputable def complexMatrixEmbeddingReal :
    Matrix ι ι ℂ → ℝ :=
  MeasureTheory.embeddingReal (Matrix ι ι ℂ)

theorem measurableEmbedding_complexMatrixEmbeddingReal :
    MeasurableEmbedding (complexMatrixEmbeddingReal ι) :=
  MeasureTheory.measurableEmbedding_embeddingReal (Matrix ι ι ℂ)

end MatrixCoordinates

section MatrixRealEquiv

variable (ι : Type*) [Fintype ι] [Nonempty ι]

private noncomputable def chosenMatrixIndex : ι :=
  Classical.choice (inferInstance : Nonempty ι)

/-- Put a real number into one fixed diagonal entry of a complex matrix. -/
private noncomputable def realDiagonalMatrixEmbedding
    (r : ℝ) : Matrix ι ι ℂ :=
  fun i j ↦
    if i = chosenMatrixIndex ι ∧ j = chosenMatrixIndex ι then (r : ℂ) else 0

private theorem realDiagonalMatrixEmbedding_injective :
    Function.Injective (realDiagonalMatrixEmbedding ι) := by
  intro x y hxy
  have hentry := congrFun (congrFun hxy (chosenMatrixIndex ι))
    (chosenMatrixIndex ι)
  have hcond :
      chosenMatrixIndex ι = chosenMatrixIndex ι ∧
        chosenMatrixIndex ι = chosenMatrixIndex ι := ⟨rfl, rfl⟩
  simp only [realDiagonalMatrixEmbedding, if_pos hcond] at hentry
  exact Complex.ofReal_injective hentry

/-- A nonempty finite complex matrix space is uncountable. -/
theorem not_countable_complexMatrix :
    ¬ Countable (Matrix ι ι ℂ) := by
  intro hmatrix
  letI : Countable (Matrix ι ι ℂ) := hmatrix
  letI : Countable ℝ := (realDiagonalMatrixEmbedding_injective ι).countable
  exact (not_countable_iff.mpr (inferInstance : Uncountable ℝ)) inferInstance

/-- For a nonempty finite coordinate type, complex matrices and the real line
are Borel isomorphic.  Thus an `ℝ`-coded interface can carry a matrix outcome
without adding any scientific assumption. -/
noncomputable def complexMatrixRealMeasurableEquiv :
    Matrix ι ι ℂ ≃ᵐ ℝ :=
  PolishSpace.measurableEquivOfNotCountable
    (not_countable_complexMatrix ι)
    (not_countable_iff.mpr (inferInstance : Uncountable ℝ))

theorem measurable_complexMatrixRealMeasurableEquiv :
    Measurable (complexMatrixRealMeasurableEquiv ι : Matrix ι ι ℂ → ℝ) :=
  (complexMatrixRealMeasurableEquiv ι).measurable

theorem measurable_complexMatrixRealMeasurableEquiv_symm :
    Measurable ((complexMatrixRealMeasurableEquiv ι).symm : ℝ → Matrix ι ι ℂ) :=
  (complexMatrixRealMeasurableEquiv ι).symm.measurable

end MatrixRealEquiv

end TomographyOracleCore
