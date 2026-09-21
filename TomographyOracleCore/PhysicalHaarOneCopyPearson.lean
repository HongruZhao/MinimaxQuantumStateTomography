import TomographyOracleCore.PhysicalHaarOneCopyPOVMLift
import TomographyOracleCore.PhysicalReferencePearson

namespace TomographyOracleCore

open MeasureTheory
open MatrixReduction
open scoped ENNReal ComplexOrder

noncomputable section

/-- Move unitary conjugation from the first factor of a trace pairing to
inverse conjugation of the second factor. -/
theorem trace_unitaryConjugateMatrix_mul
    {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A E : Matrix (Fin D) (Fin D) ℂ) :
    (unitaryConjugateMatrix U A * E).trace =
      (A * unitaryConjugateMatrix U⁻¹ E).trace := by
  rw [unitaryConjugateMatrix_apply, unitaryConjugateMatrix_apply]
  calc
    (((U : Matrix (Fin D) (Fin D) ℂ) * A *
          star (U : Matrix (Fin D) (Fin D) ℂ)) * E).trace =
        ((U : Matrix (Fin D) (Fin D) ℂ) *
          (A * star (U : Matrix (Fin D) (Fin D) ℂ) * E)).trace := by
            simp only [mul_assoc]
    _ = ((A * star (U : Matrix (Fin D) (Fin D) ℂ) * E) *
          (U : Matrix (Fin D) (Fin D) ℂ)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (A * (((U⁻¹ : unitary (Matrix (Fin D) (Fin D) ℂ)) :
          Matrix (Fin D) (Fin D) ℂ) * E *
          star (((U⁻¹ : unitary (Matrix (Fin D) (Fin D) ℂ)) :
            Matrix (Fin D) (Fin D) ℂ)))).trace := by simp [mul_assoc]

theorem orientedHardReferenceMatrix_born_re_tail_lower
    (k : ℕ) (b : ℝ) (hk : 1 ≤ k)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)
    (hE : E.PosSemidef) (htrace : E.trace = 1) :
    b / (k : ℝ) ≤
      (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re := by
  rw [trace_unitaryConjugateMatrix_mul]
  exact hardReferenceMatrix_born_re_tail_lower k b hk hb0 hbquarter
    (unitaryConjugateMatrix U⁻¹ E)
    (unitaryConjugateMatrix_posSemidef U⁻¹ hE)
    (by rw [unitaryConjugateMatrix_trace, htrace])

namespace PhysicalPOVM.DominatedPOVM

variable {k m : ℕ} {Outcome : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

theorem orientedHardReferenceBornDensity_ae_tail_lower
    (M : DominatedPOVM (k + 2) Outcome)
    (hk : 1 ≤ k) (b : ℝ) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    ∀ᵐ z ∂M.base,
      ENNReal.ofReal (b / (k : ℝ)) ≤
        bornDensityFrom M.effect
          (orientedHardReferenceDensityOperator k b hk hb0 hbquarter U) z := by
  filter_upwards [M.effect_ae_posSemidef, M.effect_ae_trace_one] with z hpos htrace
  unfold bornDensityFrom
  apply ENNReal.ofReal_le_ofReal
  exact orientedHardReferenceMatrix_born_re_tail_lower
    k b hk hb0 hbquarter U (M.effect z) hpos htrace

theorem orientedHardReferenceBornDensity_ae_ne_zero
    (M : DominatedPOVM (k + 2) Outcome)
    (hk : 1 ≤ k) (b : ℝ) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    ∀ᵐ z ∂M.base,
      bornDensityFrom M.effect
        (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U) z ≠ 0 := by
  have hkR : 0 < (k : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hbdiv : 0 < b / (k : ℝ) := div_pos hb hkR
  filter_upwards [orientedHardReferenceBornDensity_ae_tail_lower
      M hk b hb.le hbquarter U] with z hz
  exact ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hbdiv) hz)

end PhysicalPOVM.DominatedPOVM

theorem unitaryConjugateMatrix_real_smul
    {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (b : ℝ) (A : Matrix (Fin D) (Fin D) ℂ) :
    unitaryConjugateMatrix U (b • A) =
      b • unitaryConjugateMatrix U A := by
  change (Unitary.conjStarAlgAut ℂ _ U) ((b : ℂ) • A) =
    (b : ℂ) • (Unitary.conjStarAlgAut ℂ _ U) A
  exact map_smul (Unitary.conjStarAlgAut ℂ _ U) (b : ℂ) A

theorem trace_orientedHardProjector_mul_sub_trace_orientedHardReference_mul
    {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
    (unitaryConjugateMatrix U (hardProjectorMatrix P b) * E).trace -
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace =
      b • (unitaryConjugateMatrix U (embeddedCenteredProjectorTail P) * E).trace := by
  calc
    _ = ((unitaryConjugateMatrix U (hardProjectorMatrix P b) -
          unitaryConjugateMatrix U (hardReferenceMatrix k b)) * E).trace := by
      rw [sub_mul, Matrix.trace_sub]
    _ = (unitaryConjugateMatrix U
          (hardProjectorMatrix P b - hardReferenceMatrix k b) * E).trace := by
      rw [unitaryConjugateMatrix_sub]
    _ = (unitaryConjugateMatrix U
          (b • embeddedCenteredProjectorTail P) * E).trace := by
      rw [hardProjectorMatrix_sub_hardReferenceMatrix_eq_smul]
    _ = ((b • unitaryConjugateMatrix U
          (embeddedCenteredProjectorTail P)) * E).trace := by
      rw [unitaryConjugateMatrix_real_smul]
    _ = b • (unitaryConjugateMatrix U
          (embeddedCenteredProjectorTail P) * E).trace := by
      rw [Matrix.smul_mul, Matrix.trace_smul]

theorem bornTrace_orientedHardProjector_sub_orientedHardReference
    {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) :
    (unitaryConjugateMatrix U (hardProjectorMatrix P b) * E).trace.re -
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re =
      b * (unitaryConjugateMatrix U
        (embeddedCenteredProjectorTail P) * E).trace.re := by
  have h := congrArg Complex.re
    (trace_orientedHardProjector_mul_sub_trace_orientedHardReference_mul U P b E)
  simpa using h

namespace PhysicalPOVM.DominatedPOVM

variable {k m : ℕ} {Outcome : Type*}
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

theorem pearsonChiSquare_orientedHardProjector_orientedHardReference_eq_bornDensity_integral
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U)) =
      ∫ z,
        ((bornDensityFrom M.effect
              (orientedHardProjectorDensityOperator U P b hm hb.le hbquarter) z).toReal -
            (bornDensityFrom M.effect
              (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U) z).toReal) ^ 2 /
          (bornDensityFrom M.effect
            (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U) z).toReal
        ∂M.base := by
  letI : IsFiniteMeasure M.base := M.base_finite
  change pearsonChiSquare
      (M.base.withDensity
        (bornDensityFrom M.effect
          (orientedHardProjectorDensityOperator U P b hm hb.le hbquarter)))
      (M.base.withDensity
        (bornDensityFrom M.effect
          (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U))) = _
  exact pearsonChiSquare_withDensity_eq_integral M.base _ _
    (measurable_bornDensityFrom M _).aemeasurable
    (measurable_bornDensityFrom M _).aemeasurable
    (bornDensityFrom_ae_ne_top M _)
    (orientedHardReferenceBornDensity_ae_ne_zero M hk b hb hbquarter U)
    (bornDensityFrom_ae_ne_top M _)

theorem pearsonChiSquare_orientedHardProjector_orientedHardReference_eq_integral
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U)) =
      ∫ z, orientedEffectPearsonIntegrand k b (centeredProjectorTail P)
        (M.effect z) U ∂M.base := by
  rw [pearsonChiSquare_orientedHardProjector_orientedHardReference_eq_bornDensity_integral
    M P b hm hk hb hbquarter U]
  apply integral_congr_ae
  filter_upwards [
      M.born_density_ae_nonnegative
        (orientedHardProjectorDensityOperator U P b hm hb.le hbquarter),
      M.born_density_ae_nonnegative
        (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U)] with z hp hq
  unfold bornDensityFrom
  rw [ENNReal.toReal_ofReal hp, ENNReal.toReal_ofReal hq]
  change
    ((unitaryConjugateMatrix U (hardProjectorMatrix P b) * M.effect z).trace.re -
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * M.effect z).trace.re) ^ 2 /
      (unitaryConjugateMatrix U (hardReferenceMatrix k b) * M.effect z).trace.re = _
  rw [bornTrace_orientedHardProjector_sub_orientedHardReference U P b (M.effect z)]
  unfold orientedEffectPearsonIntegrand
  rw [embeddedTailMatrix_eq_embeddedCenteredProjectorTail]

/-- Exact arbitrary-standard-Borel one-copy Pearson bound, averaged over one
shared Haar orientation. -/
theorem integral_unitaryHaar_pearsonChiSquare_orientedHardProjector_le_exact
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U))
      ∂unitaryHaarProbability (k + 2)) ≤
      (2 * b ^ 2 / (1 - b)) *
        (1 / (m : ℝ) - 1 / (k : ℝ)) := by
  have hb1 : b < 1 := lt_of_le_of_lt hbquarter (by norm_num)
  calc
    _ = ∫ U, ∫ z,
          orientedPOVMEffectPearsonIntegrand k b (centeredProjectorTail P)
            M z U ∂M.base ∂unitaryHaarProbability (k + 2) := by
      apply integral_congr_ae
      filter_upwards with U
      rw [pearsonChiSquare_orientedHardProjector_orientedHardReference_eq_integral
        M P b hm hk hb hbquarter U]
      rfl
    _ ≤ (2 * b ^ 2 / (1 - b)) *
          (centeredProjectorTail P * centeredProjectorTail P).trace.re :=
      integral_unitaryHaar_integral_orientedPOVMEffectPearsonIntegrand_le
        k hk b hb.le hbquarter hb1 (centeredProjectorTail P)
          (centeredProjectorTail_isHermitian P)
          (centeredProjectorTail_trace_eq_zero P hm hk) M
    _ = _ := by
      rw [centeredProjectorTail_trace_mul_self P hm hk]
      norm_num

/-- Dimension-free simplification of the exact one-copy Pearson bound used
by the minimax lower argument. -/
theorem integral_unitaryHaar_pearsonChiSquare_orientedHardProjector_le
    (M : DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator
          U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator
          k b hk hb.le hbquarter U))
      ∂unitaryHaarProbability (k + 2)) ≤
      8 * b ^ 2 / (3 * (m : ℝ)) := by
  have hb1 : b < 1 := lt_of_le_of_lt hbquarter (by norm_num)
  have hden : 0 < 1 - b := sub_pos.mpr hb1
  have hden34 : (3 : ℝ) / 4 ≤ 1 - b := by linarith
  have hcoeff : 2 * b ^ 2 / (1 - b) ≤ 8 * b ^ 2 / 3 := by
    apply (div_le_iff₀ hden).2
    calc
      2 * b ^ 2 = (8 * b ^ 2 / 3) * ((3 : ℝ) / 4) := by ring
      _ ≤ (8 * b ^ 2 / 3) * (1 - b) := by
        exact mul_le_mul_of_nonneg_left hden34 (by positivity)
  have hcoefnonneg : 0 ≤ 2 * b ^ 2 / (1 - b) := by positivity
  have hkinv : 0 ≤ 1 / (k : ℝ) := by positivity
  have hminv : 0 ≤ 1 / (m : ℝ) := by positivity
  calc
    _ ≤ (2 * b ^ 2 / (1 - b)) *
          (1 / (m : ℝ) - 1 / (k : ℝ)) :=
      integral_unitaryHaar_pearsonChiSquare_orientedHardProjector_le_exact
        M P b hm hk hb hbquarter
    _ ≤ (2 * b ^ 2 / (1 - b)) * (1 / (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left (sub_le_self _ hkinv) hcoefnonneg
    _ ≤ (8 * b ^ 2 / 3) * (1 / (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_right hcoeff hminv
    _ = 8 * b ^ 2 / (3 * (m : ℝ)) := by ring

end PhysicalPOVM.DominatedPOVM

end

end TomographyOracleCore

