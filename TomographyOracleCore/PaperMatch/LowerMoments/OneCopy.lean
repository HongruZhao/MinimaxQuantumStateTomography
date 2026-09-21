import TomographyOracleCore.PhysicalHaarOneCopyPearson

namespace TomographyOracleCore.PaperMatch.LowerMoments

open MeasureTheory MatrixReduction
noncomputable section

/-- The exact two-step bound in the paper, including the trace-square middle
quantity; the underlying POVM is represented by its matrix-valued density. -/
theorem one_copy_chi_square_chain {k m : ℕ} {Outcome : Type*}
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (M : PhysicalPOVM.DominatedPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U))
      ∂unitaryHaarProbability (k + 2)) ≤
        (2 * b ^ 2 / (1 - b)) * (centeredProjectorTail P * centeredProjectorTail P).trace.re ∧
    (2 * b ^ 2 / (1 - b)) * (centeredProjectorTail P * centeredProjectorTail P).trace.re ≤
      8 * b ^ 2 / (3 * m) := by
  rw [centeredProjectorTail_trace_mul_self P hm hk]
  norm_num only [Complex.sub_re, Complex.one_re, Complex.div_ofNat_re, Complex.natCast_re,
    Complex.div_re, Complex.normSq_natCast] 
  constructor
  · simpa using M.integral_unitaryHaar_pearsonChiSquare_orientedHardProjector_le_exact
      P b hm hk hb hbquarter
  · have hden : 0 < 1 - b := by linarith
    have hcoeff : 2 * b ^ 2 / (1 - b) ≤ 8 * b ^ 2 / 3 := by
      apply (div_le_iff₀ hden).2
      nlinarith [sq_nonneg b]
    have hcoefnonneg : 0 ≤ 2 * b ^ 2 / (1 - b) := by positivity
    calc
      _ ≤ (2 * b ^ 2 / (1 - b)) * (1 / (m : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (sub_le_self _ (by positivity)) hcoefnonneg
      _ ≤ (8 * b ^ 2 / 3) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = _ := by ring

end
end TomographyOracleCore.PaperMatch.LowerMoments
