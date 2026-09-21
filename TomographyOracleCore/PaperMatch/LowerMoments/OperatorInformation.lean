import TomographyOracleCore.PaperMatch.Model.DominatedPOVMBridge
import TomographyOracleCore.Revision.NonadaptiveFanoPhysical

set_option autoImplicit false

namespace TomographyOracleCore.PaperMatch.ExactMain
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalPOVM
open Revision.NonadaptiveFano
noncomputable section

/-- Lemma 12 for every countably additive normalized PSD operator-valued
measure, with the paper's trace-square intermediate term and constant. -/
theorem lemma12 {k m : ℕ} {Outcome : Type*}
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (M : OperatorPOVM (k + 2) Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
      pearsonChiSquare
        (M.bornMeasure (orientedHardProjectorDensityOperator U P b hm hb.le hbquarter))
        (M.bornMeasure (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U))
      ∂unitaryHaarProbability (k + 2)) ≤
        (2 * b ^ 2 / (1 - b)) * (centeredProjectorTail P * centeredProjectorTail P).trace.re ∧
    (2 * b ^ 2 / (1 - b)) * (centeredProjectorTail P * centeredProjectorTail P).trace.re ≤
      8 * b ^ 2 / (3 * m) :=
  LowerMoments.one_copy_chi_square_chain M.toDominated P b hm hk hb hbquarter

/-- Lemma 13 for arbitrary standard Borel public seeds and outcomes, arbitrary
operator-valued one-copy POVMs, and arbitrary randomized decoders. -/
theorem lemma13_from_lemma12 {k m T N : ℕ} [NeZero N] {Seed Outcome : Type*}
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (design : OperatorDesign (k + 2) T Seed Outcome)
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) (hN : 2 ≤ N)
    (decode : Kernel (Rotation k × (Seed × (Fin T → Outcome))) (Fin N))
    [IsMarkovKernel decode] :
    1 - ((T : ℝ) * (8 * b ^ 2 / (3 * (m : ℝ))) + Real.log 2) / Real.log N ≤
      labelError (decodedLaw
        (fun x => hardTranscriptLaw design.toDominated (P x) b hm hb hbquarter) decode) :=
  Revision.NonadaptiveFano.lemma13_from_lemma12 design.toDominated P b hm hk hb hbquarter hN decode


/-- The literal budget-parametrized statement of Lemma 13, including arbitrary
one-copy POVMs in its hypothesis. -/
theorem lemma13 {k m T N : ℕ} [NeZero N] {Seed Outcome : Type*}
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (design : OperatorDesign (k + 2) T Seed Outcome)
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b budget : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (hbudget : 0 ≤ budget) (hN : 2 ≤ N)
    (hchi : ∀ x (M : OperatorPOVM (k + 2) Outcome),
      (∫ U : Rotation k,
        pearsonChiSquare
          (M.bornMeasure (orientedHardProjectorDensityOperator U (P x) b hm hb.le hbquarter))
          (M.bornMeasure (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U))
        ∂unitaryHaarProbability (k + 2)) ≤ budget)
    (decode : Kernel (Rotation k × (Seed × (Fin T → Outcome))) (Fin N))
    [IsMarkovKernel decode] :
    1 - ((T : ℝ) * budget + Real.log 2) / Real.log N ≤
      labelError (decodedLaw
        (fun x => hardTranscriptLaw design.toDominated (P x) b hm hb hbquarter) decode) := by
  apply Revision.NonadaptiveFano.lemma13 design.toDominated P b budget hm hk hb hbquarter
    hbudget hN
  intro x M
  have h := hchi x M.toOperator
  simpa only [DominatedPOVM.toOperator_bornMeasure] using h

/-- The numerical conclusion included in Lemma 13. -/
theorem lemma13_eleven_sixteenths {k m T N : ℕ} [NeZero N] {Seed Outcome : Type*}
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome]
    (design : OperatorDesign (k + 2) T Seed Outcome)
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b budget : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (hbudget : 0 ≤ budget) (hN : 2 ≤ N)
    (hchi : ∀ x (M : OperatorPOVM (k + 2) Outcome),
      (∫ U : Rotation k,
        pearsonChiSquare
          (M.bornMeasure (orientedHardProjectorDensityOperator U (P x) b hm hb.le hbquarter))
          (M.bornMeasure (orientedHardReferenceDensityOperator k b hk hb.le hbquarter U))
        ∂unitaryHaarProbability (k + 2)) ≤ budget)
    (hinformation : (T : ℝ) * budget ≤ Real.log N / 16)
    (hlog : 4 * Real.log 2 ≤ Real.log N)
    (decode : Kernel (Rotation k × (Seed × (Fin T → Outcome))) (Fin N))
    [IsMarkovKernel decode] :
    (11 : ℝ) / 16 ≤ labelError (decodedLaw
      (fun x => hardTranscriptLaw design.toDominated (P x) b hm hb hbquarter) decode) :=
  eleven_sixteenths_of_fano _ _ hN
    (lemma13 design P b budget hm hk hb hbquarter hbudget hN hchi decode) hinformation hlog

end
end TomographyOracleCore.PaperMatch.ExactMain
