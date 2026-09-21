import TomographyOracleCore.Revision.NonadaptiveFanoReduction
import TomographyOracleCore.PhysicalHaarOneCopyDesignKL
import TomographyOracleCore.PaperMatch.LowerMoments.OneCopy

namespace TomographyOracleCore.Revision.NonadaptiveFano

open MeasureTheory ProbabilityTheory InformationTheory MatrixReduction PhysicalPOVM
open PhysicalPOVM.RandomizedNonadaptiveDesign
open scoped BigOperators ENNReal
noncomputable section

/-! The paper's Haar-rotated hard family and its one-copy chi-square
hypothesis, with arbitrary standard-Borel seed and outcome spaces. -/

variable {k m T : ℕ} {Seed Outcome : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

theorem shotKL_of_chiSquare_bound
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k)
    (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (budget : ℝ)
    (hchi : ∀ M : DominatedPOVM (k + 2) Outcome,
      (∫ U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ),
        pearsonChiSquare
          (M.bornMeasure (orientedHardProjectorDensityOperator
            U P b hm hb.le hbquarter))
          (M.bornMeasure (orientedHardReferenceDensityOperator
            k b hk hb.le hbquarter U))
        ∂unitaryHaarProbability (k + 2)) ≤ budget)
    (t : Fin T) :
    klDiv
        (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design
            (fun U ↦ orientedHardProjectorDensityOperator
              U P b hm hb.le hbquarter)
            (measurable_orientedHardProjectorDensityOperator
              P b hm hb.le hbquarter) t)
        (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ
          sharedOrientationShotKernel design
            (orientedHardReferenceDensityOperator
              k b hk hb.le hbquarter)
            (measurable_orientedHardReferenceDensityOperator
              k b hk hb.le hbquarter) t) ≤
      ENNReal.ofReal (budget) := by
  let : IsProbabilityMeasure design.seed := design.seed_probability
  let stateP := fun U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
    orientedHardProjectorDensityOperator U P b hm hb.le hbquarter
  let stateQ := orientedHardReferenceDensityOperator
    k b hk hb.le hbquarter
  have hstateP : Measurable stateP :=
    measurable_orientedHardProjectorDensityOperator P b hm hb.le hbquarter
  have hstateQ : Measurable stateQ :=
    measurable_orientedHardReferenceDensityOperator k b hk hb.le hbquarter
  let κ := sharedOrientationShotKernel design stateP hstateP t
  let η := sharedOrientationShotKernel design stateQ hstateQ t
  let : IsMarkovKernel κ := by dsimp [κ]; infer_instance
  let : IsMarkovKernel η := by dsimp [η]; infer_instance
  have hac : ∀ z, κ z ≪ η z := by
    intro z
    let M := design.measurement t z.2
    change
      (sharedOrientationShotKernel design stateP hstateP t) z ≪
        (sharedOrientationShotKernel design stateQ hstateQ t) z
    rw [sharedOrientationShotKernel_apply, sharedOrientationShotKernel_apply]
    change M.bornMeasure (stateP z.1) ≪ M.bornMeasure (stateQ z.1)
    unfold DominatedPOVM.bornMeasure bornMeasureFrom
    exact withDensity_absolutelyContinuous_withDensity M.base _ _
      (DominatedPOVM.measurable_bornDensityFrom M (stateQ z.1)).aemeasurable
      (by
        simpa only [stateQ] using
          (DominatedPOVM.orientedHardReferenceBornDensity_ae_ne_zero
            M hk b hb hbquarter z.1))
  change klDiv
      (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ κ)
      (((unitaryHaarProbability (k + 2)).prod design.seed) ⊗ₘ η) ≤ _
  rw [klDiv_compProd_same_eq_lintegral_kernelConditionalKL
    ((unitaryHaarProbability (k + 2)).prod design.seed) κ η hac]
  rw [lintegral_prod_symm]
  · calc
      (∫⁻ s, ∫⁻ U, kernelConditionalKL κ η (U, s)
          ∂unitaryHaarProbability (k + 2) ∂design.seed) ≤
          ∫⁻ _s, ENNReal.ofReal (budget) ∂design.seed := by
            apply lintegral_mono
            intro s
            let M := design.measurement t s
            let fiberKL := fun U : unitary
                (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) ↦
              klDiv
                (M.bornMeasure (orientedHardProjectorDensityOperator
                  U P b hm hb.le hbquarter))
                (M.bornMeasure (orientedHardReferenceDensityOperator
                  k b hk hb.le hbquarter U))
            have hcond : ∀ U, kernelConditionalKL κ η (U, s) = fiberKL U := by
              intro U
              rw [kernelConditionalKL_eq_klDiv κ η (U, s) (hac (U, s))]
              rfl
            have hfinite : ∀ᵐ U ∂unitaryHaarProbability (k + 2),
                fiberKL U ≠ ∞ := by
              simpa only [fiberKL, M] using
                (DominatedPOVM.ae_klDiv_orientedHardProjector_orientedHardReference_ne_top
                  M P b hm hk hb hbquarter)
            have hint : Integrable (fun U ↦ (fiberKL U).toReal)
                (unitaryHaarProbability (k + 2)) := by
              simpa only [fiberKL, M] using
                (DominatedPOVM.integrable_toReal_klDiv_orientedHardProjector_orientedHardReference
                  M P b hm hk hb hbquarter)
            calc
              (∫⁻ U, kernelConditionalKL κ η (U, s)
                  ∂unitaryHaarProbability (k + 2)) =
                  ∫⁻ U, fiberKL U ∂unitaryHaarProbability (k + 2) := by
                    exact lintegral_congr hcond
              _ = ∫⁻ U, ENNReal.ofReal (fiberKL U).toReal
                    ∂unitaryHaarProbability (k + 2) := by
                  apply lintegral_congr_ae
                  filter_upwards [hfinite] with U hU
                  exact (ENNReal.ofReal_toReal hU).symm
              _ = ENNReal.ofReal
                    (∫ U, (fiberKL U).toReal
                      ∂unitaryHaarProbability (k + 2)) := by
                  symm
                  apply ofReal_integral_eq_lintegral_ofReal hint
                  filter_upwards with U
                  exact ENNReal.toReal_nonneg
              _ ≤ ENNReal.ofReal (budget) := by
                  apply ENNReal.ofReal_le_ofReal
                  simpa only [fiberKL, M] using
                    (DominatedPOVM.integral_unitaryHaar_toReal_klDiv_orientedHardProjector_le_pearsonChiSquare
                      M P b hm hk hb hbquarter).trans (hchi M)
      _ = ENNReal.ofReal (budget) := by simp
  · exact (measurable_kernelConditionalKL κ η).aemeasurable


/-- Unitaries carrying the one shared physical Haar rotation. -/
abbrev Rotation (k : ℕ) := unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)

/-- The actual law of `(W,R,Y^T)` under one member of the rotated family. -/
def hardTranscriptLaw (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    Measure (Rotation k × (Seed × (Fin T → Outcome))) :=
  (unitaryHaarProbability (k + 2)) ⊗ₘ
    design.experimentKernel.comap
      (fun U => orientedHardProjectorDensityOperator U P b hm hb.le hbquarter)
      (measurable_orientedHardProjectorDensityOperator P b hm hb.le hbquarter)

instance hardTranscriptLaw_probability
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    IsProbabilityMeasure (hardTranscriptLaw design P b hm hb hbquarter) := by
  let : IsProbabilityMeasure design.seed := design.seed_probability
  unfold hardTranscriptLaw
  infer_instance

/-- The hypothetical reference record uses the same rotation, public seed,
and preselected POVMs. -/
def referenceTranscriptLaw (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (b : ℝ) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    Measure (Rotation k × (Seed × (Fin T → Outcome))) :=
  (unitaryHaarProbability (k + 2)) ⊗ₘ
    design.experimentKernel.comap
      (orientedHardReferenceDensityOperator k b hk hb.le hbquarter)
      (measurable_orientedHardReferenceDensityOperator k b hk hb.le hbquarter)

instance referenceTranscriptLaw_probability
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (b : ℝ) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4) :
    IsProbabilityMeasure (referenceTranscriptLaw design b hk hb hbquarter) := by
  let : IsProbabilityMeasure design.seed := design.seed_probability
  unfold referenceTranscriptLaw
  infer_instance

/-- Paper Lemma 13: for every label and every one-copy POVM, the assumed
Haar-averaged Pearson bound implies the displayed Fano lower bound for every
randomized decoder of the full augmented record. -/
theorem lemma13 {N : ℕ} [NeZero N]
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b budget : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (hbudget : 0 ≤ budget) (hN : 2 ≤ N)
    (hchi : ∀ x (M : DominatedPOVM (k + 2) Outcome),
      (∫ U : Rotation k,
        pearsonChiSquare
          (M.bornMeasure (orientedHardProjectorDensityOperator
            U (P x) b hm hb.le hbquarter))
          (M.bornMeasure (orientedHardReferenceDensityOperator
            k b hk hb.le hbquarter U))
        ∂unitaryHaarProbability (k + 2)) ≤ budget)
    (decode : Kernel (Rotation k × (Seed × (Fin T → Outcome))) (Fin N))
    [IsMarkovKernel decode] :
    1 - ((T : ℝ) * budget + Real.log 2) / Real.log N ≤
      labelError (decodedLaw
        (fun x => hardTranscriptLaw design (P x) b hm hb hbquarter) decode) := by
  apply fano_of_referenceKL
    (fun x => hardTranscriptLaw design (P x) b hm hb hbquarter)
    (referenceTranscriptLaw design b hk hb hbquarter) decode
    ((T : ℝ) * budget) (by positivity) hN
  intro x
  unfold hardTranscriptLaw referenceTranscriptLaw
  rw [orientationCompProdExperiment_klDiv_eq_sum]
  calc
    _ ≤ ∑ t : Fin T, ENNReal.ofReal budget := by
      apply Finset.sum_le_sum
      intro t _
      exact shotKL_of_chiSquare_bound design (P x) b hm hk hb hbquarter budget (hchi x) t
    _ = ENNReal.ofReal ((T : ℝ) * budget) := by
      simp [ENNReal.ofReal_mul, nsmul_eq_mul]

/-- The constants in the `in particular` clause of Lemma 13. -/
theorem eleven_sixteenths_of_fano {N T : ℕ} (budget error : ℝ)
    (hN : 2 ≤ N)
    (hfano : 1 - ((T : ℝ) * budget + Real.log 2) / Real.log N ≤ error)
    (hinformation : (T : ℝ) * budget ≤ Real.log N / 16)
    (hlog : 4 * Real.log 2 ≤ Real.log N) :
    (11 : ℝ) / 16 ≤ error := by
  exact (fanoErrorLower_ge_eleven_sixteenths ((T : ℝ) * budget) (Real.log N)
    (Real.log_pos (by exact_mod_cast hN)) hinformation hlog).trans hfano

/-- Lemma 12 discharges the chi-square hypothesis of Lemma 13, giving the
paper's exact coefficient `8 T beta^2 / (3 m)` for all randomized decoders. -/
theorem lemma13_from_lemma12 {N : ℕ} [NeZero N]
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (hN : 2 ≤ N)
    (decode : Kernel (Rotation k × (Seed × (Fin T → Outcome))) (Fin N))
    [IsMarkovKernel decode] :
    1 - ((T : ℝ) * (8 * b ^ 2 / (3 * (m : ℝ))) + Real.log 2) / Real.log N ≤
      labelError (decodedLaw
        (fun x => hardTranscriptLaw design (P x) b hm hb hbquarter) decode) := by
  apply lemma13 design P b (8 * b ^ 2 / (3 * (m : ℝ))) hm hk hb hbquarter
    (by positivity) hN
  intro x M
  have h := PaperMatch.LowerMoments.one_copy_chi_square_chain M (P x) b hm hk hb hbquarter
  exact h.1.trans h.2

/-- The exact 11/16 conclusion after instantiating Lemma 13 with Lemma 12. -/
theorem lemma13_eleven_sixteenths {N : ℕ} [NeZero N]
    (design : RandomizedNonadaptiveDesign (k + 2) T Seed Outcome)
    (P : Fin N → RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hk : 1 ≤ k) (hb : 0 < b) (hbquarter : b ≤ 1 / 4)
    (hN : 2 ≤ N)
    (hinformation : (T : ℝ) * (8 * b ^ 2 / (3 * (m : ℝ))) ≤ Real.log N / 16)
    (hlog : 4 * Real.log 2 ≤ Real.log N)
    (decode : Kernel (Rotation k × (Seed × (Fin T → Outcome))) (Fin N))
    [IsMarkovKernel decode] :
    (11 : ℝ) / 16 ≤ labelError (decodedLaw
      (fun x => hardTranscriptLaw design (P x) b hm hb hbquarter) decode) := by
  exact eleven_sixteenths_of_fano _ _ hN
    (lemma13_from_lemma12 design P b hm hk hb hbquarter hN decode) hinformation hlog

end
end TomographyOracleCore.Revision.NonadaptiveFano
