import TomographyOracleCore.SharedHaarFanoAssembly
import TomographyOracleCore.PaperMatch.Model.StatesRisk

/-! The existing physical shared-orientation Fano proof on an arbitrary
parameter class. The only change from the spectral-class theorem is the
class membership used to bound the statewise expectation by the supremum. -/
namespace TomographyOracleCore.PaperMatch
open MeasureTheory ProbabilityTheory InformationTheory MatrixReduction PhysicalRisk PhysicalPOVM
open scoped BigOperators ENNReal Matrix.Norms.L2Operator
noncomputable section
variable {D T N : ℕ} [NeZero N]
  {Orientation : Type*} [MeasurableSpace Orientation]
  [StandardBorelSpace Orientation]

theorem sharedHaar_lower_on
    (C : Set (DensityOperator (Fin D)))
    (hN : 2 ≤ N)
    (design : Design D T) (estimator : Estimator D T)
    (orientationLaw : Measure Orientation)
    [IsProbabilityMeasure orientationLaw]
    (state : Fin N → Orientation → DensityOperator (Fin D))
    (reference : Orientation → DensityOperator (Fin D))
    (hstate : ∀ a, Measurable (state a))
    (hreference : Measurable reference)
    (radius : ℝ) (hradius : 0 ≤ radius)
    (hmembership : ∀ w a,
      state a w ∈ C)
    (hseparated : ∀ w a b, a ≠ b →
      2 * radius ≤ realHermitianTraceLoss (state a w) (state b w))
    (budget : Fin T → ENNReal)
    (hbudgetFinite : (∑ t, budget t) ≠ ∞)
    (honeCopy : ∀ a t,
      klDiv
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design (state a) (hstate a) t)
          ((orientationLaw.prod design.seed) ⊗ₘ
            RandomizedNonadaptiveDesign.sharedOrientationShotKernel
              design reference hreference t) ≤ budget t)
    (hinformation : (∑ t, budget t).toReal ≤ Real.log N / 16)
    (hlogTwo : 4 * Real.log 2 ≤ Real.log N) :
    ENNReal.ofReal (11 * radius / 16) ≤
      Model.worstCaseRiskOn C design estimator := by
  let kappa := sharedHaarDecodedLabelKernel design estimator
    orientationLaw state hstate
  let J := FiniteUniformJoint.ofMarkovKernel kappa
  have hposterior : J.posteriorKLSum ≤ Real.log N / 16 := by
    exact (sharedHaarDecoded_posteriorKLSum_le_budget_toReal
      design estimator orientationLaw state reference hstate hreference
        budget hbudgetFinite honeCopy).trans hinformation
  have hfano : (11 : ℝ) / 16 ≤
      (J.toPosteriorExperiment id).errorProbability := by
    apply J.eleven_sixteenths_le_errorProbability_of_posteriorKLSum_proved
    · simpa [Fintype.card_fin] using hN
    · simpa [J, Fintype.card_fin] using hposterior
    · simpa [Fintype.card_fin] using hlogTwo
  have hfanoENN : ENNReal.ofReal ((11 : ℝ) / 16) ≤
      ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) :=
    ENNReal.ofReal_le_ofReal hfano
  let worst := Model.worstCaseRiskOn C design estimator
  have hpoint (a : Fin N) :
      ENNReal.ofReal radius * kappa a {y | y ≠ a} ≤ worst := by
    have hforces : ∀ p : Orientation × DensityOperator (Fin D),
        orientedFiniteTraceNearestDecoder state p ≠ a →
          ENNReal.ofReal radius ≤ hermitianTraceLoss (state a p.1) p.2 := by
      intro p hp
      rw [orientedFiniteTraceNearestDecoder_eq] at hp
      exact
        ofReal_radius_le_hermitianTraceLoss_of_finiteTraceNearestDecoder_ne
          (fun b ↦ state b p.1) radius (hseparated p.1) a p.2 hp
    calc
      ENNReal.ofReal radius * kappa a {y | y ≠ a} ≤
          ∫⁻ w, statewiseExpectedTraceRisk design estimator (state a w)
            ∂orientationLaw := by
        exact ofReal_radius_mul_sharedHaar_wrongProbability_le_integratedRisk
          design estimator orientationLaw state hstate radius a hforces
      _ ≤ ∫⁻ _w, worst ∂orientationLaw := by
        apply lintegral_mono
        intro w
        exact le_iSup (fun rho : C =>
          statewiseExpectedTraceRisk design estimator rho.1)
            ⟨state a w, hmembership w a⟩
      _ = worst := by simp
  have hsum :
      ENNReal.ofReal radius * ∑ a, kappa a {y | y ≠ a} ≤
        ∑ _a : Fin N, worst := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ha ↦ hpoint a
  have havgWrong :
      ENNReal.ofReal radius *
          ((N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a}) ≤ worst := by
    have hcard0 : (N : ENNReal) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le (by omega : 0 < 2) hN)
    have hcardtop : (N : ENNReal) ≠ ∞ := by simp
    calc
      ENNReal.ofReal radius *
          ((N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a}) =
        (N : ENNReal)⁻¹ *
          (ENNReal.ofReal radius * ∑ a, kappa a {y | y ≠ a}) := by
            ac_rfl
      _ ≤ (N : ENNReal)⁻¹ * ∑ _a : Fin N, worst :=
        mul_le_mul' le_rfl hsum
      _ = (N : ENNReal)⁻¹ * ((N : ENNReal) * worst) := by
        simp [nsmul_eq_mul]
      _ = worst := ENNReal.inv_mul_cancel_left hcard0 hcardtop
  have herrorENN :
      ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) =
        (N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a} := by
    simpa [J] using
      (ofReal_ofMarkovKernel_errorProbability_id_eq (N := N) kappa)
  calc
    ENNReal.ofReal (11 * radius / 16) =
        ENNReal.ofReal radius * ENNReal.ofReal ((11 : ℝ) / 16) := by
      rw [show 11 * radius / 16 = radius * ((11 : ℝ) / 16) by ring,
        ENNReal.ofReal_mul hradius]
    _ ≤ ENNReal.ofReal radius *
        ENNReal.ofReal ((J.toPosteriorExperiment id).errorProbability) :=
      mul_le_mul' le_rfl hfanoENN
    _ = ENNReal.ofReal radius *
        ((N : ENNReal)⁻¹ * ∑ a, kappa a {y | y ≠ a}) := by
      rw [herrorENN]
    _ ≤ worst := havgWrong


end
end TomographyOracleCore.PaperMatch
