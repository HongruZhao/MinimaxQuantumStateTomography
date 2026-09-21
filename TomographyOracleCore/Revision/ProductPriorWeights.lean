import TomographyOracleCore.Candidate2PACBayesVariational
import Mathlib.MeasureTheory.Integral.Pi

namespace TomographyOracleCore.Revision.ProductPriorWeights

open MeasureTheory InformationTheory
open scoped BigOperators
noncomputable section

variable {X Theta : Type*} [MeasurableSpace X] [MeasurableSpace Theta]
    (mu : Measure X) (prior : Measure Theta) [IsProbabilityMeasure mu] [IsProbabilityMeasure prior]

def productWeight {T : ℕ} (w : X → Theta → ℝ) (sample : Fin T → X) (theta : Theta) : ℝ :=
  ∏ i, w (sample i) theta

def priorWeight {T : ℕ} (w : X → Theta → ℝ) (sample : Fin T → X) : ℝ :=
  ∫ theta, productWeight w sample theta ∂prior

theorem integrable_productWeight_sample {T : ℕ} (w : X → Theta → ℝ)
    (hi : ∀ theta, Integrable (fun x => w x theta) mu) (theta : Theta) :
    Integrable (fun sample : Fin T → X => productWeight w sample theta)
      (Measure.pi (fun _ : Fin T => mu)) :=
  Integrable.fintype_prod_dep (fun _ => hi theta)

theorem integral_productWeight_sample {T : ℕ} (w : X → Theta → ℝ)
    (hnormal : ∀ theta, (∫ x, w x theta ∂mu) = 1) (theta : Theta) :
    (∫ sample : Fin T → X, productWeight w sample theta ∂Measure.pi (fun _ : Fin T => mu)) = 1 := by
  unfold productWeight
  rw [integral_fintype_prod_eq_prod (f := fun _ : Fin T => fun x : X => w x theta)]
  simp [hnormal]

theorem measurable_productWeight {T : ℕ} (w : X → Theta → ℝ)
    (hw : Measurable (fun z : X × Theta => w z.1 z.2)) :
    Measurable (fun z : (Fin T → X) × Theta => productWeight w z.1 z.2) := by
  unfold productWeight
  apply Finset.measurable_prod
  intro i _
  exact hw.comp (show Measurable (fun z : (Fin T → X) × Theta => (z.1 i, z.2)) by fun_prop)

theorem productWeight_pos {T : ℕ} (w : X → Theta → ℝ) (hw : ∀ x theta, 0 < w x theta)
    (sample : Fin T → X) (theta : Theta) : 0 < productWeight w sample theta :=
  Finset.prod_pos fun i _ => hw (sample i) theta

theorem integrable_productWeight_joint {T : ℕ} (w : X → Theta → ℝ)
    (hw : Measurable (fun z : X × Theta => w z.1 z.2)) (hpos : ∀ x theta, 0 < w x theta)
    (hi : ∀ theta, Integrable (fun x => w x theta) mu)
    (hnormal : ∀ theta, (∫ x, w x theta ∂mu) = 1) :
    Integrable (fun z : (Fin T → X) × Theta => productWeight w z.1 z.2)
      ((Measure.pi (fun _ : Fin T => mu)).prod prior) := by
  apply (integrable_prod_iff' (measurable_productWeight w hw).aestronglyMeasurable).2
  constructor
  · exact ae_of_all _ (integrable_productWeight_sample mu w hi)
  · have heq : (fun theta => ∫ sample : Fin T → X, ‖productWeight w sample theta‖
        ∂Measure.pi (fun _ : Fin T => mu)) = fun _ => (1 : ℝ) := by
      funext theta
      simp only [Real.norm_eq_abs, abs_of_pos (productWeight_pos w hpos _ _)]
      exact integral_productWeight_sample mu w hnormal theta
    rw [heq]
    exact integrable_const _

theorem integrable_priorWeight {T : ℕ} (w : X → Theta → ℝ)
    (hw : Measurable (fun z : X × Theta => w z.1 z.2)) (hpos : ∀ x theta, 0 < w x theta)
    (hi : ∀ theta, Integrable (fun x => w x theta) mu)
    (hnormal : ∀ theta, (∫ x, w x theta ∂mu) = 1) :
    Integrable (priorWeight prior w : (Fin T → X) → ℝ) (Measure.pi (fun _ : Fin T => mu)) :=
  (integrable_productWeight_joint mu prior w hw hpos hi hnormal).integral_prod_left

theorem integral_priorWeight {T : ℕ} (w : X → Theta → ℝ)
    (hw : Measurable (fun z : X × Theta => w z.1 z.2)) (hpos : ∀ x theta, 0 < w x theta)
    (hi : ∀ theta, Integrable (fun x => w x theta) mu)
    (hnormal : ∀ theta, (∫ x, w x theta ∂mu) = 1) :
    (∫ sample : Fin T → X, priorWeight prior w sample ∂Measure.pi (fun _ : Fin T => mu)) = 1 := by
  have hJoint := integrable_productWeight_joint mu prior (T := T) w hw hpos hi hnormal
  unfold priorWeight
  rw [integral_integral_swap hJoint]
  simp_rw [integral_productWeight_sample mu w hnormal]
  simp

theorem exp_sum_logWeight {T : ℕ} (w : X → Theta → ℝ) (hpos : ∀ x theta, 0 < w x theta)
    (sample : Fin T → X) (theta : Theta) :
    Real.exp (∑ i, Real.log (w (sample i) theta)) = productWeight w sample theta := by
  rw [Real.exp_sum]
  unfold productWeight
  apply Finset.prod_congr rfl
  intro i _
  exact Real.exp_log (hpos _ _)

/-- One common random prior weight controls every posterior. Its expectation
is one, so this form avoids any measurability choice of a maximizing posterior. -/
theorem posterior_logWeight_le {T : ℕ} (w : X → Theta → ℝ) (hpos : ∀ x theta, 0 < w x theta)
    (sample : Fin T → X) (posterior : Measure Theta) [IsProbabilityMeasure posterior]
    (hKL : klDiv posterior prior ≠ ⊤)
    (hlog : ∀ i, Integrable (fun theta => Real.log (w (sample i) theta)) posterior)
    (hWeight : Integrable (productWeight w sample) prior) :
    (∑ i, ∫ theta, Real.log (w (sample i) theta) ∂posterior) ≤
      (klDiv posterior prior).toReal + priorWeight prior w sample := by
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hlog i)
  have hexp : Integrable (fun theta => Real.exp (∑ i, Real.log (w (sample i) theta))) prior := by
    simpa only [exp_sum_logWeight w hpos] using hWeight
  have h := TomographyOracleCore.integral_le_toReal_klDiv_add_log_integral_exp
    posterior prior (fun theta => ∑ i, Real.log (w (sample i) theta)) hsum hexp hKL
  rw [integral_finsetSum Finset.univ (fun i _ => hlog i)] at h
  simp only [exp_sum_logWeight w hpos] at h
  apply h.trans
  apply add_le_add le_rfl
  exact Real.log_le_self (integral_nonneg fun theta => (productWeight_pos w hpos sample theta).le)

end
end TomographyOracleCore.Revision.ProductPriorWeights
