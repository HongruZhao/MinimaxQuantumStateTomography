import TomographyOracleCore.Revision.ProductPriorWeights
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

namespace TomographyOracleCore.Revision.NormalizedPositiveWeights

open MeasureTheory
noncomputable section

variable {X Theta : Type*} [MeasurableSpace X] [MeasurableSpace Theta]
    (mu : Measure X) [IsProbabilityMeasure mu]

def normalizer (k : X → Theta → ℝ) (theta : Theta) : ℝ := ∫ x, k x theta ∂mu
def normalizedWeight (k : X → Theta → ℝ) (x : X) (theta : Theta) : ℝ :=
  k x theta / normalizer mu k theta

theorem normalizer_lower (k : X → Theta → ℝ)
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (theta : Theta) :
    (3 / 4 : ℝ) ≤ normalizer mu k theta := by
  have h := integral_mono (integrable_const (3 / 4 : ℝ)) (hi theta) (fun x => hk x theta)
  simpa only [integral_const, probReal_univ, one_smul, normalizer] using h

theorem normalizer_pos (k : X → Theta → ℝ)
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (theta : Theta) :
    0 < normalizer mu k theta := lt_of_lt_of_le (by norm_num) (normalizer_lower mu k hk hi theta)

theorem measurable_normalizer (k : X → Theta → ℝ)
    (hk : Measurable (fun z : X × Theta => k z.1 z.2)) : Measurable (normalizer mu k) :=
  hk.stronglyMeasurable.integral_prod_left'.measurable

theorem measurable_normalizedWeight (k : X → Theta → ℝ)
    (hk : Measurable (fun z : X × Theta => k z.1 z.2)) :
    Measurable (fun z : X × Theta => normalizedWeight mu k z.1 z.2) :=
  hk.div ((measurable_normalizer mu k hk).comp measurable_snd)

theorem normalizedWeight_pos (k : X → Theta → ℝ)
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (x : X) (theta : Theta) :
    0 < normalizedWeight mu k x theta :=
  div_pos (lt_of_lt_of_le (by norm_num) (hk x theta)) (normalizer_pos mu k hk hi theta)

theorem integrable_normalizedWeight (k : X → Theta → ℝ)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (theta : Theta) :
    Integrable (fun x => normalizedWeight mu k x theta) mu := (hi theta).div_const _

theorem integral_normalizedWeight (k : X → Theta → ℝ)
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (theta : Theta) :
    (∫ x, normalizedWeight mu k x theta ∂mu) = 1 := by
  unfold normalizedWeight
  rw [integral_div]
  exact div_self (normalizer_pos mu k hk hi theta).ne'

theorem log_normalizer_lower (k : X → Theta → ℝ)
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (theta : Theta) :
    -1 ≤ Real.log (normalizer mu k theta) := by
  have hp := normalizer_pos mu k hk hi theta
  have h := Real.one_sub_inv_le_log_of_pos hp
  have hi' := one_div_le_one_div_of_le (show (0 : ℝ) < 3 / 4 by norm_num)
    (normalizer_lower mu k hk hi theta)
  norm_num [one_div] at hi'
  linarith

theorem integrable_log_normalizer (prior : Measure Theta) [IsProbabilityMeasure prior]
    (k : X → Theta → ℝ) (hm : Measurable (fun z : X × Theta => k z.1 z.2))
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu)
    (hjoint : Integrable (fun z : X × Theta => k z.1 z.2) (mu.prod prior)) :
    Integrable (fun theta => Real.log (normalizer mu k theta)) prior := by
  have hn : Integrable (normalizer mu k) prior := hjoint.integral_prod_right
  apply ((integrable_const (1 : ℝ)).add hn.norm).mono'
    ((measurable_normalizer mu k hm).log.aestronglyMeasurable)
  filter_upwards [] with theta
  simp only [Pi.add_apply, Real.norm_eq_abs]
  apply abs_le.2
  have hlo := log_normalizer_lower mu k hk hi theta
  have hup := Real.log_le_sub_one_of_pos (normalizer_pos mu k hk hi theta)
  constructor <;> linarith [abs_nonneg (normalizer mu k theta), le_abs_self (normalizer mu k theta)]

theorem integral_log_normalizer_le (prior : Measure Theta) [IsProbabilityMeasure prior]
    (k : X → Theta → ℝ) (hm : Measurable (fun z : X × Theta => k z.1 z.2))
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu)
    (hjoint : Integrable (fun z : X × Theta => k z.1 z.2) (mu.prod prior)) :
    (∫ theta, Real.log (normalizer mu k theta) ∂prior) ≤
      (∫ theta, normalizer mu k theta ∂prior) - 1 := by
  have hn : Integrable (normalizer mu k) prior := hjoint.integral_prod_right
  have h := integral_mono (integrable_log_normalizer mu prior k hm hk hi hjoint)
    (hn.sub (integrable_const (1 : ℝ)))
    (fun theta => Real.log_le_sub_one_of_pos (normalizer_pos mu k hk hi theta))
  simpa only [Pi.sub_apply, integral_sub hn (integrable_const (1 : ℝ)), integral_const,
    probReal_univ, one_smul] using h

theorem log_normalizedWeight (k : X → Theta → ℝ)
    (hk : ∀ x theta, (3 / 4 : ℝ) ≤ k x theta)
    (hi : ∀ theta, Integrable (fun x => k x theta) mu) (x : X) (theta : Theta) :
    Real.log (normalizedWeight mu k x theta) =
      Real.log (k x theta) - Real.log (normalizer mu k theta) :=
  Real.log_div (lt_of_lt_of_le (show (0 : ℝ) < 3 / 4 by norm_num) (hk x theta)).ne'
    (normalizer_pos mu k hk hi theta).ne'

end
end TomographyOracleCore.Revision.NormalizedPositiveWeights
