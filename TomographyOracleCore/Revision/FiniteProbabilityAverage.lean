import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace TomographyOracleCore.Revision.FiniteProbabilityAverage

open scoped BigOperators
noncomputable section

/-- A literal finite list of nonnegative probability weights. -/
structure Law (Ω : Type*) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ x, 0 ≤ weight x
  total : ∑ x, weight x = 1

variable {Ω : Type*} [Fintype Ω]

def average (P : Law Ω) (f : Ω → ℝ) : ℝ := ∑ x, P.weight x * f x

@[simp] theorem average_const (P : Law Ω) (c : ℝ) : average P (fun _ => c) = c := by
  rw [average, ← Finset.sum_mul, P.total, one_mul]

@[simp] theorem average_add (P : Law Ω) (f g : Ω → ℝ) :
    average P (fun x => f x + g x) = average P f + average P g := by
  simp only [average, mul_add, Finset.sum_add_distrib]

@[simp] theorem average_sub (P : Law Ω) (f g : Ω → ℝ) :
    average P (fun x => f x - g x) = average P f - average P g := by
  simp only [average, mul_sub, Finset.sum_sub_distrib]

@[simp] theorem average_const_mul (P : Law Ω) (c : ℝ) (f : Ω → ℝ) :
    average P (fun x => c * f x) = c * average P f := by
  simp only [average, Finset.mul_sum]
  congr 1
  funext x
  ring

@[simp] theorem average_mul_const (P : Law Ω) (f : Ω → ℝ) (c : ℝ) :
    average P (fun x => f x * c) = average P f * c := by
  simp only [average, ← mul_assoc, Finset.sum_mul]

theorem average_nonneg (P : Law Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ average P f := Finset.sum_nonneg fun x _ => mul_nonneg (P.nonneg x) (hf x)

theorem average_mono (P : Law Ω) {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) :
    average P f ≤ average P g :=
  Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (P.nonneg x)

theorem average_congr (P : Law Ω) {f g : Ω → ℝ} (h : ∀ x, f x = g x) :
    average P f = average P g := congrArg (average P) (funext h)

theorem average_sum {ι : Type*} [Fintype ι] (P : Law Ω) (f : ι → Ω → ℝ) :
    average P (fun x => ∑ i, f i x) = ∑ i, average P (f i) := by
  simp only [average, Finset.mul_sum]
  exact Finset.sum_comm

/-- Cauchy--Schwarz for a finite weighted average, proved from positivity
of a quadratic polynomial. -/
theorem average_mul_sq_le (P : Law Ω) (f g : Ω → ℝ) :
    average P (fun x => f x * g x) ^ 2 ≤
      average P (fun x => f x ^ 2) * average P (fun x => g x ^ 2) := by
  let a := average P (fun x => f x ^ 2)
  let b := average P (fun x => f x * g x)
  let c := average P (fun x => g x ^ 2)
  have ha : 0 ≤ a := average_nonneg P fun _ => sq_nonneg _
  have hc : 0 ≤ c := average_nonneg P fun _ => sq_nonneg _
  have hquad (t : ℝ) : 0 ≤ a - 2 * t * b + t ^ 2 * c := by
    have h := average_nonneg P (fun x => sq_nonneg (f x - t * g x))
    have heq : average P (fun x => (f x - t * g x) ^ 2) =
        a - 2 * t * b + t ^ 2 * c := by
      calc
        _ = average P (fun x => f x ^ 2 - (2 * t) * (f x * g x) + t ^ 2 * g x ^ 2) :=
          average_congr P fun _ => by ring
        _ = _ := by simp only [average_add, average_sub, average_const_mul, a, b, c]
    rwa [heq] at h
  change b ^ 2 ≤ a * c
  by_cases hc0 : c = 0
  · have hz := hquad ((a + 1) / (2 * b))
    by_cases hb : b = 0
    · simp [hb, hc0]
    have heq : a - 2 * ((a + 1) / (2 * b)) * b + ((a + 1) / (2 * b)) ^ 2 * c = -1 := by
      rw [hc0]
      field_simp
      ring
    rw [heq] at hz
    linarith
  · have h := mul_nonneg (hquad (b / c)) hc
    field_simp at h
    nlinarith

def probability (P : Law Ω) (s : Set Ω) : ℝ := average P (s.indicator fun _ => 1)

theorem probability_nonneg (P : Law Ω) (s : Set Ω) : 0 ≤ probability P s := by
  apply average_nonneg
  intro x
  classical
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

theorem probability_le_one (P : Law Ω) (s : Set Ω) : probability P s ≤ 1 := by
  rw [← average_const P 1]
  apply average_mono
  intro x
  classical
  by_cases hx : x ∈ s <;> simp [Set.indicator, hx]

theorem probability_mono (P : Law Ω) {s t : Set Ω} (h : s ⊆ t) :
    probability P s ≤ probability P t := by
  apply average_mono
  intro x
  classical
  by_cases hx : x ∈ s
  · simp [Set.indicator_of_mem hx, Set.indicator_of_mem (h hx)]
  · by_cases ht : x ∈ t <;> simp [Set.indicator, hx, ht]

theorem probability_sub_le_diff (P : Law Ω) (s t : Set Ω) :
    probability P s - probability P t ≤ probability P (s \ t) := by
  rw [probability, probability, ← average_sub]
  apply average_mono
  intro x
  classical
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> simp [Set.indicator, hs, ht]

/-- The elementary second/fourth-moment small-ball bound. -/
theorem probability_sq_ge_half_average_sq (P : Law Ω) (f : Ω → ℝ) :
    average P (fun x => f x ^ 2) ^ 2 ≤
      4 * average P (fun x => f x ^ 4) *
        probability P {x | average P (fun y => f y ^ 2) / 2 ≤ f x ^ 2} := by
  classical
  let a := average P (fun x => f x ^ 2)
  let s := {x | a / 2 ≤ f x ^ 2}
  let g : Ω → ℝ := s.indicator fun _ => 1
  have ha : 0 ≤ a := average_nonneg P fun _ => sq_nonneg _
  have hsplit : a / 2 ≤ average P (fun x => f x ^ 2 * g x) := by
    have hpoint : ∀ x, f x ^ 2 ≤ f x ^ 2 * g x + a / 2 := by
      intro x
      by_cases hx : x ∈ s
      · simp only [g, Set.indicator_of_mem hx, mul_one]
        linarith
      · have hx' : f x ^ 2 < a / 2 := not_le.mp hx
        simp only [g, Set.indicator_of_notMem hx, mul_zero, zero_add]
        exact hx'.le
    have h := average_mono P hpoint
    rw [average_add, average_const] at h
    change a ≤ _ at h
    linarith
  have hcs := average_mul_sq_le P (fun x => f x ^ 2) g
  have hg : average P (fun x => g x ^ 2) = probability P s := by
    apply average_congr
    intro x
    by_cases hx : x ∈ s <;> simp [g, Set.indicator, hx]
  have hf : average P (fun x => (f x ^ 2) ^ 2) = average P (fun x => f x ^ 4) :=
    average_congr P fun _ => by ring
  rw [hg, hf] at hcs
  change a ^ 2 ≤ _
  nlinarith

theorem markov (P : Law Ω) {f : Ω → ℝ} (hf : ∀ x, 0 ≤ f x) {a : ℝ} (ha : 0 ≤ a) :
    a * probability P {x | a < f x} ≤ average P f := by
  rw [probability, ← average_const_mul]
  apply average_mono
  intro x
  classical
  by_cases hx : a < f x
  · simpa [Set.indicator, hx] using hx.le
  · simpa [Set.indicator, hx] using hf x

theorem exists_average_le [Nonempty Ω] (P : Law Ω) (f : Ω → ℝ) :
    ∃ x, average P f ≤ f x := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  refine ⟨x, ?_⟩
  rw [← average_const P (f x)]
  exact average_mono P fun y => hmax y (Finset.mem_univ y)

end
end TomographyOracleCore.Revision.FiniteProbabilityAverage
