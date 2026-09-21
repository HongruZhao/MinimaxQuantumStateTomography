import TomographyOracleCore.ProductKL
import Mathlib.MeasureTheory.Constructions.Pi

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open scoped BigOperators ENNReal

/-!
# KL tensorization for finite independent products

The KL divergence between two finite product probability laws is the sum of
the one-coordinate divergences.  The proof splits off one coordinate through
Mathlib's measurable `Fin` product equivalence and iterates the two-factor
identity from `ProductKL`.
-/

/-- Any two probability measures on a subsingleton measurable space agree. -/
theorem probabilityMeasure_eq_of_subsingleton
    {Alpha : Type*} [MeasurableSpace Alpha] [Subsingleton Alpha]
    (mu nu : Measure Alpha) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] :
    mu = nu := by
  ext s hs
  by_cases hsempty : s = ∅
  · simp [hsempty]
  · have hsnonempty : s.Nonempty := Set.nonempty_iff_ne_empty.mpr hsempty
    have hsuniv : s = Set.univ := Subsingleton.eq_univ_of_nonempty hsnonempty
    simp [hsuniv]

/-- Exact KL tensorization over a finite vector of independent probability
measures. -/
theorem klDiv_pi_fin_eq_sum
    {Outcome : Type*} [MeasurableSpace Outcome]
    (n : ℕ) (mu nu : Fin n → Measure Outcome)
    [∀ i, IsProbabilityMeasure (mu i)]
    [∀ i, IsProbabilityMeasure (nu i)] :
    klDiv (Measure.pi mu) (Measure.pi nu) =
      ∑ i, klDiv (mu i) (nu i) := by
  induction n with
  | zero =>
      have hmeasure : Measure.pi mu = Measure.pi nu :=
        probabilityMeasure_eq_of_subsingleton _ _
      rw [hmeasure, klDiv_self]
      simp
  | succ n ih =>
      let first : Fin (n + 1) := 0
      let muTail : Fin n → Measure Outcome :=
        fun j ↦ mu (first.succAbove j)
      let nuTail : Fin n → Measure Outcome :=
        fun j ↦ nu (first.succAbove j)
      let e : (Fin (n + 1) → Outcome) ≃ᵐ
          Outcome × (Fin n → Outcome) :=
        MeasurableEquiv.piFinSuccAbove (fun _ ↦ Outcome) first
      have hmuMap : (Measure.pi mu).map e =
          (mu first).prod (Measure.pi muTail) := by
        exact (measurePreserving_piFinSuccAbove mu first).map_eq
      have hnuMap : (Measure.pi nu).map e =
          (nu first).prod (Measure.pi nuTail) := by
        exact (measurePreserving_piFinSuccAbove nu first).map_eq
      calc
        klDiv (Measure.pi mu) (Measure.pi nu) =
            klDiv ((Measure.pi mu).map e) ((Measure.pi nu).map e) :=
          (klDiv_map_measurableEquiv (Measure.pi mu) (Measure.pi nu) e).symm
        _ = klDiv ((mu first).prod (Measure.pi muTail))
            ((nu first).prod (Measure.pi nuTail)) := by
          rw [hmuMap, hnuMap]
        _ = klDiv (mu first) (nu first) +
            klDiv (Measure.pi muTail) (Measure.pi nuTail) :=
          klDiv_prod_eq_add (mu first) (nu first)
            (Measure.pi muTail) (Measure.pi nuTail)
        _ = klDiv (mu first) (nu first) +
            ∑ j, klDiv (muTail j) (nuTail j) := by
          rw [ih muTail nuTail]
        _ = ∑ i, klDiv (mu i) (nu i) := by
          rw [Fin.sum_univ_succAbove (fun i ↦ klDiv (mu i) (nu i)) first]

end TomographyOracleCore
