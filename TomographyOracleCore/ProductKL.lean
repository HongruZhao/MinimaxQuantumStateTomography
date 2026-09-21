import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.MeasureTheory.Measure.Prod

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-!
# KL divergence of independent product measures

Mathlib supplies the KL chain rule for composition-products.  This module
derives the ordinary two-factor product identity and records invariance under
measurable equivalences, which are the ingredients needed for finite-copy
tensorization in the physical lower bound.
-/

/-- KL divergence is invariant under a measurable equivalence. -/
theorem klDiv_map_measurableEquiv
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (mu nu : Measure Alpha) [IsFiniteMeasure mu] [IsFiniteMeasure nu]
    (e : Alpha ≃ᵐ Beta) :
    klDiv (mu.map e) (nu.map e) = klDiv mu nu := by
  apply le_antisymm
  · exact klDiv_map_le mu nu e.measurable
  · calc
      klDiv mu nu =
          klDiv ((mu.map e).map e.symm) ((nu.map e).map e.symm) := by
            simp
      _ ≤ klDiv (mu.map e) (nu.map e) :=
        klDiv_map_le (mu.map e) (nu.map e) e.symm.measurable

/-- KL divergence of independent products is the sum of the component KL
divergences. -/
theorem klDiv_prod_eq_add
    {Alpha Beta : Type*} [MeasurableSpace Alpha] [MeasurableSpace Beta]
    (mu nu : Measure Alpha) (mu' nu' : Measure Beta)
    [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    [IsProbabilityMeasure mu'] [IsProbabilityMeasure nu'] :
    klDiv (mu.prod mu') (nu.prod nu') =
      klDiv mu nu + klDiv mu' nu' := by
  let kappa : Kernel Alpha Beta := Kernel.const Alpha mu'
  let eta : Kernel Alpha Beta := Kernel.const Alpha nu'
  have hsecond : klDiv (mu.prod mu') (mu.prod nu') = klDiv mu' nu' := by
    calc
      klDiv (mu.prod mu') (mu.prod nu') =
          klDiv ((mu.prod mu').map MeasurableEquiv.prodComm)
            ((mu.prod nu').map MeasurableEquiv.prodComm) :=
        (klDiv_map_measurableEquiv (mu.prod mu') (mu.prod nu')
          MeasurableEquiv.prodComm).symm
      _ = klDiv (mu'.prod mu) (nu'.prod mu) := by
        change klDiv ((mu.prod mu').map Prod.swap)
          ((mu.prod nu').map Prod.swap) = _
        rw [Measure.prod_swap, Measure.prod_swap]
      _ = klDiv
          (mu' ⊗ₘ (Kernel.const Beta mu))
          (nu' ⊗ₘ (Kernel.const Beta mu)) := by
        rw [Measure.compProd_const, Measure.compProd_const]
      _ = klDiv mu' nu' :=
        klDiv_compProd_left mu' nu' (Kernel.const Beta mu)
  calc
    klDiv (mu.prod mu') (nu.prod nu') =
        klDiv (mu ⊗ₘ kappa) (nu ⊗ₘ eta) := by
      simp [kappa, eta]
    _ = klDiv mu nu + klDiv (mu ⊗ₘ kappa) (mu ⊗ₘ eta) :=
      klDiv_compProd_eq_add mu nu kappa eta
    _ = klDiv mu nu + klDiv (mu.prod mu') (mu.prod nu') := by
      simp [kappa, eta]
    _ = klDiv mu nu + klDiv mu' nu' := by rw [hsecond]

end TomographyOracleCore
