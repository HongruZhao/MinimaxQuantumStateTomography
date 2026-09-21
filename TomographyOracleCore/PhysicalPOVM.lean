import TomographyOracleCore.MatrixReduction

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction
open scoped ComplexOrder

/-!
# Physical one-copy POVMs and randomized nonadaptive designs

This module fixes the semantic data used by the physical tomography model.
A finite-dimensional POVM is represented in the dominated form used in the
paper: a scalar measure together with an almost-everywhere positive effect
density whose integral is the identity.  Its Born laws form a Markov kernel
from density operators to the standard-Borel outcome space.

A randomized nonadaptive `T`-copy design first draws a public seed from a law
that is independent of the state.  The seed selects all `T` one-copy POVMs.
Conditional on the state and seed, the outcome law is the finite product of
their Born laws.  None of the structures below contains an oracle, risk, upper
bound, lower bound, or minimax conclusion.
-/

namespace PhysicalPOVM

/-! ## Measurable density operators -/

/-- Flatten the matrix of a density operator into its finite family of
complex coordinates.  Unlike a bare `Matrix`, this function type carries
Mathlib's coordinatewise measurable structure. -/
def densityCoordinates (D : ℕ) :
    DensityOperator (Fin D) → (Fin D × Fin D → ℂ) :=
  fun ρ p ↦ ρ.matrix p.1 p.2

/-- The canonical measurable structure on density operators is pulled back
from all of their complex matrix coordinates. -/
noncomputable instance densityOperatorMeasurableSpace (D : ℕ) :
    MeasurableSpace (DensityOperator (Fin D)) :=
  MeasurableSpace.comap (densityCoordinates D) inferInstance

/-- The complete coordinate family is measurable by construction. -/
theorem measurable_densityCoordinates (D : ℕ) :
    Measurable (densityCoordinates D) :=
  measurable_iff_comap_le.mpr le_rfl

/-- Every matrix entry of a density operator is measurable. -/
theorem measurable_densityOperator_apply (D : ℕ) (i j : Fin D) :
    Measurable (fun ρ : DensityOperator (Fin D) ↦ ρ.matrix i j) := by
  exact (measurable_pi_apply (i, j)).comp (measurable_densityCoordinates D)

/-! ## Dominated POVMs and Born kernels -/

/-- The nonnegative scalar Born density associated with an effect density.
The separate validity fields in `DominatedPOVM` record that the real trace
used here is nonnegative almost everywhere and integrates to one. -/
noncomputable def bornDensityFrom
    {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome]
    (effect : Outcome → Matrix (Fin D) (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) (z : Outcome) : ENNReal :=
  ENNReal.ofReal ((Matrix.trace (ρ.matrix * effect z)).re)

/-- The Born measure obtained by weighting the dominating scalar measure by
the scalar Born density. -/
noncomputable def bornMeasureFrom
    {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome]
    (base : Measure Outcome)
    (effect : Outcome → Matrix (Fin D) (Fin D) ℂ)
    (ρ : DensityOperator (Fin D)) : Measure Outcome :=
  base.withDensity (bornDensityFrom effect ρ)

/-- A finite-dimensional POVM on a standard-Borel outcome space, expressed
through its trace-dominating scalar measure and normalized effect density.

The final two fields are semantic validity certificates: the Born measures
vary measurably with the state and are probability measures.  They make the
associated `Kernel` usable without postulating any statistical conclusion.
-/
structure DominatedPOVM
    (D : ℕ) (Outcome : Type*) [MeasurableSpace Outcome]
    [StandardBorelSpace Outcome] where
  dimension_pos : 0 < D
  base : Measure Outcome
  base_finite : IsFiniteMeasure base
  effect : Outcome → Matrix (Fin D) (Fin D) ℂ
  effect_measurable : ∀ i j, Measurable fun z ↦ effect z i j
  effect_integrable : ∀ i j, Integrable (fun z ↦ effect z i j) base
  effect_ae_posSemidef : ∀ᵐ z ∂base, (effect z).PosSemidef
  effect_ae_trace_one : ∀ᵐ z ∂base, Matrix.trace (effect z) = 1
  integral_effect_eq_one : ∀ i j,
    ∫ z, effect z i j ∂base = if i = j then 1 else 0
  born_density_ae_nonnegative :
    ∀ ρ : DensityOperator (Fin D),
      ∀ᵐ z ∂base, 0 ≤ (Matrix.trace (ρ.matrix * effect z)).re
  born_measurable : Measurable (bornMeasureFrom base effect)
  born_probability :
    ∀ ρ : DensityOperator (Fin D),
      IsProbabilityMeasure (bornMeasureFrom base effect ρ)

namespace DominatedPOVM

variable {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome]
  [StandardBorelSpace Outcome]

/-- The Born probability measure of a dominated POVM at a state. -/
noncomputable def bornMeasure
    (M : DominatedPOVM D Outcome) (ρ : DensityOperator (Fin D)) :
    Measure Outcome :=
  bornMeasureFrom M.base M.effect ρ

/-- The Born laws of a dominated POVM as a probability kernel in the state. -/
noncomputable def bornKernel (M : DominatedPOVM D Outcome) :
    Kernel (DensityOperator (Fin D)) Outcome where
  toFun := bornMeasureFrom M.base M.effect
  measurable' := M.born_measurable

@[simp]
theorem bornKernel_apply
    (M : DominatedPOVM D Outcome) (ρ : DensityOperator (Fin D)) :
    M.bornKernel ρ = M.bornMeasure ρ :=
  rfl

instance bornKernel_isMarkov (M : DominatedPOVM D Outcome) :
    IsMarkovKernel M.bornKernel where
  isProbabilityMeasure := M.born_probability

end DominatedPOVM

/-! ## Public-seed randomized nonadaptive designs -/

/-- A randomized nonadaptive `T`-copy single-copy design.

The public seed law is independent of the unknown state.  A function of the
seed alone selects every one-copy POVM, so no measurement can depend on an
earlier outcome.  `outcomes_eq_pi` states conditional independence given the
state and public seed.  The common `Outcome` type is intended to be a
universal standard-Borel coding space.
-/
structure RandomizedNonadaptiveDesign
    (D T : ℕ) (Seed Outcome : Type*)
    [MeasurableSpace Seed] [StandardBorelSpace Seed]
    [MeasurableSpace Outcome] [StandardBorelSpace Outcome] where
  dimension_pos : 0 < D
  seed : Measure Seed
  seed_probability : IsProbabilityMeasure seed
  measurement : Fin T → Seed → DominatedPOVM D Outcome
  shot_measurable : ∀ t : Fin T,
    Measurable fun p : DensityOperator (Fin D) × Seed ↦
      (measurement t p.2).bornMeasure p.1
  outcomes :
    Kernel (DensityOperator (Fin D) × Seed) (Fin T → Outcome)
  outcomes_markov : IsMarkovKernel outcomes
  outcomes_eq_pi : ∀ p : DensityOperator (Fin D) × Seed,
    outcomes p = Measure.pi fun t : Fin T ↦
      (measurement t p.2).bornMeasure p.1

namespace RandomizedNonadaptiveDesign

variable {D T : ℕ} {Seed Outcome : Type*}
  [MeasurableSpace Seed] [StandardBorelSpace Seed]
  [MeasurableSpace Outcome] [StandardBorelSpace Outcome]

/-- The public seed kernel is constant in the state, hence independent of it. -/
noncomputable def seedKernel
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) :
    Kernel (DensityOperator (Fin D)) Seed :=
  Kernel.const (DensityOperator (Fin D)) d.seed

@[simp]
theorem seedKernel_apply
    (d : RandomizedNonadaptiveDesign D T Seed Outcome)
    (ρ : DensityOperator (Fin D)) :
    d.seedKernel ρ = d.seed :=
  rfl

instance seedKernel_isMarkov
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) :
    IsMarkovKernel d.seedKernel where
  isProbabilityMeasure ρ := by
    simpa [seedKernel] using d.seed_probability

/-- The `t`th one-copy Born kernel after the state and public seed are known. -/
noncomputable def shotKernel
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) (t : Fin T) :
    Kernel (DensityOperator (Fin D) × Seed) Outcome where
  toFun := fun p ↦ (d.measurement t p.2).bornMeasure p.1
  measurable' := d.shot_measurable t

@[simp]
theorem shotKernel_apply
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) (t : Fin T)
    (p : DensityOperator (Fin D) × Seed) :
    d.shotKernel t p = (d.measurement t p.2).bornMeasure p.1 :=
  rfl

instance shotKernel_isMarkov
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) (t : Fin T) :
    IsMarkovKernel (d.shotKernel t) where
  isProbabilityMeasure p := by
    simpa [shotKernel, DominatedPOVM.bornMeasure] using
      (d.measurement t p.2).born_probability p.1

instance outcomes_isMarkov
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) :
    IsMarkovKernel d.outcomes :=
  d.outcomes_markov

/-- The full experiment first draws the state-independent public seed and
then draws the conditionally product outcome vector. -/
noncomputable def experimentKernel
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) :
    Kernel (DensityOperator (Fin D)) (Seed × (Fin T → Outcome)) :=
  Kernel.compProd d.seedKernel d.outcomes

instance experimentKernel_isMarkov
    (d : RandomizedNonadaptiveDesign D T Seed Outcome) :
    IsMarkovKernel d.experimentKernel := by
  unfold experimentKernel
  infer_instance

end RandomizedNonadaptiveDesign

end PhysicalPOVM

end TomographyOracleCore
