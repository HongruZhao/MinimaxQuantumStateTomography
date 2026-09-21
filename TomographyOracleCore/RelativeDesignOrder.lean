import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

namespace TomographyOracleCore

open scoped CStarAlgebra

/-!
# Relative completely-positive order

This is the order relation used in the definition of a relative (or
multiplicative-error) unitary design.  It is stated for arbitrary linear maps
between non-unital C-star algebras, so a later concrete moment-twirl
construction can instantiate it without changing the theorem interface.
-/

section CPOrder

variable {A₁ A₂ : Type*}
  [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂]

/-- Completely-positive order on complex-linear maps: `Φ ≤CP Ψ` means
that the difference `Ψ - Φ` is a completely positive map. -/
def CompletelyPositiveLE (Φ Ψ : A₁ →ₗ[ℂ] A₂) : Prop :=
  ∃ Δ : A₁ →CP A₂, Δ.toLinearMap = Ψ - Φ

/-- Completely-positive order implies ordinary order after applying the maps
to a positive element. -/
theorem CompletelyPositiveLE.apply_le
    {Φ Ψ : A₁ →ₗ[ℂ] A₂} (h : CompletelyPositiveLE Φ Ψ)
    {x : A₁} (hx : 0 ≤ x) : Φ x ≤ Ψ x := by
  obtain ⟨Δ, hΔ⟩ := h
  have hnonneg : 0 ≤ Δ x := map_nonneg Δ hx
  have happly : Δ x = Ψ x - Φ x := by
    exact LinearMap.congr_fun hΔ x
  rw [happly] at hnonneg
  exact sub_nonneg.mp hnonneg

/-- Reflexivity of completely-positive order. -/
theorem CompletelyPositiveLE.refl (Φ : A₁ →ₗ[ℂ] A₂) :
    CompletelyPositiveLE Φ Φ := by
  let zeroCP : A₁ →CP A₂ :=
    { toLinearMap := 0
      map_cstarMatrix_nonneg' := by
        intro k M hM
        have hz : M.map (0 : A₁ →ₗ[ℂ] A₂) = 0 := by
          ext i j
          rfl
        rw [hz] }
  refine ⟨zeroCP, ?_⟩
  change (0 : A₁ →ₗ[ℂ] A₂) = Φ - Φ
  simp

/-- The sum of two completely positive maps. -/
def CompletelyPositiveMap.add
    (Φ Ψ : A₁ →CP A₂) : A₁ →CP A₂ :=
  { toLinearMap := Φ.toLinearMap + Ψ.toLinearMap
    map_cstarMatrix_nonneg' := by
      intro k M hM
      have hadd : M.map (Φ.toLinearMap + Ψ.toLinearMap) =
          M.map Φ.toLinearMap + M.map Ψ.toLinearMap := by
        ext i j
        rfl
      rw [hadd]
      exact add_nonneg (Φ.map_cstarMatrix_nonneg' k M hM)
        (Ψ.map_cstarMatrix_nonneg' k M hM) }

@[simp] theorem CompletelyPositiveMap.add_toLinearMap
    (Φ Ψ : A₁ →CP A₂) :
    (CompletelyPositiveMap.add Φ Ψ).toLinearMap =
      Φ.toLinearMap + Ψ.toLinearMap := rfl

/-- Transitivity of completely-positive order. -/
theorem CompletelyPositiveLE.trans
    {Φ Ψ Θ : A₁ →ₗ[ℂ] A₂}
    (hΦΨ : CompletelyPositiveLE Φ Ψ)
    (hΨΘ : CompletelyPositiveLE Ψ Θ) :
    CompletelyPositiveLE Φ Θ := by
  obtain ⟨Δ₁, hΔ₁⟩ := hΦΨ
  obtain ⟨Δ₂, hΔ₂⟩ := hΨΘ
  refine ⟨CompletelyPositiveMap.add Δ₁ Δ₂, ?_⟩
  rw [CompletelyPositiveMap.add_toLinearMap, hΔ₁, hΔ₂]
  module

end CPOrder

section RelativeOrder

variable {A : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- Relative (multiplicative-error) completely-positive approximation.

This is the literal order
`(1-ε) Φ_H ≤CP Φ_E ≤CP (1+ε) Φ_H` used for approximate
unitary designs. -/
def RelativeCPApproximation (epsilon : ℝ)
    (ensemble haar : A →ₗ[ℂ] A) : Prop :=
  CompletelyPositiveLE
      (((1 - epsilon : ℝ) : ℂ) • haar) ensemble ∧
    CompletelyPositiveLE ensemble
      (((1 + epsilon : ℝ) : ℂ) • haar)

theorem RelativeCPApproximation.lower
    {epsilon : ℝ} {ensemble haar : A →ₗ[ℂ] A}
    (h : RelativeCPApproximation epsilon ensemble haar) :
    CompletelyPositiveLE (((1 - epsilon : ℝ) : ℂ) • haar) ensemble :=
  h.1

theorem RelativeCPApproximation.upper
    {epsilon : ℝ} {ensemble haar : A →ₗ[ℂ] A}
    (h : RelativeCPApproximation epsilon ensemble haar) :
    CompletelyPositiveLE ensemble (((1 + epsilon : ℝ) : ℂ) • haar) :=
  h.2

/-- Upper pointwise consequence on every positive input. -/
theorem RelativeCPApproximation.apply_le_upper
    {epsilon : ℝ} {ensemble haar : A →ₗ[ℂ] A}
    (h : RelativeCPApproximation epsilon ensemble haar)
    {x : A} (hx : 0 ≤ x) :
    ensemble x ≤ (((1 + epsilon : ℝ) : ℂ) • haar) x :=
  h.upper.apply_le hx

/-- Lower pointwise consequence on every positive input. -/
theorem RelativeCPApproximation.lower_apply_le
    {epsilon : ℝ} {ensemble haar : A →ₗ[ℂ] A}
    (h : RelativeCPApproximation epsilon ensemble haar)
    {x : A} (hx : 0 ≤ x) :
    (((1 - epsilon : ℝ) : ℂ) • haar) x ≤ ensemble x :=
  h.lower.apply_le hx

end RelativeOrder

end TomographyOracleCore
