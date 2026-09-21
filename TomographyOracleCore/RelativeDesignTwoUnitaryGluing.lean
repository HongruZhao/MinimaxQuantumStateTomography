import TomographyOracleCore.RelativeDesignGluingIteration

namespace TomographyOracleCore

open scoped CStarAlgebra

/-!
# Algebraic two-unitary relative-CP gluing

This module proves the premise-free order algebra behind the first step of
Schuster--Haferkamp--Huang, Lemma 8.  Two local relative-CP sandwiches may be
composed because completely positive order is monotone under composition.
The resulting reference channel is the composition of the two local
reference channels.

The separate analytic content of that lemma is the comparison of this
composed local reference channel with the global Haar (or approximate-Haar)
twirl on overlapping subsystems.  No such comparison is asserted here.
-/

section CompletelyPositiveComposition

variable {A₁ A₂ A₃ : Type*}
  [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [NonUnitalCStarAlgebra A₃]
  [PartialOrder A₁] [PartialOrder A₂] [PartialOrder A₃]
  [StarOrderedRing A₁] [StarOrderedRing A₂] [StarOrderedRing A₃]

/-- Composition of completely positive maps is completely positive. -/
def CompletelyPositiveMap.comp
    (Φ : A₂ →CP A₃) (Ψ : A₁ →CP A₂) : A₁ →CP A₃ :=
  { toLinearMap := Φ.toLinearMap.comp Ψ.toLinearMap
    map_cstarMatrix_nonneg' := by
      intro k M hM
      have hΨ := Ψ.map_cstarMatrix_nonneg' k M hM
      have hΦ := Φ.map_cstarMatrix_nonneg' k
        (M.map Ψ.toLinearMap) hΨ
      have heq : (M.map Ψ.toLinearMap).map Φ.toLinearMap =
          M.map (Φ.toLinearMap.comp Ψ.toLinearMap) := by
        ext i j
        rfl
      rw [← heq]
      exact hΦ }

@[simp] theorem CompletelyPositiveMap.comp_toLinearMap
    (Φ : A₂ →CP A₃) (Ψ : A₁ →CP A₂) :
    (CompletelyPositiveMap.comp Φ Ψ).toLinearMap =
      Φ.toLinearMap.comp Ψ.toLinearMap := rfl

/-- Completely-positive order is monotone under simultaneous composition
of completely positive maps. -/
theorem CompletelyPositiveLE.comp_of_cp
    {Φ Ψ : A₂ →CP A₃} {Θ Ξ : A₁ →CP A₂}
    (hΦΨ : CompletelyPositiveLE Φ.toLinearMap Ψ.toLinearMap)
    (hΘΞ : CompletelyPositiveLE Θ.toLinearMap Ξ.toLinearMap) :
    CompletelyPositiveLE
      (CompletelyPositiveMap.comp Φ Θ).toLinearMap
      (CompletelyPositiveMap.comp Ψ Ξ).toLinearMap := by
  obtain ⟨Δ₁, hΔ₁⟩ := hΦΨ
  obtain ⟨Δ₂, hΔ₂⟩ := hΘΞ
  refine ⟨CompletelyPositiveMap.add
    (CompletelyPositiveMap.comp Δ₁ Ξ)
    (CompletelyPositiveMap.comp Φ Δ₂), ?_⟩
  simp only [CompletelyPositiveMap.add_toLinearMap,
    CompletelyPositiveMap.comp_toLinearMap]
  rw [hΔ₁, hΔ₂]
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub]
  abel

end CompletelyPositiveComposition

section CompletelyPositiveScaling

variable {A₁ A₂ : Type*}
  [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂]
  [StarOrderedRing A₁] [StarOrderedRing A₂]

/-- A nonnegative real multiple of a completely positive map is completely
positive. -/
def CompletelyPositiveMap.nonnegRealSMul
    (c : ℝ) (hc : 0 ≤ c) (Φ : A₁ →CP A₂) : A₁ →CP A₂ :=
  { toLinearMap := ((c : ℂ) • Φ.toLinearMap)
    map_cstarMatrix_nonneg' := by
      intro k M hM
      letI : IsScalarTower ℝ (CStarMatrix (Fin k) (Fin k) A₂)
          (CStarMatrix (Fin k) (Fin k) A₂) := ⟨by
        intro r X Y
        change (r • X) * Y = r • (X * Y)
        ext i j
        simp only [CStarMatrix.mul_apply, CStarMatrix.smul_apply,
          Finset.smul_sum, smul_mul_assoc]⟩
      letI : SMulCommClass ℝ (CStarMatrix (Fin k) (Fin k) A₂)
          (CStarMatrix (Fin k) (Fin k) A₂) := ⟨by
        intro r X Y
        simp only [smul_eq_mul]
        ext i j
        simp only [CStarMatrix.mul_apply, CStarMatrix.smul_apply,
          Finset.smul_sum, mul_smul_comm]⟩
      have hΦ := Φ.map_cstarMatrix_nonneg' k M hM
      have hscaled : 0 ≤ c • M.map Φ.toLinearMap :=
        smul_nonneg hc hΦ
      convert hscaled using 1
      ext i j
      rfl }

@[simp] theorem CompletelyPositiveMap.nonnegRealSMul_toLinearMap
    (c : ℝ) (hc : 0 ≤ c) (Φ : A₁ →CP A₂) :
    (CompletelyPositiveMap.nonnegRealSMul c hc Φ).toLinearMap =
      ((c : ℂ) • Φ.toLinearMap) := rfl

/-- Composition multiplies the two nonnegative real coefficients. -/
@[simp] theorem CompletelyPositiveMap.comp_nonnegRealSMul_toLinearMap
    (c d : ℝ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (Φ : A₂ →CP A₂) (Ψ : A₂ →CP A₂) :
    (CompletelyPositiveMap.comp
      (CompletelyPositiveMap.nonnegRealSMul c hc Φ)
      (CompletelyPositiveMap.nonnegRealSMul d hd Ψ)).toLinearMap =
        (((c * d : ℝ) : ℂ) •
          (CompletelyPositiveMap.comp Φ Ψ).toLinearMap) := by
  ext x
  simp [CompletelyPositiveMap.comp,
    CompletelyPositiveMap.nonnegRealSMul, mul_smul]

/-- Scalar monotonicity of CP order along a fixed completely positive map. -/
theorem CompletelyPositiveLE.real_smul_mono
    (Φ : A₁ →CP A₂) {a b : ℝ} (hab : a ≤ b) :
    CompletelyPositiveLE
      (((a : ℝ) : ℂ) • Φ.toLinearMap)
      (((b : ℝ) : ℂ) • Φ.toLinearMap) := by
  let Δ := CompletelyPositiveMap.nonnegRealSMul
    (b - a) (sub_nonneg.mpr hab) Φ
  refine ⟨Δ, ?_⟩
  simp only [Δ, CompletelyPositiveMap.nonnegRealSMul_toLinearMap]
  ext x
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  module

/-- Nonnegative real scaling preserves completely-positive order. -/
theorem CompletelyPositiveLE.real_smul
    {Φ Ψ : A₁ →ₗ[ℂ] A₂} (h : CompletelyPositiveLE Φ Ψ)
    (c : ℝ) (hc : 0 ≤ c) :
    CompletelyPositiveLE (((c : ℝ) : ℂ) • Φ)
      (((c : ℝ) : ℂ) • Ψ) := by
  obtain ⟨Δ, hΔ⟩ := h
  refine ⟨CompletelyPositiveMap.nonnegRealSMul c hc Δ, ?_⟩
  simp only [CompletelyPositiveMap.nonnegRealSMul_toLinearMap]
  rw [hΔ]
  ext x
  simp only [LinearMap.smul_apply, LinearMap.sub_apply]
  module

end CompletelyPositiveScaling

section RelativeComposition

variable {A : Type*} [NonUnitalCStarAlgebra A]
  [PartialOrder A] [StarOrderedRing A]

/-- Exact product sandwich obtained by composing two local relative-CP
approximations.  This is stronger than immediately replacing the two
one-sided products by a single symmetric error. -/
theorem relativeCPApproximation_comp_product_sandwich
    (E₁ H₁ E₂ H₂ : A →CP A) (ε₁ ε₂ : ℝ)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1)
    (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1)
    (h₁ : RelativeCPApproximation ε₁ E₁.toLinearMap H₁.toLinearMap)
    (h₂ : RelativeCPApproximation ε₂ E₂.toLinearMap H₂.toLinearMap) :
    CompletelyPositiveLE
        (((((1 - ε₁) * (1 - ε₂) : ℝ) : ℂ) •
          (CompletelyPositiveMap.comp H₁ H₂).toLinearMap))
        (CompletelyPositiveMap.comp E₁ E₂).toLinearMap ∧
      CompletelyPositiveLE
        (CompletelyPositiveMap.comp E₁ E₂).toLinearMap
        (((((1 + ε₁) * (1 + ε₂) : ℝ) : ℂ) •
          (CompletelyPositiveMap.comp H₁ H₂).toLinearMap)) := by
  let H₁lo := CompletelyPositiveMap.nonnegRealSMul
    (1 - ε₁) (sub_nonneg.mpr hε₁1) H₁
  let H₂lo := CompletelyPositiveMap.nonnegRealSMul
    (1 - ε₂) (sub_nonneg.mpr hε₂1) H₂
  let H₁hi := CompletelyPositiveMap.nonnegRealSMul
    (1 + ε₁) (by linarith) H₁
  let H₂hi := CompletelyPositiveMap.nonnegRealSMul
    (1 + ε₂) (by linarith) H₂
  have hlo₁ : CompletelyPositiveLE H₁lo.toLinearMap E₁.toLinearMap := by
    simpa [H₁lo] using h₁.lower
  have hlo₂ : CompletelyPositiveLE H₂lo.toLinearMap E₂.toLinearMap := by
    simpa [H₂lo] using h₂.lower
  have hhi₁ : CompletelyPositiveLE E₁.toLinearMap H₁hi.toLinearMap := by
    simpa [H₁hi] using h₁.upper
  have hhi₂ : CompletelyPositiveLE E₂.toLinearMap H₂hi.toLinearMap := by
    simpa [H₂hi] using h₂.upper
  constructor
  · have hcomp := CompletelyPositiveLE.comp_of_cp hlo₁ hlo₂
    rw [CompletelyPositiveMap.comp_nonnegRealSMul_toLinearMap] at hcomp
    exact hcomp
  · have hcomp := CompletelyPositiveLE.comp_of_cp hhi₁ hhi₂
    rw [CompletelyPositiveMap.comp_nonnegRealSMul_toLinearMap] at hcomp
    exact hcomp

/-- Symmetric multiplicative-error form of the exact product sandwich.
The error is exactly `(1+ε₁)(1+ε₂)-1`. -/
theorem relativeCPApproximation_comp
    (E₁ H₁ E₂ H₂ : A →CP A) (ε₁ ε₂ : ℝ)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1)
    (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1)
    (h₁ : RelativeCPApproximation ε₁ E₁.toLinearMap H₁.toLinearMap)
    (h₂ : RelativeCPApproximation ε₂ E₂.toLinearMap H₂.toLinearMap) :
    RelativeCPApproximation
      ((1 + ε₁) * (1 + ε₂) - 1)
      (CompletelyPositiveMap.comp E₁ E₂).toLinearMap
      (CompletelyPositiveMap.comp H₁ H₂).toLinearMap := by
  obtain ⟨hlo, hhi⟩ := relativeCPApproximation_comp_product_sandwich
    E₁ H₁ E₂ H₂ ε₁ ε₂ hε₁0 hε₁1 hε₂0 hε₂1 h₁ h₂
  constructor
  · apply (CompletelyPositiveLE.real_smul_mono
      (CompletelyPositiveMap.comp H₁ H₂) ?_).trans hlo
    nlinarith [mul_nonneg hε₁0 hε₂0]
  · have hcoeff :
        1 + ((1 + ε₁) * (1 + ε₂) - 1) =
          (1 + ε₁) * (1 + ε₂) := by ring
    rw [hcoeff]
    exact hhi

/-- Premise-minimal two-unitary gluing interface.

The two local ensemble/reference errors are combined unconditionally by CP
order algebra.  The sole additional premise is the relative-CP comparison
of the *composed local reference* with the desired global reference.  In
Schuster--Haferkamp--Huang Lemma 8, this is precisely the EPR-state and
permutation-Gram-matrix estimate of Eqs. (B.26)--(B.27). -/
theorem relativeCPApproximation_twoUnitary_of_reference_gluing
    (E₁ H₁ E₂ H₂ Hglobal : A →CP A) (ε₁ ε₂ δ : ℝ)
    (hε₁0 : 0 ≤ ε₁) (hε₁1 : ε₁ ≤ 1)
    (hε₂0 : 0 ≤ ε₂) (hε₂1 : ε₂ ≤ 1)
    (hδ0 : 0 ≤ δ)
    (h₁ : RelativeCPApproximation ε₁ E₁.toLinearMap H₁.toLinearMap)
    (h₂ : RelativeCPApproximation ε₂ E₂.toLinearMap H₂.toLinearMap)
    (hreference : RelativeCPApproximation δ
      (CompletelyPositiveMap.comp H₁ H₂).toLinearMap
      Hglobal.toLinearMap) :
    RelativeCPApproximation
      ((1 + ε₁) * (1 + ε₂) * (1 + δ) - 1)
      (CompletelyPositiveMap.comp E₁ E₂).toLinearMap
      Hglobal.toLinearMap := by
  obtain ⟨hlocalLower, hlocalUpper⟩ :=
    relativeCPApproximation_comp_product_sandwich
      E₁ H₁ E₂ H₂ ε₁ ε₂ hε₁0 hε₁1 hε₂0 hε₂1 h₁ h₂
  have hlowerCoefficientNonneg :
      0 ≤ (1 - ε₁) * (1 - ε₂) :=
    mul_nonneg (sub_nonneg.mpr hε₁1) (sub_nonneg.mpr hε₂1)
  have hupperCoefficientNonneg :
      0 ≤ (1 + ε₁) * (1 + ε₂) :=
    mul_nonneg (by linarith) (by linarith)
  have hproductLower : CompletelyPositiveLE
      (((((1 - ε₁) * (1 - ε₂) * (1 - δ) : ℝ) : ℂ) •
        Hglobal.toLinearMap))
      (CompletelyPositiveMap.comp E₁ E₂).toLinearMap := by
    have hscaled := hreference.lower.real_smul
      ((1 - ε₁) * (1 - ε₂)) hlowerCoefficientNonneg
    have htrans := hscaled.trans hlocalLower
    simpa [smul_smul] using htrans
  have hproductUpper : CompletelyPositiveLE
      (CompletelyPositiveMap.comp E₁ E₂).toLinearMap
      (((((1 + ε₁) * (1 + ε₂) * (1 + δ) : ℝ) : ℂ) •
        Hglobal.toLinearMap)) := by
    have hscaled := hreference.upper.real_smul
      ((1 + ε₁) * (1 + ε₂)) hupperCoefficientNonneg
    have htrans := hlocalUpper.trans hscaled
    simpa [smul_smul] using htrans
  constructor
  · apply (CompletelyPositiveLE.real_smul_mono Hglobal ?_).trans
      hproductLower
    nlinarith [mul_nonneg hε₁0 hε₂0,
      mul_nonneg hε₁0 hδ0, mul_nonneg hε₂0 hδ0]
  · have hcoeff :
        1 + ((1 + ε₁) * (1 + ε₂) * (1 + δ) - 1) =
          (1 + ε₁) * (1 + ε₂) * (1 + δ) := by ring
    rw [hcoeff]
    exact hproductUpper

end RelativeComposition

end TomographyOracleCore
