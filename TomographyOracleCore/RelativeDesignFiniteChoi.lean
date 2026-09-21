import TomographyOracleCore.RelativeDesignEPRFlatSupport
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

namespace TomographyOracleCore

open scoped CStarAlgebra ContinuousFunctionalCalculus
  NonUnitalContinuousFunctionalCalculus

noncomputable section

local instance : PartialOrder ℂ := CStarAlgebra.spectralOrder ℂ
local instance : StarOrderedRing ℂ := CStarAlgebra.spectralOrderedRing ℂ

@[simp] theorem cstarMatrix_fintypeSum_apply
    {Q m n A : Type*} [Fintype Q] [AddCommMonoid A]
    (F : Q → CStarMatrix m n A) (i : m) (j : n) :
    (∑ q : Q, F q) i j = ∑ q : Q, F q i j := by
  classical
  have hsum : ∀ s : Finset Q,
      (∑ q ∈ s, F q) i j = ∑ q ∈ s, F q i j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert q s hqs ih =>
        simp [Finset.sum_insert, hqs, ih, CStarMatrix.add_apply]
  exact hsum Finset.univ

theorem finite_delta_conjugation_sum
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : I → I → ℂ) (i a j b : I) :
    (∑ x : I,
        (∑ y : I, if y = i ∧ x = j then star (F y a) else 0) * F x b) =
      star (F i a) * F j b := by
  rw [← Fintype.sum_ite_eq' j
    (fun x : I ↦ star (F i a) * F x b)]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxj : x = j
  · subst x
    simp
  · simp [hxj]

/-!
# Finite Choi matrices for the reference-gluing reduction

The definitions here use the basis ordering `(input, output)`.  Thus the
`((i,a),(j,b))` entry of the Choi matrix of `Phi` is the `(a,b)` entry of
`Phi(E_ij)`.  This convention makes a positive Choi factor directly into a
finite Kraus family.
-/

/-- The `(i,j)` matrix unit in a finite complex matrix algebra. -/
def finiteCStarMatrixUnit {I : Type*} [DecidableEq I]
    (i j : I) : CStarMatrix I I ℂ :=
  fun a b ↦ if a = i ∧ b = j then 1 else 0

@[simp] theorem finiteCStarMatrixUnit_apply
    {I : Type*} [DecidableEq I] (i j a b : I) :
    finiteCStarMatrixUnit i j a b =
      if a = i ∧ b = j then 1 else 0 := rfl

theorem smul_finiteCStarMatrixUnit_eq_single
    {I : Type*} [DecidableEq I] (c : ℂ) (i j : I) :
    c • finiteCStarMatrixUnit i j =
      CStarMatrix.ofMatrix (Matrix.single i j c) := by
  apply CStarMatrix.ext
  intro a b
  simp [finiteCStarMatrixUnit, Matrix.single, eq_comm]

/-- The unnormalized maximally-entangled projector, with tensor coordinates
ordered as `(input, reference)`. -/
def finiteEPRProjector {I : Type*} [DecidableEq I] :
    CStarMatrix (I × I) (I × I) ℂ :=
  fun ia jb ↦ if ia.1 = ia.2 ∧ jb.1 = jb.2 then 1 else 0

/-- Choi matrix of a linear map on a finite complex matrix algebra. -/
def finiteChoiMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (Φ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ) :
    CStarMatrix (I × I) (I × I) ℂ :=
  fun ia jb ↦ Φ (finiteCStarMatrixUnit ia.1 jb.1) ia.2 jb.2

@[simp] theorem finiteChoiMatrix_apply
    {I : Type*} [Fintype I] [DecidableEq I]
    (Φ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ)
    (i a j b : I) :
    finiteChoiMatrix Φ (i, a) (j, b) =
      Φ (finiteCStarMatrixUnit i j) a b := rfl

/-- Finite Choi matrices determine their linear maps. -/
theorem finiteChoiMatrix_injective
    {I : Type*} [Fintype I] [DecidableEq I] :
    Function.Injective
      (finiteChoiMatrix (I := I)) := by
  intro Φ Ψ hchoi
  apply LinearMap.ext
  intro (X : CStarMatrix I I ℂ)
  have hunit : ∀ i j : I,
      Φ (finiteCStarMatrixUnit i j) =
        Ψ (finiteCStarMatrixUnit i j) := by
    intro i j
    apply CStarMatrix.ext
    intro a b
    exact congr_fun (congr_fun hchoi (i, a)) (j, b)
  have hdecomp :
      X = ∑ i : I, ∑ j : I,
        X i j • finiteCStarMatrixUnit i j := by
    simp_rw [smul_finiteCStarMatrixUnit_eq_single]
    change CStarMatrix.ofMatrix.symm X =
      ∑ i : I, ∑ j : I, Matrix.single i j (X i j)
    exact Matrix.matrix_eq_sum_single _
  rw [hdecomp]
  simp only [map_sum, map_smul, hunit]

/-- A single finite Kraus conjugation `X ↦ V† X V`, packaged as a
completely positive map. -/
def finiteKrausConjugation
    {I : Type*} [Fintype I] [DecidableEq I]
    (V : CStarMatrix I I ℂ) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ where
  toLinearMap :=
    { toFun := fun X ↦ star V * X * V
      map_add' := by
        intro X Y
        simp only [mul_add, add_mul]
      map_smul' := by
        intro c X
        simp only [RingHom.id_apply, smul_mul_assoc, mul_smul_comm] }
  map_cstarMatrix_nonneg' := by
    intro k M hM
    let D : CStarMatrix (Fin k) (Fin k) (CStarMatrix I I ℂ) :=
      fun i j ↦ if i = j then V else 0
    have hmap : M.map
          ({ toFun := fun X ↦ star V * X * V
             map_add' := by intro X Y; simp only [mul_add, add_mul]
             map_smul' := by
               intro c X
               simp only [RingHom.id_apply, smul_mul_assoc, mul_smul_comm] } :
            CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ) =
        star D * M * D := by
      apply CStarMatrix.ext
      intro i j
      change star V * M i j * V = (star D * M * D) i j
      rw [CStarMatrix.mul_apply]
      simp_rw [CStarMatrix.mul_apply, CStarMatrix.star_apply]
      simp only [D]
      have hsum :
          (∑ x : Fin k, star (if x = i then V else 0) * M x j) =
            star V * M i j := by
        rw [← Fintype.sum_ite_eq' i (fun x ↦ star V * M x j)]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxi : x = i <;> simp [hxi]
      have houter :
          (∑ x : Fin k,
            (∑ y : Fin k, star (if y = i then V else 0) * M y x) *
              (if x = j then V else 0)) =
            (∑ y : Fin k, star (if y = i then V else 0) * M y j) * V := by
        rw [← Fintype.sum_ite_eq' j
          (fun x ↦ (∑ y : Fin k,
            star (if y = i then V else 0) * M y x) * V)]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxj : x = j <;> simp [hxj]
      rw [houter, hsum]
    rw [hmap]
    exact star_left_conjugate_nonneg hM D

/-- A finite sum of completely positive maps is completely positive. -/
def CompletelyPositiveMap.fintypeSum
    {A₁ A₂ Q : Type*}
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
    [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂]
    [Fintype Q]
    (Φ : Q → A₁ →CP A₂) : A₁ →CP A₂ where
  toLinearMap := ∑ q : Q, (Φ q).toLinearMap
  map_cstarMatrix_nonneg' := by
    intro k M hM
    have hnonneg : 0 ≤ ∑ q : Q, M.map (Φ q).toLinearMap :=
      Finset.sum_nonneg fun q _ ↦
      (Φ q).map_cstarMatrix_nonneg' k M hM
    convert hnonneg using 1
    apply CStarMatrix.ext
    intro i j
    simp only [CStarMatrix.map_apply, LinearMap.sum_apply,
      cstarMatrix_fintypeSum_apply]

@[simp] theorem CompletelyPositiveMap.fintypeSum_toLinearMap
    {A₁ A₂ Q : Type*}
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
    [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂]
    [Fintype Q]
    (Φ : Q → A₁ →CP A₂) :
    (CompletelyPositiveMap.fintypeSum Φ).toLinearMap =
      ∑ q : Q, (Φ q).toLinearMap := rfl

/-- The Kraus matrix obtained by reshaping one row of a Choi factor. -/
def finiteChoiFactorKrausMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : CStarMatrix (I × I) (I × I) ℂ) (q : I × I) :
    CStarMatrix I I ℂ :=
  fun i a ↦ B q (i, a)

/-- Kraus reconstruction associated with the rows of a square factor of a
finite Choi matrix. -/
def finiteChoiFactorKrausMap
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : CStarMatrix (I × I) (I × I) ℂ) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  CompletelyPositiveMap.fintypeSum fun q : I × I ↦
    finiteKrausConjugation (finiteChoiFactorKrausMatrix B q)

/-- The Choi matrix of the Kraus family obtained from `B` is exactly
`B† B`. -/
theorem finiteChoiMatrix_finiteChoiFactorKrausMap
    {I : Type*} [Fintype I] [DecidableEq I]
    (B : CStarMatrix (I × I) (I × I) ℂ) :
    finiteChoiMatrix (finiteChoiFactorKrausMap B).toLinearMap =
      star B * B := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp only [finiteChoiMatrix_apply, finiteChoiFactorKrausMap,
    CompletelyPositiveMap.fintypeSum_toLinearMap, LinearMap.sum_apply,
    cstarMatrix_fintypeSum_apply, finiteKrausConjugation]
  change (∑ q : I × I,
    (star (finiteChoiFactorKrausMatrix B q) *
      finiteCStarMatrixUnit i j * finiteChoiFactorKrausMatrix B q) a b) =
    (star B * B) (i, a) (j, b)
  rw [CStarMatrix.mul_apply]
  apply Finset.sum_congr rfl
  intro q hq
  rw [CStarMatrix.mul_apply]
  simp_rw [CStarMatrix.mul_apply]
  simp_rw [CStarMatrix.star_apply]
  simp [finiteCStarMatrixUnit, finiteChoiFactorKrausMatrix]
  exact finite_delta_conjugation_sum
    (fun x y : I ↦ B q (x, y)) i a j b

/-- The zero linear map, packaged as a completely positive map. -/
def CompletelyPositiveMap.zeroMap
    {A₁ A₂ : Type*}
    [NonUnitalCStarAlgebra A₁] [NonUnitalCStarAlgebra A₂]
    [PartialOrder A₁] [PartialOrder A₂]
    [StarOrderedRing A₁] [StarOrderedRing A₂] : A₁ →CP A₂ where
  toLinearMap := 0
  map_cstarMatrix_nonneg' := by
    intro k M hM
    have hz : M.map (0 : A₁ →ₗ[ℂ] A₂) = 0 := by
      apply CStarMatrix.ext
      intro i j
      rfl
    rw [hz]

@[simp] theorem finiteChoiMatrix_zero
    {I : Type*} [Fintype I] [DecidableEq I] :
    finiteChoiMatrix
      (0 : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ) = 0 := by
  apply CStarMatrix.ext
  intro ia jb
  rfl

@[simp] theorem finiteChoiMatrix_add
    {I : Type*} [Fintype I] [DecidableEq I]
    (Φ Ψ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ) :
    finiteChoiMatrix (Φ + Ψ) =
      finiteChoiMatrix Φ + finiteChoiMatrix Ψ := by
  apply CStarMatrix.ext
  intro ia jb
  rfl

@[simp] theorem finiteChoiMatrix_sub
    {I : Type*} [Fintype I] [DecidableEq I]
    (Φ Ψ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ) :
    finiteChoiMatrix (Φ - Ψ) =
      finiteChoiMatrix Φ - finiteChoiMatrix Ψ := by
  apply CStarMatrix.ext
  intro ia jb
  rfl

@[simp] theorem finiteChoiMatrix_smul
    {I : Type*} [Fintype I] [DecidableEq I]
    (c : ℂ) (Φ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ) :
    finiteChoiMatrix (c • Φ) = c • finiteChoiMatrix Φ := by
  apply CStarMatrix.ext
  intro ia jb
  rfl

/-- Finite-dimensional Choi criterion, in the direction needed for the EPR
reduction: a nonnegative Choi matrix yields a completely positive map with
the same underlying linear map.  The proof is purely algebraic: positivity
is induction over the finite sums of `B† B` defining `StarOrderedRing`. -/
theorem exists_completelyPositiveMap_of_finiteChoiMatrix_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    (Φ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ)
    (hchoi : 0 ≤ finiteChoiMatrix Φ) :
    ∃ Ψ : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ,
      Ψ.toLinearMap = Φ := by
  have hmem := StarOrderedRing.nonneg_iff.mp hchoi
  have hconstruct : ∀
      C : CStarMatrix (I × I) (I × I) ℂ,
      C ∈ AddSubmonoid.closure
        (Set.range fun B : CStarMatrix (I × I) (I × I) ℂ ↦ star B * B) →
      ∃ Ψ : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ,
        finiteChoiMatrix Ψ.toLinearMap = C := by
    intro C hC
    induction hC using AddSubmonoid.closure_induction with
    | mem C hC =>
        obtain ⟨B, rfl⟩ := hC
        exact ⟨finiteChoiFactorKrausMap B,
          finiteChoiMatrix_finiteChoiFactorKrausMap B⟩
    | zero =>
        exact ⟨CompletelyPositiveMap.zeroMap, finiteChoiMatrix_zero⟩
    | add C₁ C₂ hC₁ hC₂ ih₁ ih₂ =>
        obtain ⟨Ψ₁, hΨ₁⟩ := ih₁
        obtain ⟨Ψ₂, hΨ₂⟩ := ih₂
        refine ⟨CompletelyPositiveMap.add Ψ₁ Ψ₂, ?_⟩
        rw [CompletelyPositiveMap.add_toLinearMap,
          finiteChoiMatrix_add, hΨ₁, hΨ₂]
  obtain ⟨Ψ, hΨ⟩ := hconstruct (finiteChoiMatrix Φ) hmem
  exact ⟨Ψ, finiteChoiMatrix_injective hΨ⟩

/-- On finite complex matrix algebras, Choi positivity proves completely
positive order without assuming the desired order comparison. -/
theorem completelyPositiveLE_of_finiteChoiMatrix_sub_nonneg
    {I : Type*} [Fintype I] [DecidableEq I]
    {Φ Ψ : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ}
    (hchoi : 0 ≤ finiteChoiMatrix (Ψ - Φ)) :
    CompletelyPositiveLE Φ Ψ := by
  obtain ⟨Δ, hΔ⟩ :=
    exists_completelyPositiveMap_of_finiteChoiMatrix_nonneg (Ψ - Φ) hchoi
  exact ⟨Δ, hΔ⟩

/-- The finite-dimensional EPR/Choi order step behind the reference gluing
argument.  A flat Choi reference `c P` and a supported self-adjoint Choi
error of norm at most `epsilon * c` give both relative completely-positive
inequalities. -/
theorem relativeCPApproximation_of_finiteChoi_flatSupport_norm
    {I : Type*} [Fintype I] [DecidableEq I]
    (epsilon c : ℝ)
    (Φ H : CStarMatrix I I ℂ →ₗ[ℂ] CStarMatrix I I ℂ)
    (P : CStarMatrix (I × I) (I × I) ℂ)
    (hepsilon : 0 ≤ epsilon) (hc : 0 ≤ c)
    (hH : finiteChoiMatrix H = (c : ℂ) • P)
    (herrorSelf : IsSelfAdjoint (finiteChoiMatrix (Φ - H)))
    (hPself : IsSelfAdjoint P)
    (hPid : P * P = P)
    (herrorSupport :
      P * finiteChoiMatrix (Φ - H) * P = finiteChoiMatrix (Φ - H))
    (herrorNorm : ‖finiteChoiMatrix (Φ - H)‖ ≤ epsilon * c) :
    RelativeCPApproximation epsilon Φ H := by
  let X := finiteChoiMatrix (Φ - H)
  have hPnonneg : 0 ≤ P := by
    calc
      0 ≤ star P * P := star_mul_self_nonneg P
      _ = P * P := by rw [hPself.star_eq]
      _ = P := hPid
  have hflat :
      -(‖X‖ : ℝ) • P ≤ X ∧ X ≤ (‖X‖ : ℝ) • P := by
    exact selfAdjoint_supported_between_norm_smul_projection
      X P herrorSelf hPself hPid herrorSupport
  have hscale : (‖X‖ : ℝ) • P ≤ (epsilon * c) • P :=
    smul_le_smul_of_nonneg_right herrorNorm hPnonneg
  have hflatLower : -((‖X‖ : ℝ) • P) ≤ X := by
    simpa only [neg_smul] using hflat.1
  have hlowerReal : -((epsilon * c) • P) ≤ X :=
    (neg_le_neg hscale).trans hflatLower
  have hupperReal : X ≤ (epsilon * c) • P := hflat.2.trans hscale
  have hPhi : finiteChoiMatrix Φ = X + (c : ℂ) • P := by
    dsimp only [X]
    rw [finiteChoiMatrix_sub, hH]
    module
  constructor
  · apply completelyPositiveLE_of_finiteChoiMatrix_sub_nonneg
    rw [finiteChoiMatrix_sub, finiteChoiMatrix_smul, hPhi, hH]
    have hnonneg : 0 ≤ X + (epsilon * c) • P :=
      neg_le_iff_add_nonneg.mp hlowerReal
    convert hnonneg using 1
    apply CStarMatrix.ext
    intro ia jb
    simp only [CStarMatrix.add_apply, CStarMatrix.sub_apply,
      CStarMatrix.smul_apply, Complex.real_smul]
    push_cast
    ring
  · apply completelyPositiveLE_of_finiteChoiMatrix_sub_nonneg
    rw [finiteChoiMatrix_sub, finiteChoiMatrix_smul, hPhi, hH]
    have hnonneg : 0 ≤ (epsilon * c) • P - X :=
      sub_nonneg.mpr hupperReal
    convert hnonneg using 1
    apply CStarMatrix.ext
    intro ia jb
    simp only [CStarMatrix.add_apply, CStarMatrix.sub_apply,
      CStarMatrix.smul_apply, Complex.real_smul]
    push_cast
    ring

end

end TomographyOracleCore
