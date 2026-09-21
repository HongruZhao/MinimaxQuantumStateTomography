import TomographyOracleCore.GrassmannHaarCyclicOrbit
import TomographyOracleCore.PureSphereProjectionLaplace
import TomographyOracleCore.ProjectiveHaarBlockLaw

namespace TomographyOracleCore

open MeasureTheory Real Set Metric
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

/-!
# Exact pure-sphere endpoint for the Grassmann Laplace reduction

The source proof compares the rank-`m` Haar orbit in `ℂ^k` with a Haar
unit vector in `ℂ^k ⊗ ℂ^m`.  The relevant fixed subspace has complex
dimension `(k-m)m`, while the ambient space has complex dimension `km`.

This file makes that last induced-state/local-unitary comparison an explicit
theorem target.  Everything after that single geometric comparison,
including the fixed-subspace Laplace estimate and the Grassmann packing
endpoint, is proved here.
-/

/-! ## A generic initial complex-coordinate subspace -/

/-- The first `q` complex coordinates in `ℂ^(q+h)`. -/
def complexInitialComplexSubspace (q h : ℕ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (q + h))) where
  carrier := {x | ∀ j : Fin h, x (Fin.natAdd q j) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy j
    simp [hx j, hy j]
  smul_mem' := by
    intro c x hx j
    simp [hx j]

/-- The same coordinate subspace, regarded over `ℝ`. -/
def complexInitialRealSubspace (q h : ℕ) :
    Submodule ℝ (EuclideanSpace ℂ (Fin (q + h))) :=
  (complexInitialComplexSubspace q h).restrictScalars ℝ

/-- Extract the first `q` coordinates. -/
def complexInitialCoord (q h : ℕ)
    (x : complexInitialComplexSubspace q h) :
    EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 (fun i ↦ x.1 (Fin.castAdd h i))

/-- Embed `ℂ^q` as the first `q` coordinates of `ℂ^(q+h)`. -/
def complexInitialEmbed (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin q)) :
    complexInitialComplexSubspace q h :=
  ⟨WithLp.toLp 2 (fun a ↦
      Sum.elim (fun i ↦ x i) (fun _ ↦ 0) (finSumFinEquiv.symm a)), by
    intro j
    simp⟩

@[simp] theorem complexInitialCoord_apply (q h : ℕ)
    (x : complexInitialComplexSubspace q h) (i : Fin q) :
    complexInitialCoord q h x i = x.1 (Fin.castAdd h i) := rfl

@[simp] theorem complexInitialEmbed_apply_castAdd (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin q)) (i : Fin q) :
    (complexInitialEmbed q h x).1 (Fin.castAdd h i) = x i := by
  simp [complexInitialEmbed]

@[simp] theorem complexInitialEmbed_apply_natAdd (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin q)) (j : Fin h) :
    (complexInitialEmbed q h x).1 (Fin.natAdd q j) = 0 := by
  simp [complexInitialEmbed]

/-- Complex-linear coordinate equivalence for the initial block. -/
def complexInitialLinearEquiv (q h : ℕ) :
    complexInitialComplexSubspace q h ≃ₗ[ℂ] EuclideanSpace ℂ (Fin q) where
  toFun := complexInitialCoord q h
  invFun := complexInitialEmbed q h
  map_add' x y := by
    ext i
    rfl
  map_smul' c x := by
    ext i
    rfl
  left_inv x := by
    apply Subtype.ext
    ext a
    generalize ha : finSumFinEquiv.symm a = z
    cases z with
    | inl i =>
        have hai : a = Fin.castAdd h i := by
          simpa using congrArg finSumFinEquiv ha
        subst a
        simp
    | inr j =>
        have haj : a = Fin.natAdd q j := by
          simpa using congrArg finSumFinEquiv ha
        subst a
        simp [x.2 j]
  right_inv x := by
    ext i
    simp [complexInitialCoord]

theorem complexInitialLinearEquiv_inner (q h : ℕ)
    (x y : complexInitialComplexSubspace q h) :
    ⟪complexInitialLinearEquiv q h x,
      complexInitialLinearEquiv q h y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [complexInitialLinearEquiv, complexInitialCoord,
    PiLp.inner_apply, RCLike.inner_apply, Submodule.coe_inner]
  rw [Fin.sum_univ_add]
  rw [show (∑ i : Fin h,
      y.1 (Fin.natAdd q i) * starRingEnd ℂ (x.1 (Fin.natAdd q i))) = 0 by
    apply Finset.sum_eq_zero
    intro i hi
    rw [x.2 i, y.2 i]
    simp]
  simp

/-- Isometric form of the initial-block equivalence. -/
def complexInitialIsometryEquiv (q h : ℕ) :
    complexInitialComplexSubspace q h ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin q) :=
  LinearEquiv.isometryOfInner (𝕜 := ℂ) (complexInitialLinearEquiv q h)
    (fun x y ↦ complexInitialLinearEquiv_inner q h x y)

/-- The initial-block equivalence over real scalars. -/
def complexInitialRealIsometryEquiv (q h : ℕ) :
    complexInitialRealSubspace q h ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin q) where
  toFun x := complexInitialIsometryEquiv q h ⟨x.1, x.2⟩
  invFun y :=
    ⟨(complexInitialIsometryEquiv q h).symm y,
      (complexInitialIsometryEquiv q h).symm y |>.property⟩
  left_inv x := by
    apply Subtype.ext
    exact congrArg Subtype.val
      ((complexInitialIsometryEquiv q h).symm_apply_apply ⟨x.1, x.2⟩)
  right_inv y := (complexInitialIsometryEquiv q h).apply_symm_apply y
  map_add' x y := by
    exact map_add (complexInitialIsometryEquiv q h) ⟨x.1, x.2⟩ ⟨y.1, y.2⟩
  map_smul' c x := by
    change complexInitialIsometryEquiv q h
        ⟨((c : ℂ) • x.1), ?_⟩ =
      c • complexInitialIsometryEquiv q h ⟨x.1, x.2⟩
    exact map_smul (complexInitialIsometryEquiv q h) (c : ℂ) ⟨x.1, x.2⟩
  norm_map' x := by
    exact (complexInitialIsometryEquiv q h).norm_map ⟨x.1, x.2⟩

/-- The real dimension of a `q`-complex-dimensional coordinate block. -/
theorem finrank_complexInitialRealSubspace (q h : ℕ) :
    Module.finrank ℝ (complexInitialRealSubspace q h) = 2 * q := by
  have hrank := LinearEquiv.finrank_eq
    (complexInitialRealIsometryEquiv q h).toLinearEquiv
  rw [finrank_real_of_complex] at hrank
  simpa using hrank

/-! ### Coordinate form of the projection -/

/-- Keep exactly the first `q` coordinates of an ambient vector. -/
def complexInitialPart (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) :
    EuclideanSpace ℂ (Fin (q + h)) :=
  (complexInitialEmbed q h (WithLp.toLp 2
    (fun i : Fin q ↦ x (Fin.castAdd h i)))).1

@[simp] theorem complexInitialPart_apply_castAdd (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) (i : Fin q) :
    complexInitialPart q h x (Fin.castAdd h i) = x (Fin.castAdd h i) := by
  simp [complexInitialPart]

@[simp] theorem complexInitialPart_apply_natAdd (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) (j : Fin h) :
    complexInitialPart q h x (Fin.natAdd q j) = 0 := by
  simp [complexInitialPart]

theorem complexInitialPart_mem (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) :
    complexInitialPart q h x ∈ complexInitialRealSubspace q h := by
  intro j
  simp

theorem complexInitialPart_is_projection (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) :
    (complexInitialRealSubspace q h).starProjection x =
      complexInitialPart q h x := by
  apply (complexInitialRealSubspace q h).eq_starProjection_of_mem_of_inner_eq_zero
  · exact complexInitialPart_mem q h x
  · intro w hw
    simp only [PiLp.inner_apply, PiLp.sub_apply]
    rw [Fin.sum_univ_add]
    have hinitial : (∑ i : Fin q,
        ⟪x (Fin.castAdd h i) - complexInitialPart q h x (Fin.castAdd h i),
          w (Fin.castAdd h i)⟫_ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp
    have hrest : (∑ j : Fin h,
        ⟪x (Fin.natAdd q j) - complexInitialPart q h x (Fin.natAdd q j),
          w (Fin.natAdd q j)⟫_ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hwj : w (Fin.natAdd q j) = 0 := hw j
      rw [hwj]
      simp
    rw [hinitial, hrest, add_zero]

theorem complexInitialPart_norm_sq (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) :
    ‖complexInitialPart q h x‖ ^ 2 =
      ∑ i : Fin q, Complex.normSq (x (Fin.castAdd h i)) := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_add]
  simp [Complex.normSq_eq_norm_sq]

/-- The projection energy is literally the mass in the first `q` complex
coordinates. -/
theorem complexInitialProjection_norm_sq (q h : ℕ)
    (x : EuclideanSpace ℂ (Fin (q + h))) :
    ‖(complexInitialRealSubspace q h).orthogonalProjectionOnto x‖ ^ 2 =
      ∑ i : Fin q, Complex.normSq (x (Fin.castAdd h i)) := by
  rw [show ‖(complexInitialRealSubspace q h).orthogonalProjectionOnto x‖ =
      ‖complexInitialPart q h x‖ by
    change ‖(complexInitialRealSubspace q h).starProjection x‖ = _
    rw [complexInitialPart_is_projection]]
  exact complexInitialPart_norm_sq q h x

/-! ## The exact remaining induced-state comparison -/

/-- The `km`-complex-dimensional pure-state space split into the
`(k-m)m` complementary block and the `m²` canonical block. -/
abbrev GrassmannPureSphereSpace (k m : ℕ) :=
  EuclideanSpace ℂ (Fin (((k - m) * m) + (m * m)))

/-- The complementary-coordinate subspace in the bipartite pure-state
realization. -/
abbrev grassmannPureSphereComplementSubspace (k m : ℕ) :
    Submodule ℝ (GrassmannPureSphereSpace k m) :=
  complexInitialRealSubspace ((k - m) * m) (m * m)

/-- Exact local-unitary/induced-state bridge remaining in the
Hayden--Leung--Winter argument.

It says that the canonical rank-`m` unitary-orbit Laplace transform is at
most the fixed complementary-block Laplace transform of a Haar pure state
on `ℂ^k ⊗ ℂ^m`.  No tail estimate is hidden in this statement. -/
def GrassmannInducedStatePureSphereBridge
    (k m : ℕ) (hm : 1 ≤ m) (hmk : m ≤ k) : Prop :=
  letI : Nontrivial (GrassmannPureSphereSpace k m) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_complexEuclideanSpace_real_headBlock]
      have hmpos : 0 < m := by omega
      positivity)
  (∫ U, Real.exp
      ((-((k : ℝ) / 3)) * canonicalUnitaryComplementOverlap k m hmk U)
      ∂unitaryHaarProbability k) ≤
    ∫ u : sphere (0 : GrassmannPureSphereSpace k m) 1,
      Real.exp
        (-(((k * m : ℕ) : ℝ) / 3) *
          ‖(grassmannPureSphereComplementSubspace k m).orthogonalProjectionOnto
              (u : GrassmannPureSphereSpace k m)‖ ^ 2)
      ∂LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m)

/-- The already-proved pure-sphere projection theorem closes the exact
canonical Haar Laplace input once the induced-state bridge is supplied. -/
theorem canonicalUnitaryQuarterLaplaceBound_of_inducedStatePureSphereBridge
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hbridge : GrassmannInducedStatePureSphereBridge k m hm (by omega)) :
    CanonicalUnitaryQuarterLaplaceBound k m (by omega) := by
  let q : ℕ := (k - m) * m
  let h : ℕ := m * m
  let E := GrassmannPureSphereSpace k m
  let K := grassmannPureSphereComplementSubspace k m
  have hmk : m ≤ k := by omega
  have hkpos : 0 < k := by omega
  have hN : 0 < k * m := Nat.mul_pos hkpos (by omega)
  have hq : 0 < q := by
    dsimp only [q]
    exact Nat.mul_pos (Nat.sub_pos_of_lt (by omega)) (by omega)
  have hE : Module.finrank ℝ E = 2 * (k * m) := by
    dsimp only [E, GrassmannPureSphereSpace]
    rw [finrank_complexEuclideanSpace_real_headBlock]
    rw [← Nat.add_mul, Nat.sub_add_cancel hmk]
  have hK : Module.finrank ℝ K = 2 * q := by
    dsimp only [K, grassmannPureSphereComplementSubspace, q, h]
    exact finrank_complexInitialRealSubspace ((k - m) * m) (m * m)
  letI : Nontrivial E := Module.nontrivial_of_finrank_pos (by
    rw [hE]
    omega)
  letI : Nontrivial K := Module.nontrivial_of_finrank_pos (by
    rw [hK]
    omega)
  have hpure := pureSphereProjection_laplace_le K hN hq hE hK
  have hpowexp : (3 / 4 : ℝ) ^ q =
      Real.exp ((q : ℝ) * Real.log (3 / 4 : ℝ)) := by
    calc
      (3 / 4 : ℝ) ^ q = (3 / 4 : ℝ) ^ (q : ℝ) := by
        rw [Real.rpow_natCast]
      _ = Real.exp (Real.log (3 / 4 : ℝ) * (q : ℝ)) := by
        rw [Real.rpow_def_of_pos (by norm_num)]
      _ = Real.exp ((q : ℝ) * Real.log (3 / 4 : ℝ)) := by
        congr 1
        ring
  unfold CanonicalUnitaryQuarterLaplaceBound
  calc
    (∫ U, Real.exp
        ((-((k : ℝ) / 3)) * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
        ∫ u : sphere (0 : E) 1,
          Real.exp
            (-(((k * m : ℕ) : ℝ) / 3) *
              ‖K.orthogonalProjectionOnto (u : E)‖ ^ 2)
          ∂LogdetLean.uniformSphereSurfaceMeasure (E := E) := by
      simpa only [GrassmannInducedStatePureSphereBridge, E, K] using hbridge
    _ ≤ (3 / 4 : ℝ) ^ q := hpure
    _ = Real.exp
        ((((k - m : ℕ) : ℝ) * (m : ℝ)) * Real.log (3 / 4 : ℝ)) := by
      rw [hpowexp]
      congr 1
      dsimp only [q]
      norm_cast

/-- Exact Grassmann packing endpoint after isolating only the
local-unitary/induced-state bridge. -/
theorem exists_complexGrassmannPackingWitness_card_eq_of_inducedStatePureSphereBridge
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hbridge : GrassmannInducedStatePureSphereBridge k m hm (by omega)) :
    ∃ V : ComplexGrassmannPackingWitness k m,
      V.card = grassmannPackingCard k m := by
  exact exists_complexGrassmannPackingWitness_card_eq_of_canonicalUnitaryLaplace
    hm hkm
      (canonicalUnitaryQuarterLaplaceBound_of_inducedStatePureSphereBridge
        hm hkm hbridge)

end

end TomographyOracleCore
