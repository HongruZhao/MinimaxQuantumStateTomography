import TomographyOracleCore.GrassmannPureSphereBridge
import TomographyOracleCore.ProjectiveHaarMoments
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Logic.Equiv.Prod

namespace TomographyOracleCore

open MeasureTheory Real Set Metric Matrix
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder
  ComplexConjugate

noncomputable section

/-!
# Local-unitary realization of the Grassmann induced-state bridge

This module develops the algebraic and invariant-measure ingredients for the
single bridge isolated in `GrassmannPureSphereBridge`.
-/

/-! ## Unitary matrices act isometrically on complex Euclidean vectors -/

/-- Multiplication by a unitary matrix as a complex-linear equivalence. -/
def unitaryMulVecLinearEquiv {k : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    EuclideanSpace ℂ (Fin k) ≃ₗ[ℂ] EuclideanSpace ℂ (Fin k) where
  toLinearMap := Matrix.toLpLin 2 2 U.1
  invFun x := Matrix.toLpLin 2 2 (star U.1) x
  left_inv x := by
    change Matrix.toLpLin 2 2 (star U.1)
        (Matrix.toLpLin 2 2 U.1 x) = x
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      U.property.1, Matrix.toLpLin_one]
    rfl
  right_inv x := by
    change Matrix.toLpLin 2 2 U.1
        (Matrix.toLpLin 2 2 (star U.1) x) = x
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same,
      U.property.2, Matrix.toLpLin_one]
    rfl

theorem unitaryMulVecLinearEquiv_inner {k : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x y : EuclideanSpace ℂ (Fin k)) :
    ⟪unitaryMulVecLinearEquiv U x,
      unitaryMulVecLinearEquiv U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [unitaryMulVecLinearEquiv,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (U.1.mulVec y) ⬝ᵥ star (U.1.mulVec x) = y ⬝ᵥ star x
  have hU : U.1ᴴ * U.1 = 1 := U.property.1
  rw [Matrix.star_mulVec, dotProduct_comm,
    Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, hU,
    Matrix.vecMul_one, dotProduct_comm]

/-- Isometric form of unitary matrix-vector multiplication. -/
def unitaryMulVecIsometryEquiv {k : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin k) :=
  LinearEquiv.isometryOfInner (𝕜 := ℂ) (unitaryMulVecLinearEquiv U)
    (unitaryMulVecLinearEquiv_inner U)

@[simp] theorem unitaryMulVecIsometryEquiv_apply {k : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x : EuclideanSpace ℂ (Fin k)) (i : Fin k) :
    unitaryMulVecIsometryEquiv U x i = U.1.mulVec x i := rfl

/-! ## Local-unitary action on a bipartite vector -/

/-- A column of a bipartite vector, viewed as an element of `ℂ^k`. -/
def bipartiteColumn (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) (j : Fin m) :
    EuclideanSpace ℂ (Fin k) :=
  WithLp.toLp 2 (fun i ↦ x (i, j))

@[simp] theorem bipartiteColumn_apply (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) (j : Fin m) (i : Fin k) :
    bipartiteColumn k m x j i = x (i, j) := rfl

/-- Apply a unitary to the first tensor factor. -/
def bipartiteLocalUnitaryLinearEquiv {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    EuclideanSpace ℂ (Fin k × Fin m) ≃ₗ[ℂ]
      EuclideanSpace ℂ (Fin k × Fin m) where
  toFun x := WithLp.toLp 2 (fun p ↦
    unitaryMulVecLinearEquiv U (bipartiteColumn k m x p.2) p.1)
  invFun x := WithLp.toLp 2 (fun p ↦
    (unitaryMulVecLinearEquiv U).symm (bipartiteColumn k m x p.2) p.1)
  map_add' x y := by
    ext p
    change unitaryMulVecLinearEquiv U
        (bipartiteColumn k m (x + y) p.2) p.1 =
      unitaryMulVecLinearEquiv U (bipartiteColumn k m x p.2) p.1 +
        unitaryMulVecLinearEquiv U (bipartiteColumn k m y p.2) p.1
    have hcol :
        bipartiteColumn k m (x + y) p.2 =
          bipartiteColumn k m x p.2 + bipartiteColumn k m y p.2 := by
      ext i
      rfl
    rw [hcol, map_add]
    rfl
  map_smul' c x := by
    ext p
    change unitaryMulVecLinearEquiv U
        (bipartiteColumn k m (c • x) p.2) p.1 =
      c * unitaryMulVecLinearEquiv U (bipartiteColumn k m x p.2) p.1
    have hcol :
        bipartiteColumn k m (c • x) p.2 =
          c • bipartiteColumn k m x p.2 := by
      ext i
      rfl
    rw [hcol, map_smul]
    rfl
  left_inv x := by
    ext p
    have h := (unitaryMulVecLinearEquiv U).symm_apply_apply
      (bipartiteColumn k m x p.2)
    exact congrFun (congrArg WithLp.ofLp h) p.1
  right_inv x := by
    ext p
    have h := (unitaryMulVecLinearEquiv U).apply_symm_apply
      (bipartiteColumn k m x p.2)
    exact congrFun (congrArg WithLp.ofLp h) p.1

@[simp] theorem bipartiteLocalUnitaryLinearEquiv_apply {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x : EuclideanSpace ℂ (Fin k × Fin m)) (i : Fin k) (j : Fin m) :
    bipartiteLocalUnitaryLinearEquiv U x (i, j) =
      unitaryMulVecLinearEquiv U (bipartiteColumn k m x j) i := rfl

theorem bipartiteLocalUnitaryLinearEquiv_inner {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x y : EuclideanSpace ℂ (Fin k × Fin m)) :
    ⟪bipartiteLocalUnitaryLinearEquiv U x,
      bipartiteLocalUnitaryLinearEquiv U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  simpa only [bipartiteLocalUnitaryLinearEquiv_apply, bipartiteColumn,
    unitaryMulVecLinearEquiv, RCLike.inner_apply, PiLp.inner_apply] using
      unitaryMulVecLinearEquiv_inner U
        (bipartiteColumn k m x j) (bipartiteColumn k m y j)

/-- Isometric local-unitary action on the first tensor factor. -/
def bipartiteLocalUnitaryIsometryEquiv {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    EuclideanSpace ℂ (Fin k × Fin m) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin k × Fin m) :=
  LinearEquiv.isometryOfInner (𝕜 := ℂ)
    (bipartiteLocalUnitaryLinearEquiv U)
    (bipartiteLocalUnitaryLinearEquiv_inner U)

@[simp] theorem bipartiteLocalUnitaryIsometryEquiv_apply {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x : EuclideanSpace ℂ (Fin k × Fin m)) (i : Fin k) (j : Fin m) :
    bipartiteLocalUnitaryIsometryEquiv U x (i, j) =
      U.1.mulVec (bipartiteColumn k m x j) i := rfl

set_option maxHeartbeats 800000 in
theorem continuous_bipartiteLocalUnitaryIsometryEquiv (k m : ℕ) :
    Continuous (fun z : unitary (Matrix (Fin k) (Fin k) ℂ) ×
      EuclideanSpace ℂ (Fin k × Fin m) ↦
        bipartiteLocalUnitaryIsometryEquiv z.1 z.2) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : unitary (Matrix (Fin k) (Fin k) ℂ) ×
      EuclideanSpace ℂ (Fin k × Fin m) ↦
    (fun p : Fin k × Fin m ↦
      Matrix.mulVec (z.1 : Matrix (Fin k) (Fin k) ℂ)
        (fun i : Fin k ↦ z.2 (i, p.2)) p.1))
  fun_prop

/-! ## Flattening the pure sphere as `ℂ^k ⊗ ℂ^m` -/

/-- Split the first tensor index into the initial `m` rows and the remaining
`k-m` rows. -/
def grassmannRowSplitEquiv (k m : ℕ) (hmk : m ≤ k) :
    Fin m ⊕ Fin (k - m) ≃ Fin k :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hmk))

/-- Coordinate equivalence from the flat `(k-m)m + m²` ordering used by the
pure-sphere Laplace theorem to the bipartite `k × m` ordering.  The initial
flat block is sent to the last `k-m` rows. -/
def grassmannFlatToBipartiteIndexEquiv (k m : ℕ) (hmk : m ≤ k) :
    Fin (((k - m) * m) + (m * m)) ≃ Fin k × Fin m :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr finProdFinEquiv.symm finProdFinEquiv.symm) |>.trans
    (Equiv.sumComm _ _) |>.trans
    (Equiv.sumProdDistrib (Fin m) (Fin (k - m)) (Fin m)).symm |>.trans
    (Equiv.prodCongr (grassmannRowSplitEquiv k m hmk) (Equiv.refl (Fin m)))

@[simp] theorem grassmannFlatToBipartiteIndexEquiv_apply_castAdd
    (k m : ℕ) (hmk : m ≤ k) (a : Fin ((k - m) * m)) :
    grassmannFlatToBipartiteIndexEquiv k m hmk
        (Fin.castAdd (m * m) a) =
      (grassmannRowSplitEquiv k m hmk
          (Sum.inr (finProdFinEquiv.symm a).1),
        (finProdFinEquiv.symm a).2) := by
  simp [grassmannFlatToBipartiteIndexEquiv, grassmannRowSplitEquiv]

@[simp] theorem grassmannFlatToBipartiteIndexEquiv_symm_apply_complement
    (k m : ℕ) (hmk : m ≤ k) (i : Fin (k - m)) (j : Fin m) :
    (grassmannFlatToBipartiteIndexEquiv k m hmk).symm
        (grassmannRowSplitEquiv k m hmk (Sum.inr i), j) =
      Fin.castAdd (m * m) (finProdFinEquiv (i, j)) := by
  apply (grassmannFlatToBipartiteIndexEquiv k m hmk).injective
  simp

/-- The preceding coordinate equivalence as a complex-linear isometry. -/
noncomputable def grassmannFlatToBipartiteComplexIsometryEquiv
    (k m : ℕ) (hmk : m ≤ k) :
    GrassmannPureSphereSpace k m ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin k × Fin m) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (grassmannFlatToBipartiteIndexEquiv k m hmk)

@[simp] theorem grassmannFlatToBipartiteComplexIsometryEquiv_apply_complement
    (k m : ℕ) (hmk : m ≤ k) (x : GrassmannPureSphereSpace k m)
    (i : Fin (k - m)) (j : Fin m) :
    grassmannFlatToBipartiteComplexIsometryEquiv k m hmk x
        (grassmannRowSplitEquiv k m hmk (Sum.inr i), j) =
      x (Fin.castAdd (m * m) (finProdFinEquiv (i, j))) := by
  simp [grassmannFlatToBipartiteComplexIsometryEquiv]

/-- A complex-linear isometry between possibly different spaces, regarded as
a real-linear isometry without changing its underlying function. -/
noncomputable def complexLinearIsometryEquivToRealBetween
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) : E ≃ₗᵢ[ℝ] F where
  toLinearEquiv := e.toLinearEquiv.restrictScalars ℝ
  norm_map' := e.norm_map

@[simp] theorem complexLinearIsometryEquivToRealBetween_apply
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (e : E ≃ₗᵢ[ℂ] F) (x : E) :
    complexLinearIsometryEquivToRealBetween e x = e x := rfl

/-- Conjugate the local-unitary action through the flat coordinate ordering. -/
noncomputable def grassmannFlatLocalUnitaryIsometryEquiv
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    GrassmannPureSphereSpace k m ≃ₗᵢ[ℝ]
      GrassmannPureSphereSpace k m :=
  (complexLinearIsometryEquivToRealBetween
      (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk)).trans
    ((complexLinearIsometryEquivToRealBetween
      (bipartiteLocalUnitaryIsometryEquiv U)).trans
      (complexLinearIsometryEquivToRealBetween
        (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk).symm))

theorem grassmannFlatLocalUnitaryIsometryEquiv_intertwines
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x : GrassmannPureSphereSpace k m) :
    grassmannFlatToBipartiteComplexIsometryEquiv k m hmk
        (grassmannFlatLocalUnitaryIsometryEquiv hmk U x) =
      bipartiteLocalUnitaryIsometryEquiv U
        (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk x) := by
  simp [grassmannFlatLocalUnitaryIsometryEquiv,
    complexLinearIsometryEquivToRealBetween]
  rfl

/-- The uniform sphere law is invariant under every flattened local unitary. -/
theorem uniformSphereSurfaceMeasure_map_grassmannFlatLocalUnitary
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    [Nontrivial (GrassmannPureSphereSpace k m)] :
    Measure.map
        (unitSphereLinearIsometryAction
          (grassmannFlatLocalUnitaryIsometryEquiv hmk U))
        (LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m)) =
      LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m) := by
  simpa only [LogdetLean.uniformSphereSurfaceMeasure,
    normalizedHaarSphereLaw] using
      normalizedHaarSphereLaw_map_linearIsometry
        (grassmannFlatLocalUnitaryIsometryEquiv hmk U)

/-- Integral form of the preceding sphere invariance. -/
theorem integral_comp_uniformSphere_grassmannFlatLocalUnitary
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    [Nontrivial (GrassmannPureSphereSpace k m)]
    (f : sphere (0 : GrassmannPureSphereSpace k m) 1 → ℝ)
    (hf : AEStronglyMeasurable f
      (LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m))) :
    (∫ u, f (unitSphereLinearIsometryAction
        (grassmannFlatLocalUnitaryIsometryEquiv hmk U) u)
      ∂LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m)) =
      ∫ u, f u ∂LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m) := by
  let e := grassmannFlatLocalUnitaryIsometryEquiv hmk U
  let μ := LogdetLean.uniformSphereSurfaceMeasure
    (E := GrassmannPureSphereSpace k m)
  have he : Measurable (unitSphereLinearIsometryAction e) :=
    measurable_unitSphereLinearIsometryAction e
  have hfmap : AEStronglyMeasurable f
      (Measure.map (unitSphereLinearIsometryAction e) μ) := by
    rw [show Measure.map (unitSphereLinearIsometryAction e) μ = μ by
      exact uniformSphereSurfaceMeasure_map_grassmannFlatLocalUnitary hmk U]
    exact hf
  calc
    (∫ u, f (unitSphereLinearIsometryAction e u) ∂μ) =
        ∫ u, f u ∂Measure.map (unitSphereLinearIsometryAction e) μ := by
      symm
      exact integral_map he.aemeasurable hfmap
    _ = ∫ u, f u ∂μ := by
      rw [show Measure.map (unitSphereLinearIsometryAction e) μ = μ by
        exact uniformSphereSurfaceMeasure_map_grassmannFlatLocalUnitary hmk U]

/-! ## Packing a rank-at-most-`m` spectrum into the initial block -/

/-- A function on `Fin k` with support cardinality at most `m` can be
permuted so all of its nonzero entries occur among the first `m` slots. -/
theorem exists_permutation_support_in_initial
    {k m : ℕ} (hmk : m ≤ k) (f : Fin k → ℝ)
    (hcard : Fintype.card {i : Fin k // f i ≠ 0} ≤ m) :
    ∃ sigma : Equiv.Perm (Fin k),
      ∀ i : Fin k, f i ≠ 0 → (sigma i).val < m := by
  classical
  let s : Finset (Fin k) := Finset.univ.filter (fun i ↦ f i ≠ 0)
  let r : ℕ := s.card
  have hrsupport : r = Fintype.card {i : Fin k // f i ≠ 0} := by
    dsimp only [r, s]
    rw [Fintype.card_subtype]
  have hrm : r ≤ m := by
    rw [hrsupport]
    exact hcard
  have hrk : r ≤ k := hrm.trans hmk
  let t : Finset (Fin k) :=
    Finset.univ.map (Fin.castLEEmb hrk)
  have htcard : t.card = r := by
    simp [t]
  obtain ⟨sigma, hsigma⟩ :=
    Equiv.Perm.exists_map_finset_eq s t (by simpa [r] using htcard.symm)
  refine ⟨sigma, ?_⟩
  intro i hi
  have his : i ∈ s := by
    simp [s, hi]
  have hsigmai : sigma i ∈ t := by
    rw [← hsigma]
    exact Finset.mem_map.mpr ⟨i, his, rfl⟩
  rcases Finset.mem_map.mp hsigmai with ⟨j, hj, hj_eq⟩
  rw [← hj_eq]
  exact (Fin.is_lt j).trans_le hrm

/-- For the permutation supplied above, every reordered slot outside the
first `m` coordinates is zero. -/
theorem reordered_eq_zero_of_support_in_initial
    {k m : ℕ} (f : Fin k → ℝ) (sigma : Equiv.Perm (Fin k))
    (hsigma : ∀ i : Fin k, f i ≠ 0 → (sigma i).val < m)
    (j : Fin k) (hj : m ≤ j.val) :
    f (sigma.symm j) = 0 := by
  by_contra hne
  have hlt := hsigma (sigma.symm j) hne
  rw [sigma.apply_symm_apply] at hlt
  exact (not_lt_of_ge hj) hlt

/-- Restricting a reordered support-at-most-`m` vector to the first `m`
slots preserves its total sum. -/
theorem sum_initial_reordered_eq_sum
    {k m : ℕ} (hmk : m ≤ k) (f : Fin k → ℝ)
    (sigma : Equiv.Perm (Fin k))
    (hsigma : ∀ i : Fin k, f i ≠ 0 → (sigma i).val < m) :
    (∑ i : Fin m, f (sigma.symm (Fin.castLE hmk i))) = ∑ j : Fin k, f j := by
  let e := grassmannRowSplitEquiv k m hmk
  calc
    (∑ i : Fin m, f (sigma.symm (Fin.castLE hmk i))) =
        (∑ z : Fin m ⊕ Fin (k - m), f (sigma.symm (e z))) := by
      have heinl (i : Fin m) : e (Sum.inl i) = Fin.castLE hmk i := by
        apply Fin.ext
        simp [e, grassmannRowSplitEquiv]
      have htail :
          (∑ j : Fin (k - m), f (sigma.symm (e (Sum.inr j)))) = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        apply reordered_eq_zero_of_support_in_initial f sigma hsigma
        simp [e, grassmannRowSplitEquiv]
      rw [Fintype.sum_sum_type, htail, add_zero]
      simp_rw [heinl]
    _ = ∑ j : Fin k, f (sigma.symm j) := by
      simpa using e.sum_comp (fun j : Fin k ↦ f (sigma.symm j))
    _ = ∑ j : Fin k, f j := by
      simpa using sigma.symm.sum_comp f

/-! ## The reduced state of a bipartite vector -/

/-- Regard a bipartite Euclidean vector as its `k × m` coefficient matrix. -/
def bipartiteCoefficientMatrix (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    Matrix (Fin k) (Fin m) ℂ :=
  fun i j ↦ x (i, j)

/-- Reduced positive matrix on the first (`Fin k`) tensor factor. -/
def bipartiteReducedState (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    Matrix (Fin k) (Fin k) ℂ :=
  bipartiteCoefficientMatrix k m x *
    (bipartiteCoefficientMatrix k m x)ᴴ

/-- The reduced matrix is positive semidefinite. -/
theorem bipartiteReducedState_posSemidef (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    (bipartiteReducedState k m x).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose
    (bipartiteCoefficientMatrix k m x)

/-- The reduced matrix has rank at most the ancilla dimension `m`. -/
theorem bipartiteReducedState_rank_le (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    (bipartiteReducedState k m x).rank ≤ m := by
  rw [bipartiteReducedState, Matrix.rank_self_mul_conjTranspose]
  exact Matrix.rank_le_width _

/-- The trace of the reduced matrix is exactly the squared norm of the
bipartite vector. -/
theorem bipartiteReducedState_trace (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    (bipartiteReducedState k m x).trace = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [bipartiteReducedState, bipartiteCoefficientMatrix,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  simp_rw [← starRingEnd_apply, Complex.mul_conj']
  rw [Fintype.sum_prod_type]
  push_cast
  rfl

/-- Applying a local unitary to the first tensor factor left-multiplies the
coefficient matrix. -/
theorem bipartiteCoefficientMatrix_localUnitary
    {k m : ℕ} (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    bipartiteCoefficientMatrix k m
        (bipartiteLocalUnitaryIsometryEquiv U x) =
      U.1 * bipartiteCoefficientMatrix k m x := by
  ext i j
  simp only [bipartiteCoefficientMatrix,
    bipartiteLocalUnitaryIsometryEquiv_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct, bipartiteColumn_apply]

/-- The reduced-state eigenvalues sum to the squared norm of the pure
bipartite vector. -/
theorem bipartiteReducedState_eigenvalues_sum_eq_norm_sq (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    (∑ i : Fin k,
        (bipartiteReducedState_posSemidef k m x).isHermitian.eigenvalues i) =
      ‖x‖ ^ 2 := by
  let hA := (bipartiteReducedState_posSemidef k m x).isHermitian
  have htrace := hA.trace_eq_sum_eigenvalues
  rw [bipartiteReducedState_trace] at htrace
  have hre := congrArg Complex.re htrace
  rw [Complex.re_sum] at hre
  convert hre.symm using 1
  · simp [hA]
  · exact (Complex.ofReal_re (‖x‖ ^ 2)).symm

/-- Pointwise rank control supplies a padded `Fin m` spectrum of the reduced
state whose weights retain the exact total mass.  The choice is existential
and is never made as a measurable function of `x`. -/
theorem exists_bipartiteReducedState_initialSpectrum
    {k m : ℕ} (hmk : m ≤ k)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    ∃ (sigma : Equiv.Perm (Fin k)) (lambda : Fin m → ℝ),
      (∀ i : Fin m,
        lambda i =
          (bipartiteReducedState_posSemidef k m x).isHermitian.eigenvalues
            (sigma.symm (Fin.castLE hmk i))) ∧
      (∑ i, lambda i) = ‖x‖ ^ 2 := by
  let hA := (bipartiteReducedState_posSemidef k m x).isHermitian
  have hcard : Fintype.card {i : Fin k // hA.eigenvalues i ≠ 0} ≤ m := by
    rw [← hA.rank_eq_card_non_zero_eigs]
    exact bipartiteReducedState_rank_le k m x
  obtain ⟨sigma, hsigma⟩ :=
    exists_permutation_support_in_initial hmk hA.eigenvalues hcard
  let lambda : Fin m → ℝ := fun i ↦
    hA.eigenvalues (sigma.symm (Fin.castLE hmk i))
  refine ⟨sigma, lambda, fun i ↦ rfl, ?_⟩
  calc
    (∑ i, lambda i) = ∑ j : Fin k, hA.eigenvalues j := by
      exact sum_initial_reordered_eq_sum hmk hA.eigenvalues sigma hsigma
    _ = ‖x‖ ^ 2 :=
      bipartiteReducedState_eigenvalues_sum_eq_norm_sq k m x

/-! ## Reindexed spectral matrix -/

/-- Conjugating a correspondingly reindexed diagonal by a permutation
unitary restores the original diagonal. -/
theorem permutationUnitary_conjugate_reindexed_diagonal
    {k : ℕ} (sigma : Equiv.Perm (Fin k)) (d : Fin k → ℝ) :
    Unitary.conjStarAlgAut ℂ _ (permutationUnitary sigma)
        (Matrix.diagonal
          (RCLike.ofReal ∘ d ∘ sigma.symm)) =
      Matrix.diagonal (RCLike.ofReal ∘ d) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Unitary.conjStarAlgAut_apply, permutationUnitary,
      Matrix.mul_apply, Matrix.diagonal_apply]
  · simp [Unitary.conjStarAlgAut_apply, permutationUnitary,
      Matrix.mul_apply, Matrix.diagonal_apply, hij]

/-- The reduced state diagonalized after moving all nonzero eigenvalues into
the initial block. -/
theorem bipartiteReducedState_reindexed_spectral
    {k m : ℕ} (x : EuclideanSpace ℂ (Fin k × Fin m))
    (sigma : Equiv.Perm (Fin k)) :
    let hA := (bipartiteReducedState_posSemidef k m x).isHermitian
    bipartiteReducedState k m x =
      Unitary.conjStarAlgAut ℂ _
        (hA.eigenvectorUnitary * permutationUnitary sigma)
        (Matrix.diagonal
          (RCLike.ofReal ∘ hA.eigenvalues ∘ sigma.symm)) := by
  let hA := (bipartiteReducedState_posSemidef k m x).isHermitian
  dsimp only
  calc
    bipartiteReducedState k m x =
        Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues)) :=
      hA.spectral_theorem
    _ = Unitary.conjStarAlgAut ℂ _ hA.eigenvectorUnitary
        (Unitary.conjStarAlgAut ℂ _ (permutationUnitary sigma)
          (Matrix.diagonal
            (RCLike.ofReal ∘ hA.eigenvalues ∘ sigma.symm))) := by
      rw [permutationUnitary_conjugate_reindexed_diagonal]
    _ = Unitary.conjStarAlgAut ℂ _
        (hA.eigenvectorUnitary * permutationUnitary sigma)
        (Matrix.diagonal
          (RCLike.ofReal ∘ hA.eigenvalues ∘ sigma.symm)) := by
      rw [Unitary.conjStarAlgAut_mul_apply]

/-! ## Complementary row energy -/

/-- Complementary diagonal mass of a square matrix. -/
def matrixComplementDiagonalMass (k m : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) : ℝ :=
  ∑ i : Fin k, if m ≤ i.val then (A i i).re else 0

/-- Complementary row mass of a bipartite vector. -/
def bipartiteComplementMass (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) : ℝ :=
  ∑ i : Fin k, if m ≤ i.val then
    ∑ j : Fin m, Complex.normSq (x (i, j)) else 0

theorem continuous_bipartiteComplementMass (k m : ℕ) :
    Continuous (bipartiteComplementMass k m) := by
  unfold bipartiteComplementMass
  refine continuous_finsetSum Finset.univ ?_
  intro i hi
  by_cases him : m ≤ i.val
  · simp only [him, if_true]
    refine continuous_finsetSum Finset.univ ?_
    intro j hj
    fun_prop
  · simpa [him] using
      (continuous_const : Continuous
        (fun _ : EuclideanSpace ℂ (Fin k × Fin m) ↦ (0 : ℝ)))

/-- Reindex complementary row mass by the explicit `Fin (k-m)` tail. -/
theorem bipartiteComplementMass_eq_sum_complementRows
    {k m : ℕ} (hmk : m ≤ k)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    bipartiteComplementMass k m x =
      ∑ i : Fin (k - m), ∑ j : Fin m,
        Complex.normSq
          (x (grassmannRowSplitEquiv k m hmk (Sum.inr i), j)) := by
  unfold bipartiteComplementMass
  let e := grassmannRowSplitEquiv k m hmk
  calc
    (∑ i : Fin k, if m ≤ i.val then
        ∑ j : Fin m, Complex.normSq (x (i, j)) else 0) =
        ∑ z : Fin m ⊕ Fin (k - m), if m ≤ (e z).val then
          ∑ j : Fin m, Complex.normSq (x (e z, j)) else 0 := by
      exact (e.sum_comp (fun i : Fin k ↦ if m ≤ i.val then
        ∑ j : Fin m, Complex.normSq (x (i, j)) else 0)).symm
    _ = ∑ i : Fin (k - m), ∑ j : Fin m,
        Complex.normSq
          (x (grassmannRowSplitEquiv k m hmk (Sum.inr i), j)) := by
      rw [Fintype.sum_sum_type]
      have hhead : (∑ i : Fin m, if m ≤ (e (Sum.inl i)).val then
          ∑ j : Fin m, Complex.normSq (x (e (Sum.inl i), j)) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hlt : (e (Sum.inl i)).val < m := by
          simp [e, grassmannRowSplitEquiv]
        simp [Nat.not_le.mpr hlt]
      rw [hhead, zero_add]
      apply Finset.sum_congr rfl
      intro i hi
      have hge : m ≤ (e (Sum.inr i)).val := by
        simp [e, grassmannRowSplitEquiv]
      simp [hge, e]

/-- The fixed-subspace projection energy in the flat pure-sphere ordering is
exactly the complementary-row mass after converting to bipartite
coordinates. -/
theorem grassmannPureSphereProjection_norm_sq_eq_bipartiteComplementMass
    {k m : ℕ} (hmk : m ≤ k) (x : GrassmannPureSphereSpace k m) :
    ‖(grassmannPureSphereComplementSubspace k m).orthogonalProjectionOnto x‖ ^ 2 =
      bipartiteComplementMass k m
        (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk x) := by
  rw [complexInitialProjection_norm_sq]
  calc
    (∑ a : Fin ((k - m) * m),
        Complex.normSq (x (Fin.castAdd (m * m) a))) =
        ∑ p : Fin (k - m) × Fin m,
          Complex.normSq
            (x (Fin.castAdd (m * m) (finProdFinEquiv p))) := by
      symm
      exact finProdFinEquiv.sum_comp
        (fun a : Fin ((k - m) * m) ↦
          Complex.normSq (x (Fin.castAdd (m * m) a)))
    _ = ∑ i : Fin (k - m), ∑ j : Fin m,
        Complex.normSq
          ((grassmannFlatToBipartiteComplexIsometryEquiv k m hmk x)
            (grassmannRowSplitEquiv k m hmk (Sum.inr i), j)) := by
      rw [Fintype.sum_prod_type]
      simp
    _ = bipartiteComplementMass k m
        (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk x) :=
      (bipartiteComplementMass_eq_sum_complementRows hmk _).symm

/-- Complementary row mass is the complementary diagonal mass of the
reduced state. -/
theorem bipartiteComplementMass_eq_reducedDiagonal (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    bipartiteComplementMass k m x =
      matrixComplementDiagonalMass k m (bipartiteReducedState k m x) := by
  unfold bipartiteComplementMass matrixComplementDiagonalMass
  apply Finset.sum_congr rfl
  intro i hi
  by_cases him : m ≤ i.val
  · simp only [him, if_true, bipartiteReducedState,
      bipartiteCoefficientMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← starRingEnd_apply, Complex.mul_conj']
    rw [Complex.normSq_eq_norm_sq]
    norm_num [pow_two, Complex.mul_re]
  · simp [him]

/-- The reduced state transforms by unitary conjugation under a local
unitary on the first tensor factor. -/
theorem bipartiteReducedState_localUnitary
    {k m : ℕ} (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    bipartiteReducedState k m
        (bipartiteLocalUnitaryIsometryEquiv U x) =
      Unitary.conjStarAlgAut ℂ _ U (bipartiteReducedState k m x) := by
  rw [bipartiteReducedState, bipartiteCoefficientMatrix_localUnitary,
    bipartiteReducedState]
  simp only [Unitary.conjStarAlgAut_apply, Matrix.conjTranspose_mul,
    ← Unitary.coe_star]
  change
    (U.1 * bipartiteCoefficientMatrix k m x) *
        ((bipartiteCoefficientMatrix k m x)ᴴ * U.1ᴴ) =
      U.1 * (bipartiteCoefficientMatrix k m x *
        (bipartiteCoefficientMatrix k m x)ᴴ) * U.1ᴴ
  calc
    (U.1 * bipartiteCoefficientMatrix k m x) *
        ((bipartiteCoefficientMatrix k m x)ᴴ * U.1ᴴ) =
      ((U.1 * bipartiteCoefficientMatrix k m x) *
        (bipartiteCoefficientMatrix k m x)ᴴ) * U.1ᴴ :=
        (Matrix.mul_assoc (U.1 * bipartiteCoefficientMatrix k m x)
          (bipartiteCoefficientMatrix k m x)ᴴ U.1ᴴ).symm
    _ = U.1 * (bipartiteCoefficientMatrix k m x *
        (bipartiteCoefficientMatrix k m x)ᴴ) * U.1ᴴ := by
      exact congrArg
        (fun A : Matrix (Fin k) (Fin k) ℂ ↦ A * U.1ᴴ)
        (Matrix.mul_assoc U.1 (bipartiteCoefficientMatrix k m x)
          (bipartiteCoefficientMatrix k m x)ᴴ)

/-- Complementary mass of one arbitrary unitary column. -/
def unitaryComplementColumnMassAll (k m : ℕ)
    (W : unitary (Matrix (Fin k) (Fin k) ℂ)) (j : Fin k) : ℝ :=
  ∑ i : Fin k, if m ≤ i.val then Complex.normSq (W.1 i j) else 0

theorem unitaryComplementColumnMassAll_castLE
    {k m : ℕ} (hmk : m ≤ k)
    (W : unitary (Matrix (Fin k) (Fin k) ℂ)) (j : Fin m) :
    unitaryComplementColumnMassAll k m W (Fin.castLE hmk j) =
      canonicalUnitaryComplementColumnMass k m hmk W j := rfl

theorem re_mul_ofReal_mul_star (z : ℂ) (a : ℝ) :
    (z * (a : ℂ) * star z).re = a * Complex.normSq z := by
  rw [← starRingEnd_apply]
  calc
    (z * (a : ℂ) * conj z).re =
        ((a : ℂ) * (z * conj z)).re := by ring
    _ = ((a : ℂ) * (Complex.normSq z : ℂ)).re := by
      rw [Complex.mul_conj]
    _ = a * Complex.normSq z := by norm_num

/-- Complementary diagonal mass of a unitary conjugate of a real diagonal
is the spectrum-weighted sum of complementary column masses. -/
theorem matrixComplementDiagonalMass_conj_diagonal
    (k m : ℕ) (W : unitary (Matrix (Fin k) (Fin k) ℂ))
    (g : Fin k → ℝ) :
    matrixComplementDiagonalMass k m
        (Unitary.conjStarAlgAut ℂ _ W
          (Matrix.diagonal (RCLike.ofReal ∘ g))) =
      ∑ j : Fin k, g j * unitaryComplementColumnMassAll k m W j := by
  unfold matrixComplementDiagonalMass unitaryComplementColumnMassAll
  simp only [Unitary.conjStarAlgAut_apply, Matrix.mul_apply,
    Matrix.star_apply]
  simp_rw [Matrix.diagonal_apply]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Function.comp_apply]
  calc
    (∑ i : Fin k, if m ≤ i.val then
        ((∑ j : Fin k, W.1 i j * (g j : ℂ) * star (W.1 i j))).re
      else 0) =
        ∑ i : Fin k, if m ≤ i.val then
          ∑ j : Fin k, g j * Complex.normSq (W.1 i j) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases him : m ≤ i.val
      · simp only [him, if_true, Complex.re_sum]
        apply Finset.sum_congr rfl
        intro j hj
        exact re_mul_ofReal_mul_star (W.1 i j) (g j)
      · simp [him]
    _ = ∑ i : Fin k, ∑ j : Fin k,
        if m ≤ i.val then g j * Complex.normSq (W.1 i j) else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases him : m ≤ i.val <;> simp [him]
    _ = ∑ j : Fin k, ∑ i : Fin k,
        if m ≤ i.val then g j * Complex.normSq (W.1 i j) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin k, g j *
        ∑ i : Fin k, if m ≤ i.val then
          Complex.normSq (W.1 i j) else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases him : m ≤ i.val <;> simp [him]

/-- If a real diagonal is supported in the first `m` coordinates, its
weighted complementary-column sum is exactly the canonical weighted
observable on those first coordinates. -/
theorem sum_weightedColumnMass_eq_weightedCanonical
    {k m : ℕ} (hmk : m ≤ k) (g : Fin k → ℝ)
    (W : unitary (Matrix (Fin k) (Fin k) ℂ))
    (hzero : ∀ j : Fin k, m ≤ j.val → g j = 0) :
    (∑ j : Fin k, g j * unitaryComplementColumnMassAll k m W j) =
      weightedCanonicalUnitaryComplementOverlap k m hmk
        (fun i : Fin m ↦ g (Fin.castLE hmk i)) W := by
  let f : Fin k → ℝ := fun j ↦
    g j * unitaryComplementColumnMassAll k m W j
  have hsupport : ∀ j : Fin k, f j ≠ 0 →
      ((Equiv.refl (Fin k)) j).val < m := by
    intro j hj
    simp only [Equiv.refl_apply]
    by_contra hnot
    have hjm : m ≤ j.val := Nat.le_of_not_gt hnot
    have hgj : g j = 0 := hzero j hjm
    exact hj (by simp [f, hgj])
  have hsum := sum_initial_reordered_eq_sum hmk f
    (Equiv.refl (Fin k)) hsupport
  rw [← hsum]
  unfold weightedCanonicalUnitaryComplementOverlap f
  simp only [Equiv.refl_symm, Equiv.refl_apply,
    unitaryComplementColumnMassAll_castLE]

/-- The reduced-state eigenvalue function after a fixed spectral
reindexing. -/
def bipartiteReindexedEigenvalue (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m))
    (sigma : Equiv.Perm (Fin k)) (j : Fin k) : ℝ :=
  (bipartiteReducedState_posSemidef k m x).isHermitian.eigenvalues
    (sigma.symm j)

/-- The fixed unitary that diagonalizes the reduced state after the same
spectral reindexing. -/
def bipartiteSpectralReindexUnitary (k m : ℕ)
    (x : EuclideanSpace ℂ (Fin k × Fin m))
    (sigma : Equiv.Perm (Fin k)) :
    unitary (Matrix (Fin k) (Fin k) ℂ) :=
  (bipartiteReducedState_posSemidef k m x).isHermitian.eigenvectorUnitary *
    permutationUnitary sigma

/-- A reduced state admits a reindexing whose spectrum is supported in the
initial `m` coordinates and whose initial block has exactly the squared norm
as total mass. -/
theorem exists_bipartiteReducedState_supportedReindex
    {k m : ℕ} (hmk : m ≤ k)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) :
    ∃ sigma : Equiv.Perm (Fin k),
      (∀ i : Fin k,
        (bipartiteReducedState_posSemidef k m x).isHermitian.eigenvalues i ≠ 0 →
          (sigma i).val < m) ∧
      (∑ i : Fin m, bipartiteReindexedEigenvalue k m x sigma
        (Fin.castLE hmk i)) = ‖x‖ ^ 2 := by
  let hA := (bipartiteReducedState_posSemidef k m x).isHermitian
  have hcard : Fintype.card {i : Fin k // hA.eigenvalues i ≠ 0} ≤ m := by
    rw [← hA.rank_eq_card_non_zero_eigs]
    exact bipartiteReducedState_rank_le k m x
  obtain ⟨sigma, hsigma⟩ :=
    exists_permutation_support_in_initial hmk hA.eigenvalues hcard
  refine ⟨sigma, hsigma, ?_⟩
  change (∑ i : Fin m,
    hA.eigenvalues (sigma.symm (Fin.castLE hmk i))) = ‖x‖ ^ 2
  calc
    (∑ i : Fin m,
        hA.eigenvalues (sigma.symm (Fin.castLE hmk i))) =
        ∑ j : Fin k, hA.eigenvalues j :=
      sum_initial_reordered_eq_sum hmk hA.eigenvalues sigma hsigma
    _ = ‖x‖ ^ 2 :=
      bipartiteReducedState_eigenvalues_sum_eq_norm_sq k m x

/-- After pointwise spectral reindexing, local-unitary complementary mass is
exactly the weighted canonical observable evaluated on a fixed right
translate of the Haar unitary.  This theorem is pointwise in `x`; no
measurable eigenbasis choice is made. -/
theorem bipartiteComplementMass_localUnitary_eq_weightedCanonical
    {k m : ℕ} (hmk : m ≤ k)
    (x : EuclideanSpace ℂ (Fin k × Fin m))
    (sigma : Equiv.Perm (Fin k))
    (hsigma : ∀ i : Fin k,
      (bipartiteReducedState_posSemidef k m x).isHermitian.eigenvalues i ≠ 0 →
        (sigma i).val < m)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    bipartiteComplementMass k m
        (bipartiteLocalUnitaryIsometryEquiv U x) =
      weightedCanonicalUnitaryComplementOverlap k m hmk
        (fun i : Fin m ↦ bipartiteReindexedEigenvalue k m x sigma
          (Fin.castLE hmk i))
        (U * bipartiteSpectralReindexUnitary k m x sigma) := by
  let hA := (bipartiteReducedState_posSemidef k m x).isHermitian
  let V : unitary (Matrix (Fin k) (Fin k) ℂ) :=
    hA.eigenvectorUnitary * permutationUnitary sigma
  let g : Fin k → ℝ := fun j ↦ hA.eigenvalues (sigma.symm j)
  have hzero : ∀ j : Fin k, m ≤ j.val → g j = 0 := by
    intro j hj
    exact reordered_eq_zero_of_support_in_initial hA.eigenvalues sigma
      hsigma j hj
  calc
    bipartiteComplementMass k m
        (bipartiteLocalUnitaryIsometryEquiv U x) =
        matrixComplementDiagonalMass k m
          (bipartiteReducedState k m
            (bipartiteLocalUnitaryIsometryEquiv U x)) :=
      bipartiteComplementMass_eq_reducedDiagonal k m _
    _ = matrixComplementDiagonalMass k m
        (Unitary.conjStarAlgAut ℂ _ U (bipartiteReducedState k m x)) := by
      rw [bipartiteReducedState_localUnitary]
    _ = matrixComplementDiagonalMass k m
        (Unitary.conjStarAlgAut ℂ _ U
          (Unitary.conjStarAlgAut ℂ _ V
            (Matrix.diagonal (RCLike.ofReal ∘ g)))) := by
      rw [bipartiteReducedState_reindexed_spectral x sigma]
      rfl
    _ = matrixComplementDiagonalMass k m
        (Unitary.conjStarAlgAut ℂ _ (U * V)
          (Matrix.diagonal (RCLike.ofReal ∘ g))) := by
      rw [← Unitary.conjStarAlgAut_mul_apply]
    _ = ∑ j : Fin k,
        g j * unitaryComplementColumnMassAll k m (U * V) j :=
      matrixComplementDiagonalMass_conj_diagonal k m (U * V) g
    _ = weightedCanonicalUnitaryComplementOverlap k m hmk
        (fun i : Fin m ↦ g (Fin.castLE hmk i)) (U * V) :=
      sum_weightedColumnMass_eq_weightedCanonical hmk g (U * V) hzero
    _ = weightedCanonicalUnitaryComplementOverlap k m hmk
        (fun i : Fin m ↦ bipartiteReindexedEigenvalue k m x sigma
          (Fin.castLE hmk i))
        (U * bipartiteSpectralReindexUnitary k m x sigma) := rfl

/-- For every fixed unit bipartite vector, the canonical projector Laplace
transform is bounded by the Haar average of the complementary mass along
its local-unitary orbit.  The spectral reindexing is chosen only inside this
pointwise proof. -/
theorem canonicalUnitaryLaplace_le_localUnitaryComplementMass
    {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k)
    (x : EuclideanSpace ℂ (Fin k × Fin m)) (hx : ‖x‖ = 1) :
    (∫ U, Real.exp
        ((-(k : ℝ) / 3) * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
      ∫ U, Real.exp
        (((-(k : ℝ) / 3) * (m : ℝ)) *
          bipartiteComplementMass k m
            (bipartiteLocalUnitaryIsometryEquiv U x))
        ∂unitaryHaarProbability k := by
  obtain ⟨sigma, hsigma, hsum⟩ :=
    exists_bipartiteReducedState_supportedReindex hmk x
  let lambda : Fin m → ℝ := fun i ↦
    bipartiteReindexedEigenvalue k m x sigma (Fin.castLE hmk i)
  let V : unitary (Matrix (Fin k) (Fin k) ℂ) :=
    bipartiteSpectralReindexUnitary k m x sigma
  have hlambda : (∑ i, lambda i) = 1 := by
    change (∑ i : Fin m, bipartiteReindexedEigenvalue k m x sigma
      (Fin.castLE hmk i)) = 1
    rw [hsum, hx]
    norm_num
  let f : unitary (Matrix (Fin k) (Fin k) ℂ) → ℝ := fun U ↦
    Real.exp (((-(k : ℝ) / 3) * (m : ℝ)) *
      weightedCanonicalUnitaryComplementOverlap k m hmk lambda U)
  have hf : Integrable f (unitaryHaarProbability k) := by
    simpa only [f] using
      integrable_exp_mul_weightedCanonicalUnitaryComplementOverlap
        k m hmk lambda ((-(k : ℝ) / 3) * (m : ℝ))
  have hinv : (∫ U, f (U * V) ∂unitaryHaarProbability k) =
      ∫ U, f U ∂unitaryHaarProbability k :=
    integral_comp_unitaryHaarProbability_mul_right
      k V f hf.aestronglyMeasurable
  have hpoint (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
      weightedCanonicalUnitaryComplementOverlap k m hmk lambda (U * V) =
        bipartiteComplementMass k m
          (bipartiteLocalUnitaryIsometryEquiv U x) := by
    exact (bipartiteComplementMass_localUnitary_eq_weightedCanonical
      hmk x sigma hsigma U).symm
  calc
    (∫ U, Real.exp
        ((-(k : ℝ) / 3) * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
        ∫ U, Real.exp
          (((-(k : ℝ) / 3) * (m : ℝ)) *
            weightedCanonicalUnitaryComplementOverlap k m hmk lambda U)
          ∂unitaryHaarProbability k :=
      canonicalUnitaryLaplace_le_weightedOrbit hm hmk lambda
        (-(k : ℝ) / 3) hlambda
    _ = ∫ U, f (U * V) ∂unitaryHaarProbability k := by
      rw [hinv]
    _ = ∫ U, Real.exp
        (((-(k : ℝ) / 3) * (m : ℝ)) *
          bipartiteComplementMass k m
            (bipartiteLocalUnitaryIsometryEquiv U x))
        ∂unitaryHaarProbability k := by
      apply integral_congr_ae
      filter_upwards [] with U
      simp only [f, hpoint]

/-! ## Haar/sphere averaging closes the induced-state bridge -/

/-- The common exponent coefficient for the pure-state comparison. -/
def grassmannPureSphereLaplaceCoefficient (k m : ℕ) : ℝ :=
  -(((k * m : ℕ) : ℝ) / 3)

theorem grassmannPureSphereLaplaceCoefficient_eq (k m : ℕ) :
    grassmannPureSphereLaplaceCoefficient k m =
      (-(k : ℝ) / 3) * (m : ℝ) := by
  unfold grassmannPureSphereLaplaceCoefficient
  push_cast
  ring

/-- Fixed-subspace pure-sphere Laplace integrand. -/
def grassmannPureSphereLaplaceIntegrand (k m : ℕ)
    (u : sphere (0 : GrassmannPureSphereSpace k m) 1) : ℝ :=
  Real.exp (grassmannPureSphereLaplaceCoefficient k m *
    ‖(grassmannPureSphereComplementSubspace k m).orthogonalProjectionOnto
      (u : GrassmannPureSphereSpace k m)‖ ^ 2)

/-- Joint local-unitary/pure-sphere Laplace integrand. -/
def grassmannLocalOrbitLaplaceIntegrand
    {k m : ℕ} (hmk : m ≤ k)
    (z : unitary (Matrix (Fin k) (Fin k) ℂ) ×
      sphere (0 : GrassmannPureSphereSpace k m) 1) : ℝ :=
  Real.exp (grassmannPureSphereLaplaceCoefficient k m *
    bipartiteComplementMass k m
      (bipartiteLocalUnitaryIsometryEquiv z.1
        (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk z.2.1)))

/-- Normalized-coefficient form of the pointwise local-orbit comparison. -/
theorem canonicalUnitaryLaplace_le_localOrbitIntegrand
    {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k)
    (u : sphere (0 : GrassmannPureSphereSpace k m) 1) :
    (∫ U, Real.exp
        (-((k : ℝ) / 3) * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
      ∫ U, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
        ∂unitaryHaarProbability k := by
  have hu : ‖grassmannFlatToBipartiteComplexIsometryEquiv k m hmk
      (u : GrassmannPureSphereSpace k m)‖ = 1 := by
    rw [(grassmannFlatToBipartiteComplexIsometryEquiv k m hmk).norm_map]
    simpa [mem_sphere] using u.2
  have h := canonicalUnitaryLaplace_le_localUnitaryComplementMass
    hm hmk
      (grassmannFlatToBipartiteComplexIsometryEquiv k m hmk
        (u : GrassmannPureSphereSpace k m)) hu
  have hneg : (-(k : ℝ) / 3) = -((k : ℝ) / 3) := by ring
  simpa only [grassmannLocalOrbitLaplaceIntegrand,
    grassmannPureSphereLaplaceCoefficient_eq, hneg] using h

set_option maxHeartbeats 800000 in
theorem continuous_grassmannLocalOrbitLaplaceIntegrand
    {k m : ℕ} (hmk : m ≤ k) :
    Continuous (grassmannLocalOrbitLaplaceIntegrand hmk) := by
  have hinput : Continuous (fun z :
      unitary (Matrix (Fin k) (Fin k) ℂ) ×
        sphere (0 : GrassmannPureSphereSpace k m) 1 ↦
      (z.1, grassmannFlatToBipartiteComplexIsometryEquiv k m hmk z.2.1)) := by
    fun_prop
  have hlocal :=
    (continuous_bipartiteLocalUnitaryIsometryEquiv k m).comp hinput
  have hmass := (continuous_bipartiteComplementMass k m).comp hlocal
  exact Real.continuous_exp.comp (continuous_const.mul hmass)

theorem continuous_grassmannPureSphereLaplaceIntegrand (k m : ℕ) :
    Continuous (grassmannPureSphereLaplaceIntegrand k m) := by
  unfold grassmannPureSphereLaplaceIntegrand
  fun_prop

theorem integrable_grassmannLocalOrbitLaplaceIntegrand
    {k m : ℕ} (hmk : m ≤ k)
    [Nontrivial (GrassmannPureSphereSpace k m)] :
    Integrable (grassmannLocalOrbitLaplaceIntegrand hmk)
      ((unitaryHaarProbability k).prod
        (LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m))) := by
  simpa [IntegrableOn] using
    (continuous_grassmannLocalOrbitLaplaceIntegrand hmk).continuousOn.integrableOn_compact
        (μ := (unitaryHaarProbability k).prod
          (LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m))) isCompact_univ

theorem integrable_grassmannPureSphereLaplaceIntegrand
    (k m : ℕ) [Nontrivial (GrassmannPureSphereSpace k m)] :
    Integrable (grassmannPureSphereLaplaceIntegrand k m)
      (LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m)) := by
  simpa [IntegrableOn] using
    (continuous_grassmannPureSphereLaplaceIntegrand k m).continuousOn.integrableOn_compact
        (μ := LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m)) isCompact_univ

theorem grassmannLocalOrbitLaplaceIntegrand_eq_sphereAction
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (u : sphere (0 : GrassmannPureSphereSpace k m) 1) :
    grassmannLocalOrbitLaplaceIntegrand hmk (U, u) =
      grassmannPureSphereLaplaceIntegrand k m
        (unitSphereLinearIsometryAction
          (grassmannFlatLocalUnitaryIsometryEquiv hmk U) u) := by
  simp only [grassmannLocalOrbitLaplaceIntegrand,
    grassmannPureSphereLaplaceIntegrand,
    unitSphereLinearIsometryAction_coe]
  rw [← grassmannFlatLocalUnitaryIsometryEquiv_intertwines hmk U u.1]
  rw [← grassmannPureSphereProjection_norm_sq_eq_bipartiteComplementMass
    hmk (grassmannFlatLocalUnitaryIsometryEquiv hmk U u.1)]
  rfl

theorem integral_grassmannLocalOrbitLaplaceIntegrand_fixed_unitary
    {k m : ℕ} (hmk : m ≤ k)
    [Nontrivial (GrassmannPureSphereSpace k m)]
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    (∫ u, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
      ∂LogdetLean.uniformSphereSurfaceMeasure
        (E := GrassmannPureSphereSpace k m)) =
      ∫ u, grassmannPureSphereLaplaceIntegrand k m u
        ∂LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m) := by
  calc
    (∫ u, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
        ∂LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m)) =
        ∫ u, grassmannPureSphereLaplaceIntegrand k m
          (unitSphereLinearIsometryAction
            (grassmannFlatLocalUnitaryIsometryEquiv hmk U) u)
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (grassmannLocalOrbitLaplaceIntegrand_eq_sphereAction hmk U)
    _ = ∫ u, grassmannPureSphereLaplaceIntegrand k m u
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m) := by
      exact integral_comp_uniformSphere_grassmannFlatLocalUnitary hmk U _
        (integrable_grassmannPureSphereLaplaceIntegrand k m).aestronglyMeasurable

/-- Averaging the pointwise local-orbit inequality over the pure sphere,
then using Fubini and sphere invariance, gives the exact pure-sphere bridge
inequality without any scientific premise. -/
theorem canonicalUnitaryLaplace_le_pureSphere
    {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k)
    [Nontrivial (GrassmannPureSphereSpace k m)] :
    (∫ U, Real.exp
        (-((k : ℝ) / 3) * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
      ∫ u, grassmannPureSphereLaplaceIntegrand k m u
        ∂LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m) := by
  let L : ℝ := ∫ U, Real.exp
    (-((k : ℝ) / 3) * canonicalUnitaryComplementOverlap k m hmk U)
      ∂unitaryHaarProbability k
  have hFint := integrable_grassmannLocalOrbitLaplaceIntegrand hmk
  have havg : L ≤
      ∫ u, ∫ U, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
          ∂unitaryHaarProbability k
        ∂LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m) := by
    have hmono := integral_mono (integrable_const L)
      hFint.integral_prod_right
      (fun u ↦ canonicalUnitaryLaplace_le_localOrbitIntegrand hm hmk u)
    simpa [L] using hmono
  have hswap :
      (∫ u, ∫ U, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
          ∂unitaryHaarProbability k
        ∂LogdetLean.uniformSphereSurfaceMeasure
          (E := GrassmannPureSphereSpace k m)) =
        ∫ U, ∫ u, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m)
          ∂unitaryHaarProbability k := by
    have huncurry :
        Function.uncurry (fun U u ↦
          grassmannLocalOrbitLaplaceIntegrand hmk (U, u)) =
          grassmannLocalOrbitLaplaceIntegrand hmk := by
      funext z
      rcases z with ⟨U, u⟩
      rfl
    have hFint' : Integrable
        (Function.uncurry (fun U u ↦
          grassmannLocalOrbitLaplaceIntegrand hmk (U, u)))
        ((unitaryHaarProbability k).prod
          (LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m))) := by
      rw [huncurry]
      exact hFint
    exact (integral_integral_swap hFint').symm
  have horbit :
      (∫ U, ∫ u, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m)
        ∂unitaryHaarProbability k) =
        ∫ u, grassmannPureSphereLaplaceIntegrand k m u
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m) := by
    calc
      (∫ U, ∫ u, grassmannLocalOrbitLaplaceIntegrand hmk (U, u)
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m)
        ∂unitaryHaarProbability k) =
          ∫ U, (∫ u, grassmannPureSphereLaplaceIntegrand k m u
            ∂LogdetLean.uniformSphereSurfaceMeasure
              (E := GrassmannPureSphereSpace k m))
            ∂unitaryHaarProbability k := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (integral_grassmannLocalOrbitLaplaceIntegrand_fixed_unitary hmk)
      _ = ∫ u, grassmannPureSphereLaplaceIntegrand k m u
          ∂LogdetLean.uniformSphereSurfaceMeasure
            (E := GrassmannPureSphereSpace k m) := by simp
  simpa only [L] using havg.trans_eq (hswap.trans horbit)

/-- The exact `GrassmannInducedStatePureSphereBridge` proposition is
unconditional. -/
theorem grassmannInducedStatePureSphereBridge
    {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k) :
    GrassmannInducedStatePureSphereBridge k m hm hmk := by
  letI : Nontrivial (GrassmannPureSphereSpace k m) :=
    Module.nontrivial_of_finrank_pos (by
      rw [finrank_complexEuclideanSpace_real_headBlock]
      have hmpos : 0 < m := by omega
      positivity)
  have hneg : (-(k : ℝ) / 3) = -((k : ℝ) / 3) := by ring
  simpa only [GrassmannInducedStatePureSphereBridge, hneg,
    grassmannPureSphereLaplaceIntegrand,
    grassmannPureSphereLaplaceCoefficient] using
    canonicalUnitaryLaplace_le_pureSphere hm hmk

/-- Premise-free canonical quarter-Laplace estimate. -/
theorem canonicalUnitaryQuarterLaplaceBound
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k) :
    CanonicalUnitaryQuarterLaplaceBound k m (by omega) := by
  exact canonicalUnitaryQuarterLaplaceBound_of_inducedStatePureSphereBridge
    hm hkm (grassmannInducedStatePureSphereBridge hm (by omega))

/-- Premise-free Grassmann packing witness at the target cardinality. -/
theorem exists_complexGrassmannPackingWitness_card_eq
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k) :
    ∃ V : ComplexGrassmannPackingWitness k m,
      V.card = grassmannPackingCard k m := by
  exact
    exists_complexGrassmannPackingWitness_card_eq_of_inducedStatePureSphereBridge
      hm hkm (grassmannInducedStatePureSphereBridge hm (by omega))

end

end TomographyOracleCore
