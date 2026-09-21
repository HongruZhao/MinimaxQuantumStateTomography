import TomographyOracleCore.RelativeDesignChoiTensorId

namespace TomographyOracleCore

universe u v w

open scoped CStarAlgebra BigOperators

noncomputable section

local instance choiTensorIdOrderSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance choiTensorIdOrderStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# Complete-positive order and a common untouched identity factor

We first prove the missing finite-dimensional direction of Choi's theorem:
the Choi matrix of a completely positive map is nonnegative.  The proof uses
the defining complete-positivity amplification on the block EPR matrix and
an explicit block-flattening star-algebra map.  It then follows formally that
adjoining the same raw EPR Choi factor preserves a relative-CP sandwich.
-/

/-- Flatten a square matrix of square matrices into a product-indexed square
matrix. -/
def finiteChoiBlockFlatten
    {I : Type u} [Fintype I] [DecidableEq I]
    (M : CStarMatrix I I (CStarMatrix I I ℂ)) :
    CStarMatrix (I × I) (I × I) ℂ :=
  fun ia jb ↦ M ia.1 jb.1 ia.2 jb.2

@[simp] theorem finiteChoiBlockFlatten_apply
    {I : Type u} [Fintype I] [DecidableEq I]
    (M : CStarMatrix I I (CStarMatrix I I ℂ))
    (i a j b : I) :
    finiteChoiBlockFlatten M (i, a) (j, b) = M i j a b := rfl

@[simp] theorem finiteChoiBlockFlatten_zero
    {I : Type u} [Fintype I] [DecidableEq I] :
    finiteChoiBlockFlatten
        (0 : CStarMatrix I I (CStarMatrix I I ℂ)) = 0 := by
  rfl

theorem finiteChoiBlockFlatten_add
    {I : Type u} [Fintype I] [DecidableEq I]
    (M N : CStarMatrix I I (CStarMatrix I I ℂ)) :
    finiteChoiBlockFlatten (M + N) =
      finiteChoiBlockFlatten M + finiteChoiBlockFlatten N := by
  rfl

theorem finiteChoiBlockFlatten_mul
    {I : Type u} [Fintype I] [DecidableEq I]
    (M N : CStarMatrix I I (CStarMatrix I I ℂ)) :
    finiteChoiBlockFlatten (M * N) =
      finiteChoiBlockFlatten M * finiteChoiBlockFlatten N := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp only [finiteChoiBlockFlatten_apply, CStarMatrix.mul_apply,
    cstarMatrix_fintypeSum_apply, Fintype.sum_prod_type]

theorem finiteChoiBlockFlatten_star
    {I : Type u} [Fintype I] [DecidableEq I]
    (M : CStarMatrix I I (CStarMatrix I I ℂ)) :
    finiteChoiBlockFlatten (star M) =
      star (finiteChoiBlockFlatten M) := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  rfl

/-- Block flattening preserves the finite star-positive cone. -/
theorem finiteChoiBlockFlatten_nonneg
    {I : Type u} [Fintype I] [DecidableEq I]
    {M : CStarMatrix I I (CStarMatrix I I ℂ)}
    (hM : 0 ≤ M) :
    0 ≤ finiteChoiBlockFlatten M := by
  have hmem := StarOrderedRing.nonneg_iff.mp hM
  clear hM
  rw [StarOrderedRing.nonneg_iff]
  refine AddSubmonoid.closure_induction (fun X hX ↦ ?_) ?_
      (fun X Y hX hY ihX ihY ↦ ?_) hmem
  · change ∃ W : CStarMatrix I I (CStarMatrix I I ℂ),
      star W * W = X at hX
    obtain ⟨W, rfl⟩ := hX
    rw [finiteChoiBlockFlatten_mul, finiteChoiBlockFlatten_star]
    exact AddSubmonoid.subset_closure (Set.mem_range_self _)
  · rw [finiteChoiBlockFlatten_zero]
    exact AddSubmonoid.zero_mem _
  · rw [finiteChoiBlockFlatten_add]
    exact AddSubmonoid.add_mem _ ihX ihY

/-- The EPR block matrix whose `(i,j)` entry is the matrix unit `E_ij`. -/
def finiteChoiBlockEPR
    {I : Type u} [Fintype I] [DecidableEq I] :
    CStarMatrix I I (CStarMatrix I I ℂ) :=
  fun i j ↦ finiteCStarMatrixUnit i j

theorem finiteChoiBlockEPR_nonneg
    {I : Type u} [Fintype I] [Nonempty I] [DecidableEq I] :
    0 ≤ finiteChoiBlockEPR (I := I) := by
  classical
  let r : I := Classical.choice inferInstance
  let W : CStarMatrix I I (CStarMatrix I I ℂ) :=
    fun p q ↦ if p = r then finiteCStarMatrixUnit r q else 0
  have hfactor : star W * W = finiteChoiBlockEPR (I := I) := by
    apply CStarMatrix.ext
    intro i j
    apply CStarMatrix.ext
    intro a b
    rw [CStarMatrix.mul_apply]
    simp only [cstarMatrix_fintypeSum_apply]
    simp_rw [CStarMatrix.mul_apply, CStarMatrix.star_apply]
    dsimp only [W, finiteChoiBlockEPR]
    rw [Fintype.sum_eq_single r]
    · rw [Fintype.sum_eq_single r]
      · by_cases ha : a = i <;> by_cases hb : b = j <;>
          simp [finiteCStarMatrixUnit, ha, hb]
      · intro x hx
        simp [finiteCStarMatrixUnit, hx]
    · intro x hx
      simp [hx]
  rw [← hfactor]
  exact star_mul_self_nonneg W

/-- The Choi matrix of every finite-dimensional completely positive map is
nonnegative. -/
theorem finiteChoiMatrix_cp_nonneg
    {I : Type u} [Fintype I] [Nonempty I] [DecidableEq I]
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ) :
    0 ≤ finiteChoiMatrix Phi.toLinearMap := by
  have hblock := Phi.map_cstarMatrix_nonneg
    (finiteChoiBlockEPR (I := I)) finiteChoiBlockEPR_nonneg
  have hflat := finiteChoiBlockFlatten_nonneg hblock
  have heq : finiteChoiBlockFlatten
      ((finiteChoiBlockEPR (I := I)).map Phi) =
        finiteChoiMatrix Phi.toLinearMap := by
    apply CStarMatrix.ext
    intro ia jb
    rcases ia with ⟨i, a⟩
    rcases jb with ⟨j, b⟩
    rfl
  rw [heq] at hflat
  exact hflat

/-- Adjoin one untouched identity factor to a concrete CP map, using its
literal finite Choi matrix. -/
def CompletelyPositiveMap.finiteChoiTensorId
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (Phi : CStarMatrix S S ℂ →CP CStarMatrix S S ℂ) :
    CStarMatrix I I ℂ →CP CStarMatrix I I ℂ :=
  finiteChoiTensorIdCP e (finiteChoiMatrix Phi.toLinearMap)
    (finiteChoiMatrix_cp_nonneg Phi)

@[simp] theorem CompletelyPositiveMap.finiteChoiTensorId_choi
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (Phi : CStarMatrix S S ℂ →CP CStarMatrix S S ℂ) :
    finiteChoiMatrix
        (CompletelyPositiveMap.finiteChoiTensorId e Phi).toLinearMap =
      finiteChoiKroneckerReindex e
        (finiteChoiMatrix Phi.toLinearMap)
        (finiteEPRProjector (I := T)) := by
  apply finiteChoiTensorIdCP_choi

/-- The explicit Choi/EPR lift respects composition at the level of its
underlying linear map. -/
theorem CompletelyPositiveMap.finiteChoiTensorId_comp_toLinearMap
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (Phi Psi : CStarMatrix S S ℂ →CP CStarMatrix S S ℂ) :
    (CompletelyPositiveMap.comp
      (CompletelyPositiveMap.finiteChoiTensorId e Phi)
      (CompletelyPositiveMap.finiteChoiTensorId e Psi)).toLinearMap =
    (CompletelyPositiveMap.finiteChoiTensorId e
      (CompletelyPositiveMap.comp Phi Psi)).toLinearMap := by
  apply finiteChoiMatrix_injective
  unfold CompletelyPositiveMap.finiteChoiTensorId
  rw [finiteChoiMatrix_comp_finiteChoiTensorIdCP,
    finiteChoiTensorIdCP_choi]
  have hPhi :
      (finiteCPMapOfNonnegativeChoi
        (finiteChoiMatrix Phi.toLinearMap)
        (finiteChoiMatrix_cp_nonneg Phi)).toLinearMap =
          Phi.toLinearMap := by
    apply finiteChoiMatrix_injective
    rw [finiteChoiMatrix_finiteCPMapOfNonnegativeChoi]
  have hPsi :
      (finiteCPMapOfNonnegativeChoi
        (finiteChoiMatrix Psi.toLinearMap)
        (finiteChoiMatrix_cp_nonneg Psi)).toLinearMap =
          Psi.toLinearMap := by
    apply finiteChoiMatrix_injective
    rw [finiteChoiMatrix_finiteCPMapOfNonnegativeChoi]
  rw [CompletelyPositiveMap.comp_toLinearMap, hPhi, hPsi]
  rw [CompletelyPositiveMap.comp_toLinearMap]

theorem finiteChoiKroneckerReindex_sub_left
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (G G' : CStarMatrix (S × S) (S × S) ℂ)
    (E : CStarMatrix (T × T) (T × T) ℂ) :
    finiteChoiKroneckerReindex e (G - G') E =
      finiteChoiKroneckerReindex e G E -
        finiteChoiKroneckerReindex e G' E := by
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  simp [finiteChoiKroneckerReindex_apply, sub_mul]

/-- A common untouched identity factor preserves the complete relative-CP
sandwich with exactly the same error. -/
theorem relativeCPApproximation_finiteChoiTensorId
    {I : Type u} {S : Type v} {T : Type w}
    [Fintype I] [Fintype S] [Fintype T]
    [Nonempty S] [Nonempty T]
    [DecidableEq I] [DecidableEq S] [DecidableEq T]
    (e : I ≃ S × T)
    (E H : CStarMatrix S S ℂ →CP CStarMatrix S S ℂ)
    (epsilon : ℝ)
    (h : RelativeCPApproximation epsilon E.toLinearMap H.toLinearMap) :
    RelativeCPApproximation epsilon
      (CompletelyPositiveMap.finiteChoiTensorId e E).toLinearMap
      (CompletelyPositiveMap.finiteChoiTensorId e H).toLinearMap := by
  constructor
  · obtain ⟨Delta, hDelta⟩ := h.lower
    refine ⟨CompletelyPositiveMap.finiteChoiTensorId e Delta, ?_⟩
    apply finiteChoiMatrix_injective
    rw [CompletelyPositiveMap.finiteChoiTensorId_choi,
      finiteChoiMatrix_sub, finiteChoiMatrix_smul,
      CompletelyPositiveMap.finiteChoiTensorId_choi,
      CompletelyPositiveMap.finiteChoiTensorId_choi]
    have hDeltaChoi :=
      congrArg (finiteChoiMatrix (I := S)) hDelta
    rw [hDeltaChoi, finiteChoiMatrix_sub, finiteChoiMatrix_smul,
      finiteChoiKroneckerReindex_sub_left,
      finiteChoiKroneckerReindex_smul_left]
  · obtain ⟨Delta, hDelta⟩ := h.upper
    refine ⟨CompletelyPositiveMap.finiteChoiTensorId e Delta, ?_⟩
    apply finiteChoiMatrix_injective
    rw [CompletelyPositiveMap.finiteChoiTensorId_choi,
      finiteChoiMatrix_sub, finiteChoiMatrix_smul,
      CompletelyPositiveMap.finiteChoiTensorId_choi,
      CompletelyPositiveMap.finiteChoiTensorId_choi]
    have hDeltaChoi :=
      congrArg (finiteChoiMatrix (I := S)) hDelta
    rw [hDeltaChoi, finiteChoiMatrix_sub, finiteChoiMatrix_smul,
      finiteChoiKroneckerReindex_sub_left,
      finiteChoiKroneckerReindex_smul_left]

end

end TomographyOracleCore
