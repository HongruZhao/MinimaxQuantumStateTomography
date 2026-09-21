import TomographyOracleCore.UnitaryHaarSphereOrbit
import TomographyOracleCore.PhysicalHaarOneCopy

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set
open MatrixReduction
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder ENNReal Pointwise

noncomputable section

/-! # Spectral and coordinate transport for the arbitrary-POVM Haar bound -/

/-- Expand a trace pairing in the orthonormal eigenbasis of its second
factor.  No measurable choice is involved: this is a pointwise identity for
one fixed effect matrix. -/
theorem trace_mul_re_eq_sum_eigenvalues_mul_quadratic
    {D : ℕ} (B E : Matrix (Fin D) (Fin D) ℂ)
    (hE : E.IsHermitian) :
    (B * E).trace.re =
      ∑ i : Fin D, hE.eigenvalues i *
        hermitianQuadraticValue B (hE.eigenvectorBasis i) := by
  let e := (EuclideanSpace.basisFun (Fin D) ℂ).toBasis
  rw [← Matrix.trace_toLin_eq (B * E) e, Matrix.toLin_mul e e]
  dsimp [e]
  rw [LinearMap.trace_eq_sum_inner _ hE.eigenvectorBasis]
  simp_rw [LinearMap.comp_apply, toLin_eigenvectorBasis]
  simp_rw [map_smul, inner_smul_right]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  congr 1

/-- Conjugating a matrix by `U` and evaluating its quadratic form at `x`
is the same as evaluating the original matrix at the inverse-rotated
vector. -/
theorem hermitianQuadraticValue_unitaryConjugate
    {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ)
    (x : EuclideanSpace ℂ (Fin D)) :
    hermitianQuadraticValue (unitaryConjugateMatrix U A) x =
      hermitianQuadraticValue A (unitaryVectorAction D U⁻¹ x) := by
  unfold hermitianQuadraticValue
  change
    (⟪x, (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ))
      (unitaryConjugateMatrix U A) x⟫_ℂ).re = _
  rw [unitaryConjugateMatrix_apply, map_mul, map_mul]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [show (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ))
        (star (U : Matrix (Fin D) (Fin D) ℂ)) x =
      unitaryVectorAction D U⁻¹ x by
    simp [unitaryVectorAction]]
  rw [show (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ))
        (U : Matrix (Fin D) (Fin D) ℂ)
        ((Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)) A
          (unitaryVectorAction D U⁻¹ x)) =
      unitaryVectorAction D U
        ((Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)) A
          (unitaryVectorAction D U⁻¹ x)) by
    rfl]
  have hx :
      unitaryVectorAction D U (unitaryVectorAction D U⁻¹ x) = x := by
    rw [← unitaryVectorAction_mul]
    simp
  nth_rewrite 1 [← hx]
  exact congrArg Complex.re
    ((unitaryVectorComplexIsometry D U).inner_map_map
      (unitaryVectorAction D U⁻¹ x)
      ((Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)) A
        (unitaryVectorAction D U⁻¹ x)))

/-- The coordinate equivalence undoing the `k+2`/`2+k` cast used in the
hard-state matrices. -/
def hardAmbientToCanonicalIndexEquiv (k : ℕ) :
    Fin (k + 2) ≃ Fin (2 + k) :=
  (Equiv.cast (congrArg Fin (Nat.add_comm 2 k))).symm

noncomputable def hardAmbientToCanonicalComplexIsometry (k : ℕ) :
    EuclideanSpace ℂ (Fin (k + 2)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (Fin (2 + k)) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (hardAmbientToCanonicalIndexEquiv k)

noncomputable def hardAmbientToCanonicalRealIsometry (k : ℕ) :
    EuclideanSpace ℂ (Fin (k + 2)) ≃ₗᵢ[ℝ]
      EuclideanSpace ℂ (Fin (2 + k)) :=
  { (hardAmbientToCanonicalComplexIsometry k).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (hardAmbientToCanonicalComplexIsometry k).norm_map }

/-- A real linear isometry equivalence between two ambient spaces acts on
their unit spheres. -/
noncomputable def unitSphereLinearIsometryActionBetween
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) : sphere (0 : E) 1 → sphere (0 : F) 1 :=
  fun x ↦ ⟨e x.1, by simpa [mem_sphere] using x.2⟩

@[simp] theorem unitSphereLinearIsometryActionBetween_coe
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (x : sphere (0 : E) 1) :
    (unitSphereLinearIsometryActionBetween e x : F) = e x.1 := rfl

theorem measurable_unitSphereLinearIsometryActionBetween
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace F] [BorelSpace F]
    (e : E ≃ₗᵢ[ℝ] F) :
    Measurable (unitSphereLinearIsometryActionBetween e) := by
  unfold unitSphereLinearIsometryActionBetween
  exact ((e.continuous.comp continuous_subtype_val).subtype_mk _).measurable

theorem unitSphereSector_preimage_between
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (s : Set (sphere (0 : F) 1)) :
    Ioo (0 : ℝ) 1 •
          ((↑) '' (unitSphereLinearIsometryActionBetween e ⁻¹' s) : Set E) =
      e ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s : Set F)) := by
  ext y
  constructor
  · rintro ⟨r, hr, z, ⟨x, hx, rfl⟩, rfl⟩
    change e (r • x.1) ∈
      Ioo (0 : ℝ) 1 • ((↑) '' s : Set F)
    exact ⟨r, hr, e x.1,
      ⟨unitSphereLinearIsometryActionBetween e x, hx, rfl⟩, by simp⟩
  · intro hy
    change e y ∈ Ioo (0 : ℝ) 1 • ((↑) '' s : Set F) at hy
    rcases hy with ⟨r, hr, z, ⟨x, hx, rfl⟩, hrey⟩
    let x' : sphere (0 : E) 1 :=
      unitSphereLinearIsometryActionBetween e.symm x
    refine ⟨r, hr, x'.1, ⟨x', ?_, rfl⟩, ?_⟩
    · change unitSphereLinearIsometryActionBetween e x' ∈ s
      simpa [x', unitSphereLinearIsometryActionBetween] using hx
    · apply e.injective
      simpa [x', unitSphereLinearIsometryActionBetween] using hrey

theorem toSphere_map_unitSphereLinearIsometryActionBetween
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] [Nontrivial F]
    (e : E ≃ₗᵢ[ℝ] F) :
    Measure.map (unitSphereLinearIsometryActionBetween e)
        ((volume : Measure E).toSphere) =
      (volume : Measure F).toSphere := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply
      (measurable_unitSphereLinearIsometryActionBetween e) hs,
    Measure.toSphere_apply' _
      (hs.preimage (measurable_unitSphereLinearIsometryActionBetween e)),
    Measure.toSphere_apply' _ hs,
    unitSphereSector_preimage_between]
  rw [LinearEquiv.finrank_eq e.toLinearEquiv]
  congr 1
  exact (LinearIsometryEquiv.measurePreserving e).measure_preimage
    (measurableSet_unitSphereSector hs).nullMeasurableSet

/-- Normalized sphere Haar law is transported by a linear isometry
equivalence even when the two coordinate index types differ. -/
theorem normalizedHaarSphereLaw_map_linearIsometryBetween
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] [Nontrivial F]
    (e : E ≃ₗᵢ[ℝ] F) :
    Measure.map (unitSphereLinearIsometryActionBetween e)
        (normalizedHaarSphereLaw (volume : Measure E)) =
      normalizedHaarSphereLaw (volume : Measure F) := by
  unfold normalizedHaarSphereLaw
  have hmap := toSphere_map_unitSphereLinearIsometryActionBetween e
  have hmass : (volume : Measure E).toSphere univ =
      (volume : Measure F).toSphere univ := by
    have h := congrArg
      (fun μ : Measure (sphere (0 : F) 1) ↦ μ univ) hmap
    rw [Measure.map_apply
      (measurable_unitSphereLinearIsometryActionBetween e) MeasurableSet.univ]
      at h
    simpa using h
  rw [Measure.map_smul, hmap]
  rw [hmass]

def hardAmbientToCanonicalSphere (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1 :=
  unitSphereLinearIsometryActionBetween
    (hardAmbientToCanonicalRealIsometry k) x

@[simp] theorem hardAmbientToCanonicalSphere_coe (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    (hardAmbientToCanonicalSphere k x).1 =
      hardAmbientToCanonicalComplexIsometry k x.1 := by
  rfl

theorem map_hardAmbientToCanonicalSphere_complexUnitSphereHaarLaw
    (k : ℕ) :
    Measure.map (hardAmbientToCanonicalSphere k)
        (complexUnitSphereHaarLaw (Fin (k + 2))) =
      complexUnitSphereHaarLaw (Fin (2 + k)) := by
  unfold hardAmbientToCanonicalSphere
  exact normalizedHaarSphereLaw_map_linearIsometryBetween
    (hardAmbientToCanonicalRealIsometry k)

@[simp] theorem hardAmbientToCanonicalComplexIsometry_tail_apply
    (k : ℕ) (x : EuclideanSpace ℂ (Fin (k + 2))) (j : Fin k) :
    complexHaarTailCoordAmbient k
        (hardAmbientToCanonicalComplexIsometry k x) j =
      x (hardProjectorBlockEquiv k (Sum.inr j)) := by
  rfl

noncomputable def embeddedTailMatrix (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
    (Matrix.fromBlocks 0 0 0 A)

theorem embeddedTailMatrix_eq_embeddedCenteredProjectorTail
    {k m : ℕ} (P : RankMComplexOrthogonalProjector k m) :
    embeddedTailMatrix k (centeredProjectorTail P) =
      embeddedCenteredProjectorTail P := by
  rfl

/-- Reindexing a matrix and its vector coordinates preserves its real
quadratic form. -/
theorem hermitianQuadraticValue_reindex
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ κ) :
    hermitianQuadraticValue (Matrix.reindex e e A) x =
      hermitianQuadraticValue A
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm x) := by
  unfold hermitianQuadraticValue
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    dotProduct, Matrix.mulVec, Matrix.reindex_apply,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  congr 1
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply,
    Matrix.submatrix_mulVec_equiv]
  simp [Function.comp_def]

/-- Extract the tail component of a vector in head/tail block coordinates. -/
def sumTailVector (k : ℕ)
    (x : EuclideanSpace ℂ (Fin 2 ⊕ Fin k)) : EuclideanSpace ℂ (Fin k) :=
  WithLp.toLp 2 (fun j ↦ x (Sum.inr j))

/-- A matrix supported on the tail block has the same quadratic form as its
tail matrix acting on the extracted tail vector. -/
theorem hermitianQuadraticValue_fromBlocks_tail
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ)
    (x : EuclideanSpace ℂ (Fin 2 ⊕ Fin k)) :
    hermitianQuadraticValue (Matrix.fromBlocks 0 0 0 A) x =
      hermitianQuadraticValue A (sumTailVector k x) := by
  unfold hermitianQuadraticValue sumTailVector
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    dotProduct]
  rw [Fintype.sum_sum_type]
  simp only [Matrix.toLin'_apply, Matrix.fromBlocks_mulVec,
    Matrix.zero_mulVec, Pi.zero_apply, zero_add, Sum.elim_inl, Sum.elim_inr]
  have hcomp : x.ofLp ∘ Sum.inr =
      (fun j : Fin k ↦ x.ofLp (Sum.inr j)) := rfl
  rw [hcomp]
  simp

theorem sumTailVector_hardAmbient_eq
    (k : ℕ) (x : EuclideanSpace ℂ (Fin (k + 2))) :
    sumTailVector k
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (hardProjectorBlockEquiv k).symm x) =
      complexHaarTailCoordAmbient k
        (hardAmbientToCanonicalComplexIsometry k x) := by
  ext j
  exact (hardAmbientToCanonicalComplexIsometry_tail_apply k x j).symm

/-- The physical hard-state tail matrix and the canonical coupled-ratio tail
quadratic form agree exactly, including the `k+2`/`2+k` coordinate cast. -/
theorem hermitianQuadraticValue_embeddedTailMatrix
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ)
    (x : EuclideanSpace ℂ (Fin (k + 2))) :
    hermitianQuadraticValue (embeddedTailMatrix k A) x =
      hermitianQuadraticValue A
        (complexHaarTailCoordAmbient k
          (hardAmbientToCanonicalComplexIsometry k x)) := by
  unfold embeddedTailMatrix
  rw [hermitianQuadraticValue_reindex]
  rw [hermitianQuadraticValue_fromBlocks_tail]
  rw [sumTailVector_hardAmbient_eq]

/-- The ambient matrix selecting the two-dimensional head block. -/
noncomputable def embeddedHeadMatrix (k : ℕ) :
    Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ :=
  Matrix.reindex (hardProjectorBlockEquiv k) (hardProjectorBlockEquiv k)
    (Matrix.fromBlocks 1 0 0 0)

/-- The quadratic form of the head-block selector is the squared norm of the
two head coordinates. -/
theorem hermitianQuadraticValue_fromBlocks_head
    (k : ℕ) (x : EuclideanSpace ℂ (Fin 2 ⊕ Fin k)) :
    hermitianQuadraticValue
        (Matrix.fromBlocks 1 0 0 (0 : Matrix (Fin k) (Fin k) ℂ)) x =
      ∑ i : Fin 2, Complex.normSq (x (Sum.inl i)) := by
  unfold hermitianQuadraticValue
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    dotProduct]
  rw [Fintype.sum_sum_type]
  simp [Matrix.toLin'_apply, Matrix.fromBlocks_mulVec,
    Complex.normSq_apply]

@[simp] theorem hardAmbientToCanonicalComplexIsometry_head_apply
    (k : ℕ) (x : EuclideanSpace ℂ (Fin (k + 2))) (i : Fin 2) :
    hardAmbientToCanonicalComplexIsometry k x (Fin.castAdd k i) =
      x (hardProjectorBlockEquiv k (Sum.inl i)) := by
  rfl

/-- The physical head selector and canonical coupled-ratio head mass agree
exactly, including the `k+2`/`2+k` coordinate cast. -/
theorem hermitianQuadraticValue_embeddedHeadMatrix
    (k : ℕ) (x : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    hermitianQuadraticValue (embeddedHeadMatrix k) x.1 =
      complexHaarHeadMass k (hardAmbientToCanonicalSphere k x) := by
  unfold embeddedHeadMatrix
  rw [hermitianQuadraticValue_reindex]
  rw [hermitianQuadraticValue_fromBlocks_head]
  unfold complexHaarHeadMass
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The hard reference is the sum of its scalar head selector and its
positive uniform-tail block. -/
theorem hardReferenceMatrix_eq_head_add_tail
    (k : ℕ) (b : ℝ) :
    hardReferenceMatrix k b =
      hardSpectrumHead b • embeddedHeadMatrix k +
        embeddedTailMatrix k (hardReferenceTailBlock k b) := by
  ext i j
  simp only [hardReferenceMatrix, hardReferenceBlockMatrix,
    hardProjectorHeadBlock, embeddedHeadMatrix, embeddedTailMatrix,
    Matrix.reindex_apply, Matrix.add_apply, Matrix.smul_apply]
  generalize hi : (hardProjectorBlockEquiv k).symm i = p
  generalize hj : (hardProjectorBlockEquiv k).symm j = q
  rcases p with p | p <;> rcases q with q | q
  · by_cases hpq : p = q <;>
      simp_all [hardReferenceTailBlock, Matrix.diagonal_apply, hpq]
  · simp_all [hardReferenceTailBlock, Matrix.diagonal_apply]
  · simp_all [hardReferenceTailBlock, Matrix.diagonal_apply]
  · by_cases hpq : p = q <;>
      simp_all [hardReferenceTailBlock, Matrix.diagonal_apply, hpq]

theorem hermitianQuadraticValue_add
    {D : ℕ} (A B : Matrix (Fin D) (Fin D) ℂ)
    (x : EuclideanSpace ℂ (Fin D)) :
    hermitianQuadraticValue (A + B) x =
      hermitianQuadraticValue A x + hermitianQuadraticValue B x := by
  unfold hermitianQuadraticValue
  simp [map_add]

theorem hermitianQuadraticValue_real_smul
    {D : ℕ} (c : ℝ) (A : Matrix (Fin D) (Fin D) ℂ)
    (x : EuclideanSpace ℂ (Fin D)) :
    hermitianQuadraticValue (c • A) x =
      c * hermitianQuadraticValue A x := by
  unfold hermitianQuadraticValue
  rw [show c • A = (c : ℂ) • A by rfl]
  rw [Matrix.toEuclideanLin.map_smul]
  change (⟪x, (c : ℂ) • A.toEuclideanLin x⟫_ℂ).re = _
  rw [inner_smul_right]
  simp [Complex.mul_re]

/-- Positive-semidefinite matrices have nonnegative real quadratic forms. -/
theorem hermitianQuadraticValue_nonneg_of_posSemidef
    {D : ℕ} {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : A.PosSemidef) (x : EuclideanSpace ℂ (Fin D)) :
    0 ≤ hermitianQuadraticValue A x := by
  have h := hA.dotProduct_mulVec_nonneg x.ofLp
  rw [Complex.nonneg_iff] at h
  unfold hermitianQuadraticValue
  simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.ofLp_toLpLin,
    dotProduct, Matrix.toLin'_apply]
  convert h.1 using 1
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

/-- The reference quadratic form dominates its head-block contribution. -/
theorem hardReferenceQuadratic_head_lower
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    hardSpectrumHead b *
        complexHaarHeadMass k (hardAmbientToCanonicalSphere k x) ≤
      hermitianQuadraticValue (hardReferenceMatrix k b) x.1 := by
  rw [hardReferenceMatrix_eq_head_add_tail]
  rw [hermitianQuadraticValue_add,
    hermitianQuadraticValue_real_smul,
    hermitianQuadraticValue_embeddedHeadMatrix]
  exact le_add_of_nonneg_right
    (by
      rw [hermitianQuadraticValue_embeddedTailMatrix]
      exact hermitianQuadraticValue_nonneg_of_posSemidef
        (hardReferenceTailBlock_posSemidef k b hb0) _)

/-- Normalized unitary Haar probability is invariant under inversion. -/
theorem unitaryHaarProbability_map_inv (D : ℕ) :
    Measure.map Inv.inv (unitaryHaarProbability D) =
      unitaryHaarProbability D := by
  let G := unitary (Matrix (Fin D) (Fin D) ℂ)
  let μ : Measure G := unitaryHaarProbability D
  let ν : Measure G := Measure.map Inv.inv μ
  letI : Measure.IsHaarMeasure μ := by
    dsimp only [μ]
    unfold unitaryHaarProbability
    have hzero : (Measure.haar : Measure G) univ ≠ 0 := by
      exact isOpen_univ.measure_ne_zero _ univ_nonempty
    have htop : (Measure.haar : Measure G) univ ≠ ⊤ := by
      exact ne_of_lt isCompact_univ.measure_lt_top
    exact Measure.IsHaarMeasure.smul _
      (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr hzero)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop : AEMeasurable Inv.inv μ)
  letI : Measure.IsHaarMeasure ν := by
    change Measure.IsHaarMeasure μ.inv
    letI : Measure.IsMulRightInvariant μ := by
      dsimp only [μ]
      infer_instance
    letI : IsFiniteMeasureOnCompacts μ.inv := by infer_instance
    letI : Measure.IsMulLeftInvariant μ.inv := by infer_instance
    letI : Measure.IsOpenPosMeasure μ.inv := by infer_instance
    exact Measure.IsHaarMeasure.mk
  change ν = μ
  exact Measure.isHaarMeasure_eq_of_isProbabilityMeasure ν μ

end
end TomographyOracleCore
