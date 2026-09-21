import TomographyOracleCore.PhysicalHaarOneCopySpectral

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set MatrixReduction
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder

noncomputable section

/-! # Rank-one orbit kernel and positive-effect reduction -/

/-- The inverse-oriented unit-vector orbit naturally appearing when a
conjugated matrix is evaluated in a fixed effect eigenvector. -/
def inverseUnitarySphereOrbit (D : ℕ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin D)) 1)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    sphere (0 : EuclideanSpace ℂ (Fin D)) 1 :=
  unitarySphereAction D U⁻¹ v

theorem measurable_inverseUnitarySphereOrbit (D : ℕ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    Measurable (inverseUnitarySphereOrbit D v) := by
  unfold inverseUnitarySphereOrbit
  exact (continuous_unitarySphereAction_fixed_point D v).measurable.comp
    (by fun_prop : Measurable fun U :
      unitary (Matrix (Fin D) (Fin D) ℂ) ↦ U⁻¹)

theorem map_inverseUnitarySphereOrbit_unitaryHaarProbability
    (D : ℕ) (hD : 0 < D)
    (v : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    Measure.map (inverseUnitarySphereOrbit D v)
        (unitaryHaarProbability D) =
      complexUnitSphereHaarLaw (Fin D) := by
  calc
    Measure.map (inverseUnitarySphereOrbit D v)
        (unitaryHaarProbability D) =
      Measure.map (fun V ↦ unitarySphereAction D V v)
        (Measure.map Inv.inv (unitaryHaarProbability D)) := by
          rw [Measure.map_map]
          rfl
          · exact (continuous_unitarySphereAction_fixed_point D v).measurable
          · fun_prop
    _ = Measure.map (fun V ↦ unitarySphereAction D V v)
        (unitaryHaarProbability D) := by rw [unitaryHaarProbability_map_inv]
    _ = complexUnitSphereHaarLaw (Fin D) :=
      map_unitarySphereAction_unitaryHaarProbability D hD v

/-- The inverse orbit transported into the literal `ℂ² ⊕ ℂᵏ`
coordinates of the exact coupled-ratio calculation. -/
def hardCanonicalInverseOrbit (k : ℕ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)) :
    sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1 :=
  hardAmbientToCanonicalSphere k
    (inverseUnitarySphereOrbit (k + 2) v U)

theorem measurable_hardCanonicalInverseOrbit (k : ℕ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    Measurable (hardCanonicalInverseOrbit k v) := by
  unfold hardCanonicalInverseOrbit
  exact (measurable_unitSphereLinearIsometryActionBetween _).comp
    (measurable_inverseUnitarySphereOrbit _ _)

theorem map_hardCanonicalInverseOrbit_unitaryHaarProbability
    (k : ℕ) (hk : 1 ≤ k)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    Measure.map (hardCanonicalInverseOrbit k v)
        (unitaryHaarProbability (k + 2)) =
      complexUnitSphereHaarLaw (Fin (2 + k)) := by
  calc
    Measure.map (hardCanonicalInverseOrbit k v)
        (unitaryHaarProbability (k + 2)) =
      Measure.map (hardAmbientToCanonicalSphere k)
        (Measure.map (inverseUnitarySphereOrbit (k + 2) v)
          (unitaryHaarProbability (k + 2))) := by
            rw [Measure.map_map]
            rfl
            · exact measurable_unitSphereLinearIsometryActionBetween _
            · exact measurable_inverseUnitarySphereOrbit _ _
    _ = Measure.map (hardAmbientToCanonicalSphere k)
        (complexUnitSphereHaarLaw (Fin (k + 2))) := by
          rw [map_inverseUnitarySphereOrbit_unitaryHaarProbability]
          omega
    _ = complexUnitSphereHaarLaw (Fin (2 + k)) :=
      map_hardAmbientToCanonicalSphere_complexUnitSphereHaarLaw k

/-- The scalar singular rank-one kernel after canonical coordinate
transport. -/
def complexHaarTailRatio (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) : ℝ :=
  (hermitianQuadraticValue A (complexHaarTailVector k x)) ^ 2 /
    complexHaarHeadMass k x

theorem measurable_complexHaarTailRatio (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    Measurable (complexHaarTailRatio k A) := by
  have htailAmbient : Measurable (complexHaarTailCoordAmbient k) := by
    unfold complexHaarTailCoordAmbient
    fun_prop
  have htail : Measurable (complexHaarTailVector k) := by
    unfold complexHaarTailVector
    exact htailAmbient.comp measurable_subtype_coe
  have hquad : Measurable
      (fun y : EuclideanSpace ℂ (Fin k) ↦ hermitianQuadraticValue A y) := by
    unfold hermitianQuadraticValue
    fun_prop
  unfold complexHaarTailRatio
  exact ((hquad.comp htail).pow_const 2).div
    (measurable_complexHaarHeadMass k)

/-- Exact Haar average of the rank-one singular kernel, for every fixed
unit effect eigenvector. -/
theorem integral_hardCanonicalInverseOrbit_tailRatio
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    (∫ U, complexHaarTailRatio k A
        (hardCanonicalInverseOrbit k v U)
      ∂unitaryHaarProbability (k + 2)) =
      (A * A).trace.re / ((k : ℝ) + 2) := by
  calc
    (∫ U, complexHaarTailRatio k A
        (hardCanonicalInverseOrbit k v U)
      ∂unitaryHaarProbability (k + 2)) =
      ∫ x, complexHaarTailRatio k A x
        ∂Measure.map (hardCanonicalInverseOrbit k v)
          (unitaryHaarProbability (k + 2)) := by
            symm
            exact integral_map
              (measurable_hardCanonicalInverseOrbit k v).aemeasurable
              (measurable_complexHaarTailRatio k A).aestronglyMeasurable
    _ = ∫ x, complexHaarTailRatio k A x
        ∂complexUnitSphereHaarLaw (Fin (2 + k)) := by
          rw [map_hardCanonicalInverseOrbit_unitaryHaarProbability k hk v]
    _ = (A * A).trace.re / ((k : ℝ) + 2) :=
      integral_complexHaarTailQuadratic_sq_div_headMass
        k hk A hA htrace

/-- Bundle a Hermitian eigenvector as a unit-sphere point. -/
def hermitianEigenvectorSphere {D : ℕ}
    (E : Matrix (Fin D) (Fin D) ℂ) (hE : E.IsHermitian) (i : Fin D) :
    sphere (0 : EuclideanSpace ℂ (Fin D)) 1 :=
  ⟨hE.eigenvectorBasis i, by
    simpa [mem_sphere] using hE.eigenvectorBasis.norm_eq_one i⟩

@[simp] theorem hermitianEigenvectorSphere_coe {D : ℕ}
    (E : Matrix (Fin D) (Fin D) ℂ) (hE : E.IsHermitian) (i : Fin D) :
    (hermitianEigenvectorSphere E hE i).1 = hE.eigenvectorBasis i := rfl

theorem orientedEmbeddedTailQuadratic_eq_canonical
    (k : ℕ) (A : Matrix (Fin k) (Fin k) ℂ)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    hermitianQuadraticValue
        (unitaryConjugateMatrix U (embeddedTailMatrix k A)) v.1 =
      hermitianQuadraticValue A
        (complexHaarTailVector k (hardCanonicalInverseOrbit k v U)) := by
  rw [hermitianQuadraticValue_unitaryConjugate]
  rw [hermitianQuadraticValue_embeddedTailMatrix]
  rfl

theorem orientedHardReferenceQuadratic_head_lower
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    hardSpectrumHead b *
        complexHaarHeadMass k (hardCanonicalInverseOrbit k v U) ≤
      hermitianQuadraticValue
        (unitaryConjugateMatrix U (hardReferenceMatrix k b)) v.1 := by
  rw [hermitianQuadraticValue_unitaryConjugate]
  exact hardReferenceQuadratic_head_lower k b hb0
    (inverseUnitarySphereOrbit (k + 2) v U)

/-- Deterministic spectral Cauchy bound for one positive trace-one effect,
at every orientation for which all finitely many head coordinates are
nonzero. -/
theorem orientedPositiveEffect_ratio_le_spectralTailRatio
    (k : ℕ) (b : ℝ) (hb0 : 0 ≤ b) (hb1 : b < 1)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ)
    (hE : E.PosSemidef) (htrace : E.trace = 1)
    (hhead : ∀ i : Fin (k + 2),
      0 < complexHaarHeadMass k
        (hardCanonicalInverseOrbit k
          (hermitianEigenvectorSphere E hE.isHermitian i) U)) :
    (b * (unitaryConjugateMatrix U (embeddedTailMatrix k A) * E).trace.re) ^ 2 /
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re ≤
      (2 * b ^ 2 / (1 - b)) *
        ∑ i : Fin (k + 2), hE.isHermitian.eigenvalues i *
          complexHaarTailRatio k A
            (hardCanonicalInverseOrbit k
              (hermitianEigenvectorSphere E hE.isHermitian i) U) := by
  let w : Fin (k + 2) → ℝ := fun i ↦ hE.isHermitian.eigenvalues i
  let q : Fin (k + 2) → ℝ := fun i ↦
    complexHaarHeadMass k
      (hardCanonicalInverseOrbit k
        (hermitianEigenvectorSphere E hE.isHermitian i) U)
  let δ : Fin (k + 2) → ℝ := fun i ↦
    hermitianQuadraticValue A
      (complexHaarTailVector k
        (hardCanonicalInverseOrbit k
          (hermitianEigenvectorSphere E hE.isHermitian i) U))
  let r : Fin (k + 2) → ℝ := fun i ↦
    hermitianQuadraticValue
      (unitaryConjugateMatrix U (hardReferenceMatrix k b))
      (hE.isHermitian.eigenvectorBasis i)
  let s : Finset (Fin (k + 2)) := Finset.univ.filter (fun i ↦ w i ≠ 0)
  have hw_nonneg (i : Fin (k + 2)) : 0 ≤ w i := by
    exact hE.eigenvalues_nonneg i
  have hw_sum : (∑ i : Fin (k + 2), w i) = 1 := by
    have ht := hE.isHermitian.trace_eq_sum_eigenvalues
    have hre := congrArg Complex.re ht
    rw [htrace] at hre
    simpa [w] using hre.symm
  have hq_pos (i : Fin (k + 2)) : 0 < q i := hhead i
  have hheadCoeff : 0 < hardSpectrumHead b := by
    unfold hardSpectrumHead
    linarith
  have hnum :
      (unitaryConjugateMatrix U (embeddedTailMatrix k A) * E).trace.re =
        ∑ i : Fin (k + 2), w i * δ i := by
    rw [trace_mul_re_eq_sum_eigenvalues_mul_quadratic _ E hE.isHermitian]
    apply Finset.sum_congr rfl
    intro i hi
    change hE.isHermitian.eigenvalues i *
        hermitianQuadraticValue
          (unitaryConjugateMatrix U (embeddedTailMatrix k A))
          (hermitianEigenvectorSphere E hE.isHermitian i).1 = _
    rw [orientedEmbeddedTailQuadratic_eq_canonical]
  have hden :
      (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re =
        ∑ i : Fin (k + 2), w i * r i := by
    rw [trace_mul_re_eq_sum_eigenvalues_mul_quadratic _ E hE.isHermitian]
  have hdenLower :
      hardSpectrumHead b * (∑ i : Fin (k + 2), w i * q i) ≤
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re := by
    rw [hden, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    calc
      hardSpectrumHead b * (w i * q i) =
          w i * (hardSpectrumHead b * q i) := by ring
      _ ≤ w i * r i := by
        apply mul_le_mul_of_nonneg_left _ (hw_nonneg i)
        exact orientedHardReferenceQuadratic_head_lower k b hb0 U
          (hermitianEigenvectorSphere E hE.isHermitian i)
  have hQpos : 0 < ∑ i : Fin (k + 2), w i * q i := by
    have hsumwpos : 0 < ∑ i : Fin (k + 2), w i := by
      rw [hw_sum]
      norm_num
    have hex : ∃ i ∈ (Finset.univ : Finset (Fin (k + 2))), 0 < w i :=
      (Finset.sum_pos_iff_of_nonneg
        (fun i hi ↦ hw_nonneg i)).mp hsumwpos
    obtain ⟨i, hi, hwi⟩ := hex
    apply Finset.sum_pos'
      (fun j hj ↦ mul_nonneg (hw_nonneg j) (le_of_lt (hq_pos j)))
    exact ⟨i, hi, mul_pos hwi (hq_pos i)⟩
  have hw_s_pos : ∀ i ∈ s, 0 < w i := by
    intro i hi
    have hwi : w i ≠ 0 := (Finset.mem_filter.mp hi).2
    exact lt_of_le_of_ne (hw_nonneg i) (Ne.symm hwi)
  have hq_s_pos : ∀ i ∈ s, 0 < q i := by
    intro i hi
    exact hq_pos i
  have hweighted := weighted_sq_sum_div_le s w q δ hw_s_pos hq_s_pos
  have hNfilter :
      (∑ i ∈ s, w i * δ i) = ∑ i : Fin (k + 2), w i * δ i := by
    unfold s
    simpa using Finset.sum_filter_of_ne
      (s := (Finset.univ : Finset (Fin (k + 2))))
      (f := fun i ↦ w i * δ i) (p := fun i ↦ w i ≠ 0)
      (fun i hi hprod ↦ by
        intro hwi
        simp [hwi] at hprod)
  have hQfilter :
      (∑ i ∈ s, w i * q i) = ∑ i : Fin (k + 2), w i * q i := by
    unfold s
    simpa using Finset.sum_filter_of_ne
      (s := (Finset.univ : Finset (Fin (k + 2))))
      (f := fun i ↦ w i * q i) (p := fun i ↦ w i ≠ 0)
      (fun i hi hprod ↦ by
        intro hwi
        simp [hwi] at hprod)
  have hSfilter :
      (∑ i ∈ s, w i * (δ i) ^ 2 / q i) =
        ∑ i : Fin (k + 2), w i * (δ i) ^ 2 / q i := by
    unfold s
    simpa using Finset.sum_filter_of_ne
      (s := (Finset.univ : Finset (Fin (k + 2))))
      (f := fun i ↦ w i * (δ i) ^ 2 / q i)
      (p := fun i ↦ w i ≠ 0)
      (fun i hi hprod ↦ by
        intro hwi
        simp [hwi] at hprod)
  rw [hNfilter, hQfilter, hSfilter] at hweighted
  calc
    (b * (unitaryConjugateMatrix U (embeddedTailMatrix k A) * E).trace.re) ^ 2 /
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re =
      (b * (∑ i : Fin (k + 2), w i * δ i)) ^ 2 /
        (unitaryConjugateMatrix U (hardReferenceMatrix k b) * E).trace.re := by
          rw [hnum]
    _ ≤ (b * (∑ i : Fin (k + 2), w i * δ i)) ^ 2 /
        (hardSpectrumHead b * (∑ i : Fin (k + 2), w i * q i)) := by
      exact div_le_div_of_nonneg_left (sq_nonneg _)
        (mul_pos hheadCoeff hQpos) hdenLower
    _ = (b ^ 2 / hardSpectrumHead b) *
        (((∑ i : Fin (k + 2), w i * δ i) ^ 2) /
          (∑ i : Fin (k + 2), w i * q i)) := by
      field_simp [ne_of_gt hheadCoeff, ne_of_gt hQpos]
    _ ≤ (b ^ 2 / hardSpectrumHead b) *
        (∑ i : Fin (k + 2), w i * (δ i) ^ 2 / q i) := by
      exact mul_le_mul_of_nonneg_left hweighted
        (div_nonneg (sq_nonneg b) (le_of_lt hheadCoeff))
    _ = (2 * b ^ 2 / (1 - b)) *
        ∑ i : Fin (k + 2), hE.isHermitian.eigenvalues i *
          complexHaarTailRatio k A
            (hardCanonicalInverseOrbit k
              (hermitianEigenvectorSphere E hE.isHermitian i) U) := by
      unfold w q δ complexHaarTailRatio hardSpectrumHead
      have hbne : 1 - b ≠ 0 := ne_of_gt (sub_pos.mpr hb1)
      field_simp [hbne]

/-- The two-coordinate Haar head mass is strictly positive almost
everywhere. -/
theorem ae_complexHaarHeadMass_pos (k : ℕ) (hk : 1 ≤ k) :
    ∀ᵐ x ∂complexUnitSphereHaarLaw (Fin (2 + k)),
      0 < complexHaarHeadMass k x := by
  have hbeta : ∀ᵐ s ∂betaMeasure 2 (k : ℝ), 0 < s := by
    filter_upwards [ae_mem_Ioo_betaMeasure' 2 (k : ℝ)] with s hs
    exact hs.1
  have hmap : Measure.map (complexHaarHeadMass k)
      (complexUnitSphereHaarLaw (Fin (2 + k))) =
        betaMeasure 2 (k : ℝ) :=
    complexHaarHeadMass_betaLaw k hk
  rw [← hmap] at hbeta
  exact (ae_map_iff
    (measurable_complexHaarHeadMass k).aemeasurable measurableSet_Ioi).mp hbeta

theorem ae_hardCanonicalInverseOrbit_headMass_pos
    (k : ℕ) (hk : 1 ≤ k)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      0 < complexHaarHeadMass k (hardCanonicalInverseOrbit k v U) := by
  have h := ae_complexHaarHeadMass_pos k hk
  rw [← map_hardCanonicalInverseOrbit_unitaryHaarProbability k hk v] at h
  exact (ae_map_iff (measurable_hardCanonicalInverseOrbit k v).aemeasurable
    (measurableSet_Ioi.preimage (measurable_complexHaarHeadMass k))).mp h

/-- All finitely many eigenvectors of one fixed effect have positive head
mass simultaneously for almost every hidden orientation. -/
theorem ae_all_effectEigenvector_headMass_pos
    (k : ℕ) (hk : 1 ≤ k)
    (E : Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ) (hE : E.IsHermitian) :
    ∀ᵐ U ∂unitaryHaarProbability (k + 2),
      ∀ i : Fin (k + 2),
        0 < complexHaarHeadMass k
          (hardCanonicalInverseOrbit k (hermitianEigenvectorSphere E hE i) U) := by
  have hall := (Filter.eventually_all_finite (Set.finite_univ)).2
    (fun i hi ↦ ae_hardCanonicalInverseOrbit_headMass_pos k hk
      (hermitianEigenvectorSphere E hE i))
  filter_upwards [hall] with U hU
  intro i
  exact hU i (Set.mem_univ i)

theorem abs_hermitianQuadraticValue_le_operatorNorm_mul_norm_sq
    {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (x : EuclideanSpace ℂ (Fin D)) :
    |hermitianQuadraticValue A x| ≤ matrixOperatorNorm A * ‖x‖ ^ 2 := by
  unfold hermitianQuadraticValue matrixOperatorNorm
  calc
    |(⟪x, A.toEuclideanLin x⟫_ℂ).re| ≤ ‖⟪x, A.toEuclideanLin x⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖A.toEuclideanLin x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ *
        (‖A.toEuclideanLin.toContinuousLinearMap‖ * ‖x‖) := by
      exact mul_le_mul_of_nonneg_left
        (A.toEuclideanLin.toContinuousLinearMap.le_opNorm x) (norm_nonneg _)
    _ = ‖A.toEuclideanLin.toContinuousLinearMap‖ * ‖x‖ ^ 2 := by ring

/-- The singular tail/head kernel is genuinely integrable; its exact
integral is therefore usable inside finite spectral sums and Tonelli
arguments. -/
theorem integrable_complexHaarTailRatio
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ) :
    Integrable (complexHaarTailRatio k A)
      (complexUnitSphereHaarLaw (Fin (2 + k))) := by
  have hinfo := integrable_complexHaarHeadMass_information k hk
    (complexHaarHeadMass_betaLaw k hk)
  have hdom := hinfo.const_mul (matrixOperatorNorm A ^ 2)
  apply hdom.mono'
    (measurable_complexHaarTailRatio k A).aestronglyMeasurable
  filter_upwards with x
  have hhead_nonneg : 0 ≤ complexHaarHeadMass k x := by
    unfold complexHaarHeadMass
    exact Finset.sum_nonneg fun i hi ↦ Complex.normSq_nonneg _
  have hratio_nonneg : 0 ≤ complexHaarTailRatio k A x := by
    unfold complexHaarTailRatio
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hratio_nonneg]
  unfold complexHaarTailRatio
  rw [← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ hhead_nonneg
  have hquad := abs_hermitianQuadraticValue_le_operatorNorm_mul_norm_sq
    A (complexHaarTailVector k x)
  calc
    (hermitianQuadraticValue A (complexHaarTailVector k x)) ^ 2 ≤
        (matrixOperatorNorm A * ‖complexHaarTailVector k x‖ ^ 2) ^ 2 := by
      rw [sq_le_sq]
      rwa [abs_of_nonneg (mul_nonneg (matrixOperatorNorm_nonneg A)
        (sq_nonneg _))]
    _ = matrixOperatorNorm A ^ 2 *
        (1 - complexHaarHeadMass k x) ^ 2 := by
      rw [complexHaarTailVector_norm_sq]
      ring

theorem integrable_hardCanonicalInverseOrbit_tailRatio
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (v : sphere (0 : EuclideanSpace ℂ (Fin (k + 2))) 1) :
    Integrable (fun U ↦ complexHaarTailRatio k A
      (hardCanonicalInverseOrbit k v U))
      (unitaryHaarProbability (k + 2)) := by
  have h := integrable_complexHaarTailRatio k hk A
  rw [← map_hardCanonicalInverseOrbit_unitaryHaarProbability k hk v] at h
  exact h.comp_aemeasurable
    (measurable_hardCanonicalInverseOrbit k v).aemeasurable

end

end TomographyOracleCore
