import TomographyOracleCore.ProjectiveHaarCoupledRatio
import TomographyOracleCore.UnitaryHaarOrientation
import Mathlib.MeasureTheory.Integral.Prod

namespace TomographyOracleCore
open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace ComplexOrder
noncomputable section

def matrixToEuclideanCLMStarMonoidHom (D : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →⋆*
      (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D)) where
  toFun := Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)
  map_one' := map_one _
  map_mul' := map_mul _
  map_star' := map_star _

set_option synthInstance.maxHeartbeats 200000 in
def euclideanCLMToMatrixStarMonoidHom (D : ℕ) :
    (EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D)) →⋆*
      Matrix (Fin D) (Fin D) ℂ where
  toFun := (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)).symm
  map_one' := map_one _
  map_mul' := map_mul _
  map_star' := map_star _

def unitaryVectorComplexIsometry (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    EuclideanSpace ℂ (Fin D) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D) :=
  Unitary.linearIsometryEquiv
    ((Unitary.map (matrixToEuclideanCLMStarMonoidHom D)) U)

def unitaryVectorRealIsometry (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    EuclideanSpace ℂ (Fin D) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin D) :=
  { (unitaryVectorComplexIsometry D U).toLinearEquiv.restrictScalars ℝ with
    norm_map' := (unitaryVectorComplexIsometry D U).norm_map }

def unitaryVectorAction (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : EuclideanSpace ℂ (Fin D)) : EuclideanSpace ℂ (Fin D) :=
  (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ))
    (U : Matrix (Fin D) (Fin D) ℂ) x

@[simp] theorem unitaryVectorComplexIsometry_apply (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : EuclideanSpace ℂ (Fin D)) :
    unitaryVectorComplexIsometry D U x = unitaryVectorAction D U x := by
  rfl

@[simp] theorem unitaryVectorRealIsometry_apply (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : EuclideanSpace ℂ (Fin D)) :
    unitaryVectorRealIsometry D U x = unitaryVectorAction D U x := by
  rfl

theorem continuous_unitaryVectorAction (D : ℕ) :
    Continuous (fun z : unitary (Matrix (Fin D) (Fin D) ℂ) ×
      EuclideanSpace ℂ (Fin D) => unitaryVectorAction D z.1 z.2) := by
  unfold unitaryVectorAction
  change Continuous (fun z : unitary (Matrix (Fin D) (Fin D) ℂ) ×
      EuclideanSpace ℂ (Fin D) => WithLp.toLp 2
    (Matrix.mulVec (z.1 : Matrix (Fin D) (Fin D) ℂ) (WithLp.ofLp z.2)))
  fun_prop

theorem measurable_unitaryVectorAction_fixed (D : ℕ)
    (x : EuclideanSpace ℂ (Fin D)) :
    Measurable (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) =>
      unitaryVectorAction D U x) := by
  exact ((continuous_unitaryVectorAction D).comp
    (continuous_id.prodMk continuous_const)).measurable

theorem exists_orthonormalBasis_zero_eq
    (D : ℕ) (hD : 0 < D)
    (x : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    ∃ b : OrthonormalBasis (Fin D) ℂ (EuclideanSpace ℂ (Fin D)),
      b ⟨0, hD⟩ = x.1 := by
  letI : NeZero D := ⟨Nat.ne_of_gt hD⟩
  let E := EuclideanSpace ℂ (Fin D)
  let i0 : Fin D := ⟨0, hD⟩
  let v : Fin D → E := fun i ↦ if i = i0 then x.1 else 0
  let s : Set (Fin D) := {i0}
  have hv : Orthonormal ℂ (s.domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i.1 = i0 := by simpa only [s, mem_singleton_iff] using i.2
    have hj : j.1 = i0 := by simpa only [s, mem_singleton_iff] using j.2
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    subst j
    have hxnorm : ‖x.1‖ = 1 := by
      simpa [mem_sphere] using x.2
    simp only [if_pos rfl]
    change ⟪v i.1, v i.1⟫_ℂ = 1
    rw [hi]
    simp only [v, if_pos rfl]
    rw [inner_self_eq_norm_sq_to_K, hxnorm]
    norm_num
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (by simp [E])
  refine ⟨b, ?_⟩
  have h := hb i0 (by simp [s])
  simpa [v, i0] using h

def unitaryMatrixOfComplexIsometry (D : ℕ)
    (e : EuclideanSpace ℂ (Fin D) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D)) :
    unitary (Matrix (Fin D) (Fin D) ℂ) :=
  (Unitary.map (euclideanCLMToMatrixStarMonoidHom D))
      (Unitary.linearIsometryEquiv.symm e)

@[simp] theorem unitaryVectorComplexIsometry_matrixOfComplexIsometry
    (D : ℕ)
    (e : EuclideanSpace ℂ (Fin D) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D)) :
    unitaryVectorComplexIsometry D (unitaryMatrixOfComplexIsometry D e) = e := by
  have hu :
      (Unitary.map (matrixToEuclideanCLMStarMonoidHom D))
          (unitaryMatrixOfComplexIsometry D e) =
        Unitary.linearIsometryEquiv.symm e := by
    apply Subtype.ext
    change (Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ))
        ((Matrix.toEuclideanCLM (n := Fin D) (𝕜 := ℂ)).symm
          (Unitary.linearIsometryEquiv.symm e :
            EuclideanSpace ℂ (Fin D) →L[ℂ] EuclideanSpace ℂ (Fin D))) = _
    rw [StarAlgEquiv.apply_symm_apply]
  unfold unitaryVectorComplexIsometry
  rw [hu]
  exact (Unitary.linearIsometryEquiv.apply_symm_apply e)

@[simp] theorem unitaryVectorAction_matrixOfComplexIsometry
    (D : ℕ)
    (e : EuclideanSpace ℂ (Fin D) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D))
    (x : EuclideanSpace ℂ (Fin D)) :
    unitaryVectorAction D (unitaryMatrixOfComplexIsometry D e) x = e x := by
  rw [← unitaryVectorComplexIsometry_apply]
  rw [unitaryVectorComplexIsometry_matrixOfComplexIsometry]

theorem exists_unitaryVectorAction_eq
    (D : ℕ) (hD : 0 < D)
    (x y : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    ∃ U : unitary (Matrix (Fin D) (Fin D) ℂ),
      unitaryVectorAction D U x.1 = y.1 := by
  obtain ⟨bx, hbx⟩ := exists_orthonormalBasis_zero_eq D hD x
  obtain ⟨byBasis, hby⟩ := exists_orthonormalBasis_zero_eq D hD y
  let e := bx.equiv byBasis (Equiv.refl (Fin D))
  refine ⟨unitaryMatrixOfComplexIsometry D e, ?_⟩
  rw [unitaryVectorAction_matrixOfComplexIsometry]
  change e x.1 = y.1
  rw [← hbx, ← hby]
  exact OrthonormalBasis.equiv_apply_basis bx byBasis
    (Equiv.refl (Fin D)) ⟨0, hD⟩

@[simp] theorem unitaryVectorAction_one (D : ℕ)
    (x : EuclideanSpace ℂ (Fin D)) :
    unitaryVectorAction D 1 x = x := by
  simp [unitaryVectorAction]

@[simp] theorem unitaryVectorAction_mul (D : ℕ)
    (U V : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : EuclideanSpace ℂ (Fin D)) :
    unitaryVectorAction D (U * V) x =
      unitaryVectorAction D U (unitaryVectorAction D V x) := by
  simp [unitaryVectorAction, map_mul]

def unitarySphereAction (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    sphere (0 : EuclideanSpace ℂ (Fin D)) 1 :=
  ⟨unitaryVectorAction D U x.1, by
    have hnorm := (unitaryVectorRealIsometry D U).norm_map x.1
    rw [unitaryVectorRealIsometry_apply] at hnorm
    simpa [mem_sphere, hnorm] using x.2⟩

@[simp] theorem unitarySphereAction_coe (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    (unitarySphereAction D U x).1 = unitaryVectorAction D U x.1 := by
  rfl

set_option maxHeartbeats 800000 in
theorem continuous_unitarySphereAction (D : ℕ) :
    Continuous (fun z : unitary (Matrix (Fin D) (Fin D) ℂ) ×
      sphere (0 : EuclideanSpace ℂ (Fin D)) 1 =>
        unitarySphereAction D z.1 z.2) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : unitary (Matrix (Fin D) (Fin D) ℂ) ×
      sphere (0 : EuclideanSpace ℂ (Fin D)) 1 => WithLp.toLp 2
    (Matrix.mulVec (z.1 : Matrix (Fin D) (Fin D) ℂ)
      (WithLp.ofLp z.2.1)))
  fun_prop

theorem continuous_unitarySphereAction_fixed_point (D : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    Continuous (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) ↦
      unitarySphereAction D U x) := by
  apply continuous_induced_rng.2
  change Continuous (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) ↦
    WithLp.toLp 2 (Matrix.mulVec
      (U : Matrix (Fin D) (Fin D) ℂ) (WithLp.ofLp x.1)))
  fun_prop

theorem continuous_unitarySphereAction_fixed_unitary (D : ℕ)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    Continuous (unitarySphereAction D U) := by
  apply continuous_induced_rng.2
  change Continuous (fun x : sphere
      (0 : EuclideanSpace ℂ (Fin D)) 1 ↦
    WithLp.toLp 2 (Matrix.mulVec
      (U : Matrix (Fin D) (Fin D) ℂ) (WithLp.ofLp x.1)))
  fun_prop

theorem continuous_unitarySphereAction_swap (D : ℕ) :
    Continuous (fun z : sphere (0 : EuclideanSpace ℂ (Fin D)) 1 ×
      unitary (Matrix (Fin D) (Fin D) ℂ) ↦
        unitarySphereAction D z.2 z.1) := by
  apply continuous_induced_rng.2
  change Continuous (fun z : sphere
      (0 : EuclideanSpace ℂ (Fin D)) 1 ×
      unitary (Matrix (Fin D) (Fin D) ℂ) ↦
    WithLp.toLp 2 (Matrix.mulVec
      (z.2 : Matrix (Fin D) (Fin D) ℂ) (WithLp.ofLp z.1.1)))
  fun_prop

@[simp] theorem unitarySphereAction_mul (D : ℕ)
    (U V : unitary (Matrix (Fin D) (Fin D) ℂ))
    (x : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    unitarySphereAction D (U * V) x =
      unitarySphereAction D U (unitarySphereAction D V x) := by
  apply Subtype.ext
  simp

theorem exists_unitarySphereAction_eq
    (D : ℕ) (hD : 0 < D)
    (x y : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    ∃ U : unitary (Matrix (Fin D) (Fin D) ℂ),
      unitarySphereAction D U x = y := by
  obtain ⟨U, hU⟩ := exists_unitaryVectorAction_eq D hD x y
  refine ⟨U, ?_⟩
  apply Subtype.ext
  exact hU

theorem complexUnitSphereHaarLaw_map_unitarySphereAction
    (D : ℕ) (hD : 0 < D)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ)) :
    Measure.map (unitarySphereAction D U)
        (complexUnitSphereHaarLaw (Fin D)) =
      complexUnitSphereHaarLaw (Fin D) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have heq : unitarySphereAction D U =
      unitSphereLinearIsometryAction (unitaryVectorRealIsometry D U) := by
    funext x
    apply Subtype.ext
    rfl
  rw [heq]
  exact complexUnitSphereHaarLaw_map_linearIsometry
    (Fin D) (unitaryVectorRealIsometry D U)

theorem integral_comp_unitarySphereAction_real
    (D : ℕ) (hD : 0 < D)
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (f : sphere (0 : EuclideanSpace ℂ (Fin D)) 1 → ℝ)
    (hf : Continuous f) :
    (∫ x, f (unitarySphereAction D U x)
        ∂complexUnitSphereHaarLaw (Fin D)) =
      ∫ x, f x ∂complexUnitSphereHaarLaw (Fin D) := by
  have haction : Measurable (unitarySphereAction D U) :=
    (continuous_unitarySphereAction_fixed_unitary D U).measurable
  calc
    (∫ x, f (unitarySphereAction D U x)
        ∂complexUnitSphereHaarLaw (Fin D)) =
        ∫ y, f y ∂Measure.map (unitarySphereAction D U)
          (complexUnitSphereHaarLaw (Fin D)) := by
      symm
      exact integral_map haction.aemeasurable hf.aestronglyMeasurable
    _ = ∫ x, f x ∂complexUnitSphereHaarLaw (Fin D) := by
      rw [complexUnitSphereHaarLaw_map_unitarySphereAction D hD]

set_option maxHeartbeats 400000 in
theorem map_unitarySphereAction_unitaryHaarProbability
    (D : ℕ) (hD : 0 < D)
    (v : sphere (0 : EuclideanSpace ℂ (Fin D)) 1) :
    Measure.map (fun U : unitary (Matrix (Fin D) (Fin D) ℂ) =>
        unitarySphereAction D U v) (unitaryHaarProbability D) =
      complexUnitSphereHaarLaw (Fin D) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  let G := unitary (Matrix (Fin D) (Fin D) ℂ)
  let S := sphere (0 : EuclideanSpace ℂ (Fin D)) 1
  let μ : Measure G := unitaryHaarProbability D
  let σ : Measure S := complexUnitSphereHaarLaw (Fin D)
  let orbit : G → S := fun U ↦ unitarySphereAction D U v
  have horbit : Continuous orbit :=
    continuous_unitarySphereAction_fixed_point D v
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply horbit.measurable hA]
  let indicatorA : S → ENNReal := A.indicator (fun _ ↦ 1)
  let φ : S → G → ENNReal :=
    fun x U ↦ indicatorA (unitarySphereAction D U x)
  have hindicatorA : Measurable indicatorA :=
    measurable_const.indicator hA
  have hactionSwap : Measurable (fun z : S × G ↦
      unitarySphereAction D z.2 z.1) :=
    (continuous_unitarySphereAction_swap D).measurable
  have hφ : Measurable (Function.uncurry φ) :=
    hindicatorA.comp hactionSwap
  have havg_const (x : S) :
      (∫⁻ U : G, φ x U ∂μ) = ∫⁻ U : G, φ v U ∂μ := by
    obtain ⟨V, hV⟩ := exists_unitarySphereAction_eq D hD v x
    let g : G → ENNReal := fun U ↦ φ v U
    calc
      (∫⁻ U : G, φ x U ∂μ) = ∫⁻ U : G, g (U * V) ∂μ := by
        apply lintegral_congr
        intro U
        unfold g φ
        rw [unitarySphereAction_mul, hV]
      _ = ∫⁻ U : G, g U ∂μ := lintegral_mul_right_eq_self g V
      _ = ∫⁻ U : G, φ v U ∂μ := by rfl
  have hfixed (U : G) : (∫⁻ x : S, φ x U ∂σ) = σ A := by
    have haction : Measurable (unitarySphereAction D U) :=
      (continuous_unitarySphereAction_fixed_unitary D U).measurable
    have hpre : MeasurableSet ((unitarySphereAction D U) ⁻¹' A) :=
      hA.preimage haction
    change (∫⁻ x : S,
      ((unitarySphereAction D U) ⁻¹' A).indicator 1 x ∂σ) = σ A
    rw [MeasureTheory.lintegral_indicator_one hpre]
    have hmap := complexUnitSphereHaarLaw_map_unitarySphereAction D hD U
    have happ := congrArg (fun η : Measure S ↦ η A) hmap
    rw [Measure.map_apply haction hA] at happ
    exact happ
  calc
    μ (orbit ⁻¹' A) = ∫⁻ U : G, φ v U ∂μ := by
      change μ ((fun U : G ↦ unitarySphereAction D U v) ⁻¹' A) = _
      rw [← MeasureTheory.lintegral_indicator_one
        (hA.preimage horbit.measurable)]
      rfl
    _ = ∫⁻ x : S, (∫⁻ U : G, φ x U ∂μ) ∂σ := by
      symm
      calc
        (∫⁻ x : S, (∫⁻ U : G, φ x U ∂μ) ∂σ) =
            ∫⁻ _x : S, (∫⁻ U : G, φ v U ∂μ) ∂σ := by
          apply lintegral_congr
          exact havg_const
        _ = ∫⁻ U : G, φ v U ∂μ := by simp
    _ = ∫⁻ U : G, (∫⁻ x : S, φ x U ∂σ) ∂μ := by
      calc
        (∫⁻ x : S, (∫⁻ U : G, φ x U ∂μ) ∂σ) =
            ∫⁻ z : S × G, Function.uncurry φ z ∂σ.prod μ := by
          symm
          exact lintegral_prod _ hφ.aemeasurable
        _ = ∫⁻ U : G, (∫⁻ x : S, φ x U ∂σ) ∂μ :=
          lintegral_prod_symm _ hφ.aemeasurable
    _ = ∫⁻ _U : G, σ A ∂μ := by
      apply lintegral_congr
      exact hfixed
    _ = σ A := by simp

end
end TomographyOracleCore
