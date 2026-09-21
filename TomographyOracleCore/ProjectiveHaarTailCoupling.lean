import TomographyOracleCore.ProjectiveHaarHardRatio
import TomographyOracleCore.GaussianRadialDirectionIndependence

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory Metric Set
open scoped BigOperators InnerProductSpace RealInnerProductSpace

noncomputable section

/-!
# The tail block as the orthogonal Gaussian factor

This file identifies the real orthogonal complement of the first two complex
coordinates in `ℂ^(2+k)` with the literal `k`-coordinate complex tail.  It is
the deterministic coordinate bridge required to combine the independent
head/tail Gaussian theorem with the complex-projective second moment.
-/

/-- Embed a `k`-coordinate complex vector into the last `k` coordinates of
`ℂ^(2+k)`, filling the first two coordinates with zero. -/
def complexHaarTailEmbedAmbient (k : ℕ)
    (x : EuclideanSpace ℂ (Fin k)) :
    EuclideanSpace ℂ (Fin (2 + k)) :=
  WithLp.toLp 2 (fun q ↦
    Sum.elim (fun _ : Fin 2 ↦ 0) (fun j ↦ x j)
      (finSumFinEquiv.symm q))

@[simp] theorem complexHaarTailEmbedAmbient_apply_castAdd (k : ℕ)
    (x : EuclideanSpace ℂ (Fin k)) (i : Fin 2) :
    complexHaarTailEmbedAmbient k x (Fin.castAdd k i) = 0 := by
  simp [complexHaarTailEmbedAmbient]

@[simp] theorem complexHaarTailEmbedAmbient_apply_natAdd (k : ℕ)
    (x : EuclideanSpace ℂ (Fin k)) (j : Fin k) :
    complexHaarTailEmbedAmbient k x (Fin.natAdd 2 j) = x j := by
  simp [complexHaarTailEmbedAmbient]

/-- The literal tail embedding lands in the real orthogonal complement of
the literal two-complex-dimensional head. -/
theorem complexHaarTailEmbedAmbient_mem_orthogonal (k : ℕ)
    (x : EuclideanSpace ℂ (Fin k)) :
    complexHaarTailEmbedAmbient k x ∈
      (complexHaarHeadRealSubspace k).orthogonal := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  simp only [PiLp.inner_apply]
  rw [Fin.sum_univ_add]
  have hhead : (∑ i : Fin 2,
      ⟪u (Fin.castAdd k i),
        complexHaarTailEmbedAmbient k x (Fin.castAdd k i)⟫_ℝ) = 0 := by
    simp
  have htail : (∑ j : Fin k,
      ⟪u (Fin.natAdd 2 j),
        complexHaarTailEmbedAmbient k x (Fin.natAdd 2 j)⟫_ℝ) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hu j]
    simp
  rw [hhead, htail, add_zero]

/-- The literal tail embedding preserves the real Hilbert norm. -/
theorem complexHaarTailEmbedAmbient_norm (k : ℕ)
    (x : EuclideanSpace ℂ (Fin k)) :
    ‖complexHaarTailEmbedAmbient k x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Fin.sum_univ_add]
  simp

/-- Linear-isometric tail embedding, with codomain restricted to the
orthogonal complement of the head. -/
def complexHaarTailLinearIsometry (k : ℕ) :
    EuclideanSpace ℂ (Fin k) →ₗᵢ[ℝ]
      (complexHaarHeadRealSubspace k).orthogonal where
  toFun x := ⟨complexHaarTailEmbedAmbient k x,
    complexHaarTailEmbedAmbient_mem_orthogonal k x⟩
  map_add' x y := by
    apply Subtype.ext
    ext q
    cases hq : finSumFinEquiv.symm q <;>
      simp [complexHaarTailEmbedAmbient, hq]
  map_smul' c x := by
    apply Subtype.ext
    ext q
    cases hq : finSumFinEquiv.symm q <;>
      simp [complexHaarTailEmbedAmbient, hq]
  norm_map' x := complexHaarTailEmbedAmbient_norm k x

/-- The complex `k`-coordinate tail has real dimension `2k`. -/
theorem finrank_complexEuclideanSpace_real_tailBlock (k : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin k)) = 2 * k := by
  exact finrank_complexEuclideanSpace_real_headBlock k

/-- The literal complex tail is exactly, not merely contained in, the real
orthogonal complement of the two-coordinate head. -/
def complexHaarTailRealIsometryEquiv (k : ℕ) :
    EuclideanSpace ℂ (Fin k) ≃ₗᵢ[ℝ]
      (complexHaarHeadRealSubspace k).orthogonal :=
  LinearIsometryEquiv.ofSurjective (complexHaarTailLinearIsometry k)
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (by rw [finrank_complexEuclideanSpace_real_tailBlock,
        finrank_complexHaarHeadRealSubspace_orthogonal])).mp
      (complexHaarTailLinearIsometry k).injective)

/-! ## Literal coordinates of the Gaussian tail projection -/

/-- Extract the final `k` complex coordinates from an ambient vector. -/
def complexHaarTailCoordAmbient (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    EuclideanSpace ℂ (Fin k) :=
  WithLp.toLp 2 (fun j ↦ x (Fin.natAdd 2 j))

@[simp] theorem complexHaarTailCoordAmbient_apply (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) (j : Fin k) :
    complexHaarTailCoordAmbient k x j = x (Fin.natAdd 2 j) := rfl

/-- Embedding the extracted tail is exactly subtraction of the head
projection. -/
theorem complexHaarTailEmbed_coord_eq_sub_headPart (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    complexHaarTailEmbedAmbient k (complexHaarTailCoordAmbient k x) =
      x - complexHaarHeadPart k x := by
  ext q
  generalize hq : finSumFinEquiv.symm q = z
  cases z with
  | inl i =>
      have hqi : q = Fin.castAdd k i := by
        simpa using congrArg finSumFinEquiv hq
      subst q
      simp
  | inr j =>
      have hqj : q = Fin.natAdd 2 j := by
        simpa using congrArg finSumFinEquiv hq
      subst q
      simp

/-- The orthogonal-complement projection is the literal zero-head tail
embedding. -/
theorem complexHaarTailOrthogonalProjection_coe (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    ((complexHaarHeadRealSubspace k).orthogonal.orthogonalProjectionOnto x :
      EuclideanSpace ℂ (Fin (2 + k))) =
      complexHaarTailEmbedAmbient k (complexHaarTailCoordAmbient k x) := by
  change (complexHaarHeadRealSubspace k).orthogonal.starProjection x = _
  rw [Submodule.starProjection_orthogonal]
  change x - (complexHaarHeadRealSubspace k).starProjection x = _
  rw [complexHaarHeadPart_is_projection]
  exact (complexHaarTailEmbed_coord_eq_sub_headPart k x).symm

@[simp] theorem complexHaarTailRealIsometryEquiv_symm_projection (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    (complexHaarTailRealIsometryEquiv k).symm
      ((complexHaarHeadRealSubspace k).orthogonal.orthogonalProjectionOnto x) =
      complexHaarTailCoordAmbient k x := by
  apply (complexHaarTailRealIsometryEquiv k).injective
  rw [(complexHaarTailRealIsometryEquiv k).apply_symm_apply]
  apply Subtype.ext
  exact complexHaarTailOrthogonalProjection_coe k x

/-- Under the ambient standard Gaussian, the extracted literal complex tail
is itself a standard `k`-coordinate complex Gaussian. -/
theorem hasLaw_complexHaarTailCoordAmbient_stdGaussian (k : ℕ) :
    HasLaw (complexHaarTailCoordAmbient k)
      (stdGaussian (EuclideanSpace ℂ (Fin k)))
      (stdGaussian (EuclideanSpace ℂ (Fin (2 + k)))) := by
  let K := complexHaarHeadRealSubspace k
  have hproj := LogdetLean.hasLaw_orthogonalComplementProjection_stdGaussian K
  have hequiv : HasLaw
      (complexHaarTailRealIsometryEquiv k).symm
      (stdGaussian (EuclideanSpace ℂ (Fin k)))
      (stdGaussian K.orthogonal) := by
    refine ⟨(complexHaarTailRealIsometryEquiv k).symm.continuous.measurable.aemeasurable,
      ?_⟩
    exact stdGaussian_map (complexHaarTailRealIsometryEquiv k).symm
  have hcomp := hequiv.fun_comp hproj
  apply hcomp.congr
  exact Filter.Eventually.of_forall fun x ↦ by
    exact (complexHaarTailRealIsometryEquiv_symm_projection k x).symm

/-! ## Deterministic factorization of the singular tail score -/

/-- The literal `k`-coordinate tail of a unit vector. -/
def complexHaarTailVector (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    EuclideanSpace ℂ (Fin k) :=
  complexHaarTailCoordAmbient k x.1

@[simp] theorem complexHaarTailVector_apply (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) (j : Fin k) :
    complexHaarTailVector k x j = x.1 (Fin.natAdd 2 j) := rfl

/-- On the ambient unit sphere, tail squared norm is one minus the
two-coordinate head mass. -/
theorem complexHaarTailVector_norm_sq (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    ‖complexHaarTailVector k x‖ ^ 2 =
      1 - complexHaarHeadMass k x := by
  have hxnorm : ‖x.1‖ ^ 2 = 1 := by
    have hx : ‖x.1‖ = 1 := by
      simpa [mem_sphere] using x.2
    rw [hx]
    norm_num
  rw [EuclideanSpace.norm_sq_eq] at hxnorm ⊢
  rw [Fin.sum_univ_add] at hxnorm
  unfold complexHaarHeadMass
  simp only [complexHaarTailVector_apply, Complex.normSq_eq_norm_sq]
  linarith

/-- Totalized normalized tail direction.  Its value when the tail vanishes
is irrelevant for the Haar integral and is fixed to zero. -/
def complexHaarTailDirection (k : ℕ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    EuclideanSpace ℂ (Fin k) :=
  LogdetLean.unitDirection (complexHaarTailVector k x)

/-- Every quadratic form scales into squared radius times its value on the
totalized unit direction. -/
theorem hermitianQuadraticValue_unitDirection (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (y : EuclideanSpace ℂ (Fin k)) :
    hermitianQuadraticValue A y =
      ‖y‖ ^ 2 *
        hermitianQuadraticValue A (LogdetLean.unitDirection y) := by
  by_cases hy : y = 0
  · subst y
    simp [hermitianQuadraticValue, LogdetLean.unitDirection]
  · simp only [LogdetLean.unitDirection, if_neg hy]
    unfold hermitianQuadraticValue
    simp
    have hnorm : ‖y‖ ≠ 0 := norm_ne_zero_iff.mpr hy
    field_simp

/-- The unnormalized tail quadratic score factors into tail mass and the
normalized-direction score. -/
theorem complexHaarTailQuadratic_factor (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    hermitianQuadraticValue A (complexHaarTailVector k x) =
      (1 - complexHaarHeadMass k x) *
        hermitianQuadraticValue A (complexHaarTailDirection k x) := by
  rw [hermitianQuadraticValue_unitDirection]
  rw [complexHaarTailVector_norm_sq]
  rfl

/-- Exact pointwise factorization of the singular block-ratio observable. -/
theorem complexHaarTailRatio_factor (k : ℕ)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (2 + k))) 1) :
    (hermitianQuadraticValue A (complexHaarTailVector k x)) ^ 2 /
        complexHaarHeadMass k x =
      ((1 - complexHaarHeadMass k x) ^ 2 /
        complexHaarHeadMass k x) *
        (hermitianQuadraticValue A (complexHaarTailDirection k x)) ^ 2 := by
  rw [complexHaarTailQuadratic_factor]
  ring

/-! ## Independence of the block radius and normalized tail direction -/

/-- If `f(Y)` and `g(Y)` are independent under the right factor of a product
probability, then every measurable function of the left factor and `f(Y)` is
independent of `g(Y)`. -/
theorem indepFun_prod_comp_of_indepFun_right
    {A B C D : Type*}
    [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : B → C) (g : B → D) (φ : A × C → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hφ : Measurable φ)
    (hfg : IndepFun f g ν) :
    IndepFun
      (fun z : A × B ↦ φ (z.1, f z.2))
      (fun z : A × B ↦ g z.2)
      (μ.prod ν) := by
  let pair : B → C × D := fun b ↦ (f b, g b)
  let Q : A × (C × D) → ℝ × D :=
    fun z ↦ (φ (z.1, z.2.1), z.2.2)
  let ψ : A × C → ℝ := fun z ↦ φ z
  have hpair : Measurable pair := hf.prodMk hg
  have hQ : Measurable Q := by fun_prop
  have hψ : Measurable ψ := hφ
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (by fun_prop) (by fun_prop)).2
  have hpairlaw : Measure.map pair ν =
      (Measure.map f ν).prod (Measure.map g ν) :=
    hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hsplitPair :
      Measure.map (Prod.map id pair) (μ.prod ν) =
        μ.prod (Measure.map pair ν) := by
    rw [← Measure.map_prod_map μ ν measurable_id hpair]
    simp
  have hleft :
      Measure.map
          (fun z : A × B ↦ (φ (z.1, f z.2), g z.2)) (μ.prod ν) =
        Measure.map Q (μ.prod (Measure.map pair ν)) := by
    rw [← hsplitPair, Measure.map_map hQ (by fun_prop)]
    congr 1
  have hQassoc : Q ∘ MeasurableEquiv.prodAssoc = Prod.map ψ id := by
    funext z
    rfl
  have hjoint :
      Measure.map Q (μ.prod (Measure.map pair ν)) =
        (Measure.map ψ (μ.prod (Measure.map f ν))).prod
          (Measure.map g ν) := by
    rw [hpairlaw]
    rw [← (measurePreserving_prodAssoc μ (Measure.map f ν)
      (Measure.map g ν)).map_eq]
    rw [Measure.map_map hQ MeasurableEquiv.prodAssoc.measurable]
    rw [hQassoc]
    rw [← Measure.map_prod_map (μ.prod (Measure.map f ν))
      (Measure.map g ν) hψ measurable_id]
    simp
  have hfirst :
      Measure.map (fun z : A × B ↦ φ (z.1, f z.2)) (μ.prod ν) =
        Measure.map ψ (μ.prod (Measure.map f ν)) := by
    have hsplit : Measure.map (Prod.map id f) (μ.prod ν) =
        μ.prod (Measure.map f ν) := by
      rw [← Measure.map_prod_map μ ν measurable_id hf]
      simp
    rw [← hsplit, Measure.map_map hψ (by fun_prop)]
    congr 1
  have hsecond :
      Measure.map (fun z : A × B ↦ g z.2) (μ.prod ν) =
        Measure.map g ν := by
    rw [← Function.comp_def, ← Measure.map_map hg measurable_snd,
      Measure.map_snd_prod]
    simp
  rw [hleft, hjoint, hfirst, hsecond]

/-- Independence is transported along a measurable random variable with a
specified law. -/
theorem IndepFun.fun_comp_hasLaw
    {Ω X Y Z : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace Z]
    {P : Measure Ω} {μ : Measure X}
    [IsFiniteMeasure P] [IsFiniteMeasure μ]
    (f : X → Y) (g : X → Z) (W : Ω → X)
    (hf : Measurable f) (hg : Measurable g)
    (hfg : IndepFun f g μ) (hWmeas : Measurable W)
    (hW : HasLaw W μ P) :
    IndepFun (f ∘ W) (g ∘ W) P := by
  apply (indepFun_iff_map_prod_eq_prod_map_map
    (hf.comp_aemeasurable hWmeas.aemeasurable)
    (hg.comp_aemeasurable hWmeas.aemeasurable)).2
  calc
    Measure.map (fun ω ↦ ((f ∘ W) ω, (g ∘ W) ω)) P =
        Measure.map (fun x ↦ (f x, g x)) (Measure.map W P) := by
      rw [Measure.map_map (hf.prodMk hg) hWmeas]
      rfl
    _ = Measure.map (fun x ↦ (f x, g x)) μ := by rw [hW.map_eq]
    _ = (Measure.map f μ).prod (Measure.map g μ) :=
      hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
    _ = (Measure.map f (Measure.map W P)).prod
        (Measure.map g (Measure.map W P)) := by rw [hW.map_eq]
    _ = (Measure.map (f ∘ W) P).prod
        (Measure.map (g ∘ W) P) := by
      rw [Measure.map_map hf hWmeas, Measure.map_map hg hWmeas]

/-- Totalized unit direction commutes with a real linear isometric
equivalence. -/
theorem unitDirection_linearIsometryEquiv
    {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [InnerProductSpace ℝ E] [InnerProductSpace ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (x : E) :
    LogdetLean.unitDirection (e x) =
      e (LogdetLean.unitDirection x) := by
  by_cases hx : x = 0
  · subst x
    simp [LogdetLean.unitDirection]
  · have hex : e x ≠ 0 := by
      simpa using e.injective.ne hx
    simp only [LogdetLean.unitDirection, if_neg hx, if_neg hex]
    rw [e.norm_map, map_smul]

/-- Tail normalization computed in the orthogonal complement agrees with
normalization of the extracted literal `k`-coordinate tail. -/
theorem tailDirection_projection_eq_coord (k : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 + k))) :
    (complexHaarTailRealIsometryEquiv k).symm
        (LogdetLean.unitDirection
          ((complexHaarHeadRealSubspace k).orthogonal
            |>.orthogonalProjectionOnto x)) =
      LogdetLean.unitDirection (complexHaarTailCoordAmbient k x) := by
  rw [← unitDirection_linearIsometryEquiv
    (complexHaarTailRealIsometryEquiv k).symm]
  rw [complexHaarTailRealIsometryEquiv_symm_projection]

/-- Under the ambient standard Gaussian, the two-block energy fraction and
the normalized complex tail direction are independent. -/
theorem indepFun_complexHaarAmbientHeadFraction_tailDirection_stdGaussian
    (k : ℕ) (hk : 1 ≤ k) :
    IndepFun (complexHaarAmbientHeadFraction k)
      (fun x : EuclideanSpace ℂ (Fin (2 + k)) ↦
        LogdetLean.unitDirection (complexHaarTailCoordAmbient k x))
      (stdGaussian (EuclideanSpace ℂ (Fin (2 + k)))) := by
  let E := EuclideanSpace ℂ (Fin (2 + k))
  let K := complexHaarHeadRealSubspace k
  let T := K.orthogonal
  let e := complexHaarTailRealIsometryEquiv k
  let r : T → ℝ := fun t ↦ ‖t‖ ^ 2
  let d : T → T := LogdetLean.unitDirection
  let φ : K × ℝ → ℝ :=
    fun z ↦ ‖z.1‖ ^ 2 / (‖z.1‖ ^ 2 + z.2)
  let F : K × T → ℝ := fun z ↦ φ (z.1, r z.2)
  let G : K × T → EuclideanSpace ℂ (Fin k) :=
    fun z ↦ e.symm (d z.2)
  let Z : E → K × T := fun x ↦
    (K.orthogonalProjectionOnto x, T.orthogonalProjectionOnto x)
  letI : Nontrivial T :=
    Module.nontrivial_of_finrank_pos (by
      rw [show Module.finrank ℝ T = 2 * k by
        exact finrank_complexHaarHeadRealSubspace_orthogonal k]
      omega)
  have hrad : IndepFun r d (stdGaussian T) := by
    exact indepFun_normSq_unitDirection_stdGaussian
  have hprod0 : IndepFun F (fun z : K × T ↦ d z.2)
      ((stdGaussian K).prod (stdGaussian T)) := by
    exact indepFun_prod_comp_of_indepFun_right
      (stdGaussian K) (stdGaussian T) r d φ
      (by fun_prop) LogdetLean.measurable_unitDirection (by fun_prop) hrad
  have hprod : IndepFun F G
      ((stdGaussian K).prod (stdGaussian T)) := by
    exact IndepFun.comp hprod0 measurable_id
      e.symm.continuous.measurable
  have hZ : HasLaw Z ((stdGaussian K).prod (stdGaussian T))
      (stdGaussian E) := by
    exact LogdetLean.hasLaw_orthogonalProjections_prod_stdGaussian K
  have hG : Measurable G := by
    exact e.symm.continuous.measurable.comp
      (LogdetLean.measurable_unitDirection.comp measurable_snd)
  have hZmeas : Measurable Z := by fun_prop
  have hcomp := IndepFun.fun_comp_hasLaw F G Z
    (by fun_prop) hG hprod hZmeas hZ
  apply hcomp.congr
  · filter_upwards [] with x
    change F (Z x) = complexHaarAmbientHeadFraction k x
    dsimp only [complexHaarAmbientHeadFraction, F, φ, r, Z, T, K]
    symm
    rw [← LogdetLean.normSq_eq_projection_add_orthogonalComplement
      (complexHaarHeadRealSubspace k) x]
  · filter_upwards [] with x
    change G (Z x) =
      LogdetLean.unitDirection (complexHaarTailCoordAmbient k x)
    dsimp only [G, Z, d, e, T, K]
    exact tailDirection_projection_eq_coord k x

end

end TomographyOracleCore
