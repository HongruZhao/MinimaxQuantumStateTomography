import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory

/-!
# Repeated-shot product scores

This file contains only the generic probability layer for a scalar score of
independent, identically distributed one-shot outcomes.  The `Fin (B * m)`
coordinates are reindexed as `Fin B × Fin m`; the curried view exposes the
independent blocks used in product-law identities.
-/

namespace PhysicalProductScore

section IndependenceTransport

/-- Independence is preserved when all random variables are pulled back along
a measure-preserving map. -/
theorem iIndepFun_comp_measurePreserving
    {I Omega Omega' : Type*} [Fintype I]
    [MeasurableSpace Omega] [MeasurableSpace Omega']
    {Target : I → Type*} [∀ i, MeasurableSpace (Target i)]
    {mu : Measure Omega} {nu : Measure Omega'} [IsProbabilityMeasure mu]
    {e : Omega → Omega'} (he : MeasurePreserving e mu nu)
    {f : ∀ i, Omega' → Target i}
    (hf : ∀ i, Measurable (f i)) (hindep : iIndepFun f nu) :
    iIndepFun (fun i omega ↦ f i (e omega)) mu := by
  classical
  have hcomp : ∀ i, AEMeasurable (fun omega ↦ f i (e omega)) mu :=
    fun i ↦ ((hf i).comp he.measurable).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map hcomp).2
  calc
    mu.map (fun omega i ↦ f i (e omega)) =
        (mu.map e).map (fun omega' i ↦ f i omega') := by
      simpa [Function.comp_def] using
        (Measure.map_map (measurable_pi_lambda _ hf) he.measurable).symm
    _ = nu.map (fun omega' i ↦ f i omega') := by rw [he.map_eq]
    _ = Measure.pi (fun i ↦ nu.map (f i)) :=
      hindep.map_fun_eq_pi_map fun i ↦ (hf i).aemeasurable
    _ = Measure.pi (fun i ↦ mu.map (fun omega ↦ f i (e omega))) := by
      congr with i
      rw [← he.map_eq, Measure.map_map (hf i) he.measurable]
      rfl

end IndependenceTransport

section ProductLaw

variable {Outcome Direction : Type*} [MeasurableSpace Outcome]
variable (B m : ℕ)

/-- The canonical coordinate assigned to block `b` and within-block index `j`. -/
def blockWithinIndex (b : Fin B) (j : Fin m) : Fin (B * m) :=
  finProdFinEquiv (b, j)

theorem blockWithinIndex_pair_injective :
    Function.Injective
      (fun p : Fin B × Fin m ↦ blockWithinIndex B m p.1 p.2) :=
  finProdFinEquiv.injective

theorem blockWithinIndex_within_injective (b : Fin B) :
    Function.Injective (blockWithinIndex B m b) := by
  intro j k hjk
  have hpair : (b, j) = (b, k) := finProdFinEquiv.injective hjk
  exact congrArg Prod.snd hpair

/-- The flat repeated-shot product law indexed by `Fin (B * m)`. -/
noncomputable def finProductLaw (nu : Measure Outcome) :
    Measure (Fin (B * m) → Outcome) :=
  Measure.pi fun _ : Fin (B * m) ↦ nu

/-- The same product law indexed by block/within pairs. -/
noncomputable def pairProductLaw (nu : Measure Outcome) :
    Measure (Fin B × Fin m → Outcome) :=
  Measure.pi fun _ : Fin B × Fin m ↦ nu

/-- The same product law, curried into independent block vectors. -/
noncomputable def blockedProductLaw (nu : Measure Outcome) :
    Measure (Fin B → Fin m → Outcome) :=
  Measure.pi fun _ : Fin B ↦ Measure.pi fun _ : Fin m ↦ nu

noncomputable instance finProductLaw_isProbabilityMeasure
    (nu : Measure Outcome) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (finProductLaw B m nu) := by
  unfold finProductLaw
  infer_instance

noncomputable instance pairProductLaw_isProbabilityMeasure
    (nu : Measure Outcome) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (pairProductLaw B m nu) := by
  unfold pairProductLaw
  infer_instance

noncomputable instance blockedProductLaw_isProbabilityMeasure
    (nu : Measure Outcome) [IsProbabilityMeasure nu] :
    IsProbabilityMeasure (blockedProductLaw B m nu) := by
  unfold blockedProductLaw
  infer_instance

/-- Reindex a flat `Fin (B * m)` sample by block/within pairs. -/
noncomputable def finToPairEquiv :
    (Fin (B * m) → Outcome) ≃ᵐ (Fin B × Fin m → Outcome) :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin B × Fin m ↦ Outcome)
    (finProdFinEquiv : Fin B × Fin m ≃ Fin (B * m)).symm

/-- Reindex and curry a flat sample into block vectors. -/
noncomputable def finToBlockedOutcome :
    (Fin (B * m) → Outcome) → (Fin B → Fin m → Outcome) :=
  (MeasurableEquiv.curry (Fin B) (Fin m) Outcome) ∘ finToPairEquiv B m

@[simp]
theorem finToBlockedOutcome_apply
    (observed : Fin (B * m) → Outcome) (b : Fin B) (j : Fin m) :
    finToBlockedOutcome B m observed b j =
      observed (blockWithinIndex B m b j) := by
  simp [finToBlockedOutcome, finToPairEquiv, blockWithinIndex,
    MeasurableEquiv.curry, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft]

theorem finToBlockedOutcome_measurable :
    Measurable (finToBlockedOutcome (Outcome := Outcome) B m) :=
  (MeasurableEquiv.curry (Fin B) (Fin m) Outcome).measurable.comp
    (finToPairEquiv B m).measurable

theorem measurePreserving_finToPair (nu : Measure Outcome)
    [IsProbabilityMeasure nu] :
    MeasurePreserving (finToPairEquiv (Outcome := Outcome) B m)
      (finProductLaw B m nu) (pairProductLaw B m nu) := by
  refine ⟨(finToPairEquiv B m).measurable, ?_⟩
  simpa [finToPairEquiv, finProductLaw, pairProductLaw] using
    (Measure.pi_map_piCongrLeft
      (e := (finProdFinEquiv : Fin B × Fin m ≃ Fin (B * m)).symm)
      (fun _ : Fin B × Fin m ↦ nu))

theorem measurePreserving_pairToBlocked (nu : Measure Outcome)
    [IsProbabilityMeasure nu] :
    MeasurePreserving (MeasurableEquiv.curry (Fin B) (Fin m) Outcome)
      (pairProductLaw B m nu) (blockedProductLaw B m nu) := by
  refine ⟨(MeasurableEquiv.curry (Fin B) (Fin m) Outcome).measurable, ?_⟩
  simpa [pairProductLaw, blockedProductLaw, Measure.infinitePi_eq_pi] using
    (Measure.infinitePi_map_curry
      (μ := fun (_ : Fin B) (_ : Fin m) ↦ nu))

theorem measurePreserving_finToBlocked (nu : Measure Outcome)
    [IsProbabilityMeasure nu] :
    MeasurePreserving (finToBlockedOutcome (Outcome := Outcome) B m)
      (finProductLaw B m nu) (blockedProductLaw B m nu) := by
  simpa [finToBlockedOutcome] using
    (measurePreserving_pairToBlocked B m nu).comp
      (measurePreserving_finToPair B m nu)

/-- A one-shot scalar score evaluated at a flat repeated-shot coordinate. -/
noncomputable def finRawScore (score : Direction → Outcome → ℝ)
    (u : Direction) (b : Fin B) (j : Fin m) :
    (Fin (B * m) → Outcome) → ℝ :=
  fun observed ↦ score u (observed (blockWithinIndex B m b j))

/-- Pull a flat repeated-shot score back to any data space carrying those
outcomes.  In the physical experiment the pullback map will be `Prod.snd`. -/
noncomputable def pullbackFinRawScore {Data : Type*}
    (decode : Data → (Fin (B * m) → Outcome))
    (score : Direction → Outcome → ℝ) (u : Direction) (b : Fin B) (j : Fin m) :
    Data → ℝ :=
  fun observed ↦ finRawScore B m score u b j (decode observed)

/-- The corresponding score in the curried block representation. -/
noncomputable def blockedRawScore (score : Direction → Outcome → ℝ)
    (u : Direction) (b : Fin B) (j : Fin m) :
    (Fin B → Fin m → Outcome) → ℝ :=
  fun observed ↦ score u (observed b j)

theorem finRawScore_measurable (score : Direction → Outcome → ℝ)
    (hscore : ∀ u, Measurable (score u)) (u : Direction) (b : Fin B) (j : Fin m) :
    Measurable (finRawScore B m score u b j) :=
  (hscore u).comp (measurable_pi_apply (blockWithinIndex B m b j))

theorem blockedRawScore_measurable (score : Direction → Outcome → ℝ)
    (hscore : ∀ u, Measurable (score u)) (u : Direction) (b : Fin B) (j : Fin m) :
    Measurable (blockedRawScore B m score u b j) :=
  (hscore u).comp ((measurable_pi_apply j).comp (measurable_pi_apply b))

/-- The block-valued rows are independent under the curried product law. -/
theorem blockedRawScore_rows_iIndep (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (hscore : ∀ u, Measurable (score u))
    (u : Direction) :
    iIndepFun
      (fun b observed j ↦ blockedRawScore B m score u b j observed)
      (blockedProductLaw B m nu) := by
  simpa [blockedRawScore, blockedProductLaw] using
    (iIndepFun_pi
      (μ := fun _ : Fin B ↦ Measure.pi fun _ : Fin m ↦ nu)
      (X := fun _ row j ↦ score u (row j))
      (fun _ ↦ (measurable_pi_lambda _ fun j ↦
        (hscore u).comp (measurable_pi_apply j)).aemeasurable))

/-- The block-valued rows are independent in the flat `Fin (B * m)` model. -/
theorem finRawScore_rows_iIndep (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (hscore : ∀ u, Measurable (score u))
    (u : Direction) :
    iIndepFun (fun b observed j ↦ finRawScore B m score u b j observed)
      (finProductLaw B m nu) := by
  have hblocked := blockedRawScore_rows_iIndep B m nu score hscore u
  have hpull := iIndepFun_comp_measurePreserving
    (measurePreserving_finToBlocked B m nu)
    (fun b ↦ measurable_pi_lambda _ fun j ↦
      blockedRawScore_measurable B m score hscore u b j)
    hblocked
  simpa [finRawScore, blockedRawScore] using hpull

/-- Within each block, the scalar scores are independent. -/
theorem finRawScore_within_iIndep (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (hscore : ∀ u, Measurable (score u))
    (u : Direction) (b : Fin B) :
    iIndepFun (finRawScore B m score u b) (finProductLaw B m nu) := by
  have hall : iIndepFun
      (fun k (observed : Fin (B * m) → Outcome) ↦ score u (observed k))
      (finProductLaw B m nu) := by
    simpa [finProductLaw] using
      (iIndepFun_pi
        (μ := fun _ : Fin (B * m) ↦ nu)
        (X := fun _ ↦ score u)
        (fun _ ↦ (hscore u).aemeasurable))
  change iIndepFun
    (fun j observed ↦ score u (observed (blockWithinIndex B m b j)))
    (finProductLaw B m nu)
  exact iIndepFun.precomp (g := blockWithinIndex B m b)
    (blockWithinIndex_within_injective B m b) hall

/-- Every repeated-shot score has exactly the one-shot expectation. -/
theorem integral_finRawScore (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (u : Direction) (b : Fin B) (j : Fin m)
    (hscore : AEStronglyMeasurable (score u) nu) :
    ∫ observed, finRawScore B m score u b j observed ∂finProductLaw B m nu =
      ∫ outcome, score u outcome ∂nu := by
  simpa [finRawScore, finProductLaw] using
    (integral_comp_eval
      (μ := fun _ : Fin (B * m) ↦ nu)
      (i := blockWithinIndex B m b j) hscore)

/-- `L^p` membership transfers exactly from the one-shot score. -/
theorem memLp_finRawScore (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (u : Direction) (b : Fin B) (j : Fin m)
    (p : ENNReal) (hmem : MemLp (score u) p nu) :
    MemLp (finRawScore B m score u b j) p (finProductLaw B m nu) := by
  change MemLp
    (fun observed ↦ score u (observed (blockWithinIndex B m b j))) p
    (Measure.pi fun _ : Fin (B * m) ↦ nu)
  exact hmem.comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin (B * m) ↦ nu)
      (blockWithinIndex B m b j))

/-- Every repeated-shot score has exactly the one-shot variance. -/
theorem variance_finRawScore (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (u : Direction) (b : Fin B) (j : Fin m)
    (hscore : AEMeasurable (score u) nu) :
    variance (finRawScore B m score u b j) (finProductLaw B m nu) =
      variance (score u) nu := by
  change variance
    (fun observed ↦ score u (observed (blockWithinIndex B m b j)))
    (Measure.pi fun _ : Fin (B * m) ↦ nu) = variance (score u) nu
  simpa using
    (measurePreserving_eval (fun _ : Fin (B * m) ↦ nu)
      (blockWithinIndex B m b j)).variance_fun_comp hscore

/-- Product-measure measurability, independence, and moment facts, bundled into
one theorem.  The expectation and variance conclusions are exact equalities,
so any one-shot mean identity or variance bound transfers by rewriting. -/
theorem finRawScore_product_bridge (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ)
    (hscore : ∀ u, Measurable (score u))
    (hmem : ∀ u, MemLp (score u) 2 nu) :
    (∀ u b j, Measurable (finRawScore B m score u b j)) ∧
    (∀ u, iIndepFun
      (fun b observed j ↦ finRawScore B m score u b j observed)
      (finProductLaw B m nu)) ∧
    (∀ u b, iIndepFun (finRawScore B m score u b) (finProductLaw B m nu)) ∧
    (∀ u b j, MemLp (finRawScore B m score u b j) 2 (finProductLaw B m nu)) ∧
    (∀ u b j,
      ∫ observed, finRawScore B m score u b j observed ∂finProductLaw B m nu =
        ∫ outcome, score u outcome ∂nu) ∧
    (∀ u b j,
      variance (finRawScore B m score u b j) (finProductLaw B m nu) =
        variance (score u) nu) := by
  refine ⟨fun u b j ↦ finRawScore_measurable B m score hscore u b j,
    fun u ↦ finRawScore_rows_iIndep B m nu score hscore u,
    fun u b ↦ finRawScore_within_iIndep B m nu score hscore u b,
    fun u b j ↦ memLp_finRawScore B m nu score u b j 2 (hmem u),
    fun u b j ↦ integral_finRawScore B m nu score u b j
      (hscore u).aestronglyMeasurable,
    fun u b j ↦ variance_finRawScore B m nu score u b j
      (hscore u).aemeasurable⟩

/-- A directly usable hypothesis-transfer form of `finRawScore_product_bridge`.
One-shot mean identities and variance bounds become the corresponding facts
for every block/within coordinate. -/
theorem finRawScore_product_obligations
    (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (score : Direction → Outcome → ℝ) (mean : Direction → ℝ) (kappa : ℝ)
    (hscore : ∀ u, Measurable (score u))
    (hmem : ∀ u, MemLp (score u) 2 nu)
    (hmean : ∀ u, ∫ outcome, score u outcome ∂nu = mean u)
    (hvariance : ∀ u, variance (score u) nu ≤ kappa) :
    (∀ u b j, Measurable (finRawScore B m score u b j)) ∧
    (∀ u, iIndepFun
      (fun b observed j ↦ finRawScore B m score u b j observed)
      (finProductLaw B m nu)) ∧
    (∀ u b, iIndepFun (finRawScore B m score u b) (finProductLaw B m nu)) ∧
    (∀ u b j, MemLp (finRawScore B m score u b j) 2 (finProductLaw B m nu)) ∧
    (∀ u b j,
      ∫ observed, finRawScore B m score u b j observed ∂finProductLaw B m nu =
        mean u) ∧
    (∀ u b j,
      variance (finRawScore B m score u b j) (finProductLaw B m nu) ≤ kappa) := by
  rcases finRawScore_product_bridge B m nu score hscore hmem with
    ⟨hmeas, hrows, hwithin, hmem', hint, hvar⟩
  exact ⟨hmeas, hrows, hwithin, hmem',
    fun u b j ↦ (hint u b j).trans (hmean u),
    fun u b j ↦ (hvar u b j).trans_le (hvariance u)⟩

/-- Product-score obligations after pullback to a larger observed-data space.
Consequently, a physical model only has to prove that its outcome projection
is measure-preserving to the repeated one-shot product law. -/
theorem pullbackFinRawScore_product_obligations
    {Data : Type*} [MeasurableSpace Data]
    {P : Measure Data} [IsProbabilityMeasure P]
    (nu : Measure Outcome) [IsProbabilityMeasure nu]
    (decode : Data → (Fin (B * m) → Outcome))
    (hdecode : MeasurePreserving decode P (finProductLaw B m nu))
    (score : Direction → Outcome → ℝ) (mean : Direction → ℝ) (kappa : ℝ)
    (hscore : ∀ u, Measurable (score u))
    (hmem : ∀ u, MemLp (score u) 2 nu)
    (hmean : ∀ u, ∫ outcome, score u outcome ∂nu = mean u)
    (hvariance : ∀ u, variance (score u) nu ≤ kappa) :
    (∀ u b j, Measurable (pullbackFinRawScore B m decode score u b j)) ∧
    (∀ u, iIndepFun
      (fun b observed j ↦ pullbackFinRawScore B m decode score u b j observed) P) ∧
    (∀ u b, iIndepFun (pullbackFinRawScore B m decode score u b) P) ∧
    (∀ u b j, MemLp (pullbackFinRawScore B m decode score u b j) 2 P) ∧
    (∀ u b j,
      ∫ observed, pullbackFinRawScore B m decode score u b j observed ∂P = mean u) ∧
    (∀ u b j,
      variance (pullbackFinRawScore B m decode score u b j) P ≤ kappa) := by
  have hmeas : ∀ u b j,
      Measurable (pullbackFinRawScore B m decode score u b j) := by
    intro u b j
    exact (finRawScore_measurable B m score hscore u b j).comp hdecode.measurable
  have hrows : ∀ u, iIndepFun
      (fun b observed j ↦ pullbackFinRawScore B m decode score u b j observed) P := by
    intro u
    have h := iIndepFun_comp_measurePreserving hdecode
      (fun b ↦ measurable_pi_lambda _ fun j ↦
        finRawScore_measurable B m score hscore u b j)
      (finRawScore_rows_iIndep B m nu score hscore u)
    simpa [pullbackFinRawScore] using h
  have hwithin : ∀ u b,
      iIndepFun (pullbackFinRawScore B m decode score u b) P := by
    intro u b
    have h := iIndepFun_comp_measurePreserving hdecode
      (fun j ↦ finRawScore_measurable B m score hscore u b j)
      (finRawScore_within_iIndep B m nu score hscore u b)
    change iIndepFun
      (fun j observed ↦ finRawScore B m score u b j (decode observed)) P
    exact h
  have hmem' : ∀ u b j,
      MemLp (pullbackFinRawScore B m decode score u b j) 2 P := by
    intro u b j
    change MemLp
      (fun observed ↦ finRawScore B m score u b j (decode observed)) 2 P
    exact (memLp_finRawScore B m nu score u b j 2 (hmem u)).comp_measurePreserving hdecode
  have hint : ∀ u b j,
      ∫ observed, pullbackFinRawScore B m decode score u b j observed ∂P = mean u := by
    intro u b j
    let f := finRawScore B m score u b j
    have hfmap : AEStronglyMeasurable f (P.map decode) := by
      rw [hdecode.map_eq]
      exact (finRawScore_measurable B m score hscore u b j).aestronglyMeasurable
    calc
      ∫ observed, pullbackFinRawScore B m decode score u b j observed ∂P =
          ∫ outcomes, f outcomes ∂P.map decode := by
        simpa [pullbackFinRawScore, f] using
          (integral_map hdecode.aemeasurable hfmap).symm
      _ = ∫ outcomes, f outcomes ∂finProductLaw B m nu := by rw [hdecode.map_eq]
      _ = ∫ outcome, score u outcome ∂nu :=
        integral_finRawScore B m nu score u b j
          (hscore u).aestronglyMeasurable
      _ = mean u := hmean u
  have hvar : ∀ u b j,
      variance (pullbackFinRawScore B m decode score u b j) P ≤ kappa := by
    intro u b j
    change variance (fun observed ↦ finRawScore B m score u b j (decode observed)) P ≤ kappa
    calc
      variance (fun observed ↦ finRawScore B m score u b j (decode observed)) P =
          variance (finRawScore B m score u b j) (finProductLaw B m nu) := by
        exact hdecode.variance_fun_comp
          (finRawScore_measurable B m score hscore u b j).aemeasurable
      _ = variance (score u) nu :=
        variance_finRawScore B m nu score u b j (hscore u).aemeasurable
      _ ≤ kappa := hvariance u
  exact ⟨hmeas, hrows, hwithin, hmem', hint, hvar⟩

end ProductLaw

end PhysicalProductScore

end TomographyOracleCore
