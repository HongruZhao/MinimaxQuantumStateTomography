import TomographyOracleCore.MathlibImports
import TomographyOracleCore.Structural

namespace TomographyOracleCore
open MeasureTheory ProbabilityTheory

/-! Generic finite maxima, finite argmin measurability, and concentration tools.
Coverings in this module are geometric proof devices. -/

section FiniteSupScore

variable {Direction Candidate : Type*}

/-- The largest absolute residual over a nonempty finite direction set. -/
noncomputable def finiteSupScore
    (directions : Finset Direction) (hdirections : directions.Nonempty)
    (prediction : Candidate → Direction → ℝ) (data : Direction → ℝ)
    (candidate : Candidate) : ℝ := by
  classical
  exact (directions.image fun u ↦ |prediction candidate u - data u|).max'
    (hdirections.image fun u ↦ |prediction candidate u - data u|)

/-- Every directional residual is bounded by the finite sup score. -/
theorem abs_residual_le_finiteSupScore
    (directions : Finset Direction) (hdirections : directions.Nonempty)
    (prediction : Candidate → Direction → ℝ) (data : Direction → ℝ)
    (candidate : Candidate) {u : Direction} (hu : u ∈ directions) :
    |prediction candidate u - data u| ≤
      finiteSupScore directions hdirections prediction data candidate := by
  classical
  unfold finiteSupScore
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨u, hu, rfl⟩

/-- Pointwise control of all residuals controls their finite supremum. -/
theorem finiteSupScore_le
    (directions : Finset Direction) (hdirections : directions.Nonempty)
    (prediction : Candidate → Direction → ℝ) (data : Direction → ℝ)
    (candidate : Candidate) (eta : ℝ)
    (h : ∀ u ∈ directions, |prediction candidate u - data u| ≤ eta) :
    finiteSupScore directions hdirections prediction data candidate ≤ eta := by
  classical
  unfold finiteSupScore
  apply Finset.max'_le
  intro residual hresidual
  rcases Finset.mem_image.mp hresidual with ⟨u, hu, rfl⟩
  exact h u hu

end FiniteSupScore

section FiniteLeastArgmin

variable {Candidate : Type*} [LinearOrder Candidate]

/-- The finite set of candidates attaining the smallest score. -/
noncomputable def finiteMinimizers
    (candidates : Finset Candidate) (score : Candidate → ℝ) :
    Finset Candidate := by
  classical
  exact candidates.filter fun candidate ↦
    ∀ competitor ∈ candidates, score candidate ≤ score competitor

theorem finiteMinimizers_nonempty
    (candidates : Finset Candidate) (hcandidates : candidates.Nonempty)
    (score : Candidate → ℝ) :
    (finiteMinimizers candidates score).Nonempty := by
  classical
  obtain ⟨candidate, hcandidate, hmin⟩ :=
    Finset.exists_min_image candidates score hcandidates
  refine ⟨candidate, ?_⟩
  simp only [finiteMinimizers, Finset.mem_filter]
  exact ⟨hcandidate, hmin⟩

/-- A finite argmin with deterministic tie-breaking: among all minimizers,
choose the least candidate in the supplied linear order. -/
noncomputable def finiteLeastArgmin
    (candidates : Finset Candidate) (hcandidates : candidates.Nonempty)
    (score : Candidate → ℝ) : Candidate :=
  (finiteMinimizers candidates score).min'
    (finiteMinimizers_nonempty candidates hcandidates score)

theorem finiteLeastArgmin_mem
    (candidates : Finset Candidate) (hcandidates : candidates.Nonempty)
    (score : Candidate → ℝ) :
    finiteLeastArgmin candidates hcandidates score ∈ candidates := by
  classical
  have hmem : finiteLeastArgmin candidates hcandidates score ∈
      finiteMinimizers candidates score := by
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).1

theorem finiteLeastArgmin_score_le
    (candidates : Finset Candidate) (hcandidates : candidates.Nonempty)
    (score : Candidate → ℝ) {competitor : Candidate}
    (hcompetitor : competitor ∈ candidates) :
    score (finiteLeastArgmin candidates hcandidates score) ≤ score competitor := by
  classical
  have hmem : finiteLeastArgmin candidates hcandidates score ∈
      finiteMinimizers candidates score := by
    exact Finset.min'_mem _ _
  exact (Finset.mem_filter.mp hmem).2 competitor hcompetitor

end FiniteLeastArgmin

section MeasurableFiniteLeastArgmin

variable {Omega Candidate : Type*} [MeasurableSpace Omega]
  [LinearOrder Candidate]

/-- Event that a fixed candidate minimizes a finite family of measurable
scores. -/
def finiteMinimizerEvent
    (candidates : Finset Candidate) (score : Candidate → Omega → ℝ)
    (candidate : Candidate) : Set Omega :=
  {omega | ∀ competitor ∈ candidates,
    score candidate omega ≤ score competitor omega}

theorem finiteMinimizerEvent_measurable
    (candidates : Finset Candidate) (score : Candidate → Omega → ℝ)
    (hscore : ∀ candidate ∈ candidates, Measurable (score candidate))
    {candidate : Candidate} (hcandidate : candidate ∈ candidates) :
    MeasurableSet (finiteMinimizerEvent candidates score candidate) := by
  rw [show finiteMinimizerEvent candidates score candidate =
      ⋂ competitor ∈ candidates,
        {omega | score candidate omega ≤ score competitor omega} by
    ext omega
    simp [finiteMinimizerEvent]]
  exact Finset.measurableSet_biInter candidates fun competitor hcompetitor ↦
    measurableSet_le (hscore candidate hcandidate)
      (hscore competitor hcompetitor)

/-- Every fiber of the finite, order-tie-broken argmin is measurable when
the candidate scores are measurable.  This is a finite Boolean-combination
proof and uses no measurable-selection theorem. -/
theorem finiteLeastArgmin_fiber_measurable
    (candidates : Finset Candidate) (hcandidates : candidates.Nonempty)
    (score : Candidate → Omega → ℝ)
    (hscore : ∀ candidate ∈ candidates, Measurable (score candidate))
    {candidate : Candidate} (hcandidate : candidate ∈ candidates) :
    MeasurableSet {omega |
      finiteLeastArgmin candidates hcandidates (fun c ↦ score c omega) =
        candidate} := by
  let E := finiteMinimizerEvent candidates score
  have hE : ∀ c ∈ candidates, MeasurableSet (E c) :=
    fun c hc ↦ finiteMinimizerEvent_measurable candidates score hscore hc
  have heq : {omega |
      finiteLeastArgmin candidates hcandidates (fun c ↦ score c omega) =
        candidate} =
      E candidate ∩ ⋂ c ∈ candidates,
        if candidate ≤ c then Set.univ else (E c)ᶜ := by
    ext omega
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · intro hselect
      have hselectedMem :
          finiteLeastArgmin candidates hcandidates
              (fun c ↦ score c omega) ∈
            finiteMinimizers candidates (fun c ↦ score c omega) := by
        unfold finiteLeastArgmin
        exact Finset.min'_mem _ _
      have hcandidateMin : candidate ∈
          finiteMinimizers candidates (fun c ↦ score c omega) := by
        rwa [hselect] at hselectedMem
      refine ⟨?_, ?_⟩
      · exact (Finset.mem_filter.mp hcandidateMin).2
      · intro c hc
        by_cases hle : candidate ≤ c
        · simp [hle]
        · simp only [hle, ↓reduceIte, Set.mem_compl_iff]
          intro hcMin
          have hcMinMem : c ∈ finiteMinimizers candidates
              (fun d ↦ score d omega) :=
            Finset.mem_filter.mpr ⟨hc, hcMin⟩
          have hleast :
              finiteLeastArgmin candidates hcandidates
                  (fun d ↦ score d omega) ≤ c := Finset.min'_le
            (finiteMinimizers candidates (fun d ↦ score d omega)) c hcMinMem
          rw [hselect] at hleast
          exact hle hleast
    · rintro ⟨hcandidateMin, hleast⟩
      apply (Finset.min'_eq_iff
        (finiteMinimizers candidates (fun c ↦ score c omega))
        (finiteMinimizers_nonempty candidates hcandidates _) candidate).2
      refine ⟨Finset.mem_filter.mpr ⟨hcandidate, hcandidateMin⟩, ?_⟩
      intro c hcMin
      have hc : c ∈ candidates := (Finset.mem_filter.mp hcMin).1
      have hcScore : E c omega := (Finset.mem_filter.mp hcMin).2
      specialize hleast c hc
      by_cases hle : candidate ≤ c
      · exact hle
      · simp only [hle, ↓reduceIte, Set.mem_compl_iff] at hleast
        exact False.elim (hleast hcScore)
  rw [heq]
  apply (hE candidate hcandidate).inter
  exact Finset.measurableSet_biInter candidates fun c hc ↦ by
    by_cases hle : candidate ≤ c
    · simp [hle]
    · simp [hle, hE c hc]

end MeasurableFiniteLeastArgmin
/-- Scalar quarter-net lifting.  In the matrix application `h` is an operator
norm and `netError` is the largest quadratic-form error on a `1/4`-net.  The
geometric net argument gives `h ≤ netError + h / 2`; this lemma performs the
exact absorption. -/
theorem quarter_net_lift
    (h netError eta : ℝ)
    (hlift : h ≤ netError + h / 2) (hnet : netError ≤ 2 * eta) :
    h ≤ 4 * eta := by
  linarith

/-- General half-absorption form of the quarter-net calculation. -/
theorem half_error_lift
    (h netError bound : ℝ)
    (hlift : h ≤ netError + h / 2) (hnet : netError ≤ bound) :
    h ≤ 2 * bound := by
  linarith
section SimultaneousEvent

open MeasureTheory

variable {Omega Direction : Type*} [MeasurableSpace Omega]

/-- Finite union bound in the form needed to turn scalar robust estimates into
a simultaneous net event. -/
theorem measure_finite_bad_union_le
    (mu : Measure Omega) (directions : Finset Direction)
    (bad : Direction → Set Omega) (q : ENNReal)
    (hbad : ∀ u ∈ directions, mu (bad u) ≤ q) :
    mu (⋃ u ∈ directions, bad u) ≤ directions.card * q := by
  calc
    mu (⋃ u ∈ directions, bad u) ≤ ∑ u ∈ directions, mu (bad u) :=
      measure_biUnion_finset_le directions bad
    _ ≤ ∑ _u ∈ directions, q := by
      exact Finset.sum_le_sum fun u hu ↦ hbad u hu
    _ = directions.card * q := by simp

/-- Complementary formulation: if the scalar failure probability is at most
`q` in every direction, the event that all directions are accurate has
probability at least `1 - card * q`. -/
theorem measure_simultaneous_good_ge
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (directions : Finset Direction) (bad : Direction → Set Omega) (q : ENNReal)
    (hmeas : ∀ u ∈ directions, MeasurableSet (bad u))
    (hbad : ∀ u ∈ directions, mu (bad u) ≤ q) :
    1 - directions.card * q ≤ mu (⋂ u ∈ directions, (bad u)ᶜ) := by
  let B : Set Omega := ⋃ u ∈ directions, bad u
  have hBmeas : MeasurableSet B := by
    dsimp [B]
    exact Finset.measurableSet_biUnion directions fun u hu ↦ hmeas u hu
  have hunion := measure_finite_bad_union_le mu directions bad q hbad
  have hcompl : (⋂ u ∈ directions, (bad u)ᶜ) = Bᶜ := by
    simp [B]
  rw [hcompl, measure_compl hBmeas (measure_ne_top mu B), measure_univ]
  exact tsub_le_tsub_left hunion 1

end SimultaneousEvent

section ScalarBlockAverage

open MeasureTheory ProbabilityTheory

variable {Omega Index : Type*} [MeasurableSpace Omega]

/-- Arithmetic mean of the observations indexed by a finite block. -/
noncomputable def blockAverage
    (block : Finset Index) (X : Index → Omega → ℝ) : Omega → ℝ :=
  (block.card : ℝ)⁻¹ • ∑ i ∈ block, X i

theorem blockAverage_memLp_two
    (mu : Measure Omega) (block : Finset Index) (X : Index → Omega → ℝ)
    (hX : ∀ i ∈ block, MemLp (X i) 2 mu) :
    MemLp (blockAverage block X) 2 mu := by
  unfold blockAverage
  exact (memLp_finsetSum' block (fun i hi ↦ hX i hi)).const_smul
    ((block.card : ℝ)⁻¹)

/-- A block average of variables with common mean has that same mean. -/
theorem integral_blockAverage
    (mu : Measure Omega) (block : Finset Index) (hblock : block.Nonempty)
    (X : Index → Omega → ℝ) (mean : ℝ)
    (hX : ∀ i ∈ block, Integrable (X i) mu)
    (hmean : ∀ i ∈ block, ∫ omega, X i omega ∂mu = mean) :
    ∫ omega, blockAverage block X omega ∂mu = mean := by
  rw [show blockAverage block X =
      fun omega ↦ (block.card : ℝ)⁻¹ * (∑ i ∈ block, X i omega) by
        ext omega
        simp [blockAverage]]
  rw [integral_const_mul, integral_finsetSum block]
  · have hsum : (∑ i ∈ block, ∫ omega, X i omega ∂mu) =
        ∑ _i ∈ block, mean := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hmean i hi
    rw [hsum]
    have hcard : (block.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr hblock
    rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hcard, one_mul]
  · exact fun i hi ↦ hX i hi

/-- Pairwise independence reduces the variance of a block average by the
block cardinality. -/
theorem variance_blockAverage_le
    (mu : Measure Omega) (block : Finset Index) (hblock : block.Nonempty)
    (X : Index → Omega → ℝ) (varianceBound : ℝ)
    (hX : ∀ i ∈ block, MemLp (X i) 2 mu)
    (hindep : Set.Pairwise (↑block) fun i j ↦ IndepFun (X i) (X j) mu)
    (hvariance : ∀ i ∈ block, variance (X i) mu ≤ varianceBound) :
    variance (blockAverage block X) mu ≤ varianceBound / block.card := by
  rw [show blockAverage block X =
      fun omega ↦ (block.card : ℝ)⁻¹ * (∑ i ∈ block, X i omega) by
        ext omega
        simp [blockAverage]]
  rw [variance_const_mul]
  have hvarsum : variance (fun omega ↦ ∑ i ∈ block, X i omega) mu =
      ∑ i ∈ block, variance (X i) mu := by
    have hfun : (fun omega ↦ ∑ i ∈ block, X i omega) =
        ∑ i ∈ block, X i := by
      symm
      exact Finset.sum_fn block X
    rw [hfun]
    exact IndepFun.variance_sum hX hindep
  rw [hvarsum]
  have hsum : ∑ i ∈ block, variance (X i) mu ≤
      ∑ _i ∈ block, varianceBound := by
    exact Finset.sum_le_sum fun i hi ↦ hvariance i hi
  have hcardpos : 0 < (block.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hblock
  calc
    ((block.card : ℝ)⁻¹) ^ 2 * ∑ i ∈ block, variance (X i) mu ≤
        ((block.card : ℝ)⁻¹) ^ 2 *
          ∑ _i ∈ block, varianceBound :=
      mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = varianceBound / block.card := by
      rw [Finset.sum_const, nsmul_eq_mul]
      field_simp

/-- Chebyshev with an externally supplied upper bound on the variance. -/
theorem measure_deviation_le_of_variance_le
    (mu : Measure Omega) [IsFiniteMeasure mu] (X : Omega → ℝ)
    (hX : MemLp X 2 mu) (radius varianceBound : ℝ)
    (hradius : 0 < radius) (hvariance : variance X mu ≤ varianceBound) :
    mu {omega | radius ≤ |X omega - mu[X]|} ≤
      ENNReal.ofReal (varianceBound / radius ^ 2) := by
  refine (meas_ge_le_variance_div_sq hX hradius).trans ?_
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_div_iff_of_pos_right (sq_pos_of_pos hradius)).2 hvariance

/-- A variance bound for a single block average.  A block of pairwise
independent variables, each with variance at most `varianceBound`, misses its
common mean by `sqrt (8 * varianceBound / card)` with probability at most
`1/8`. -/
theorem blockAverage_failure_le_one_eighth
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (block : Finset Index) (hblock : block.Nonempty)
    (X : Index → Omega → ℝ) (mean varianceBound radius : ℝ)
    (hX : ∀ i ∈ block, MemLp (X i) 2 mu)
    (hindep : Set.Pairwise (↑block) fun i j ↦ IndepFun (X i) (X j) mu)
    (hmean : ∀ i ∈ block, ∫ omega, X i omega ∂mu = mean)
    (hvariance : ∀ i ∈ block, variance (X i) mu ≤ varianceBound)
    (hradius : 0 < radius)
    (hradius_sq : 8 * varianceBound / block.card ≤ radius ^ 2) :
    mu {omega | radius ≤ |blockAverage block X omega - mean|} ≤
      ENNReal.ofReal (1 / 8 : ℝ) := by
  have hmeanAverage : mu[blockAverage block X] = mean := by
    exact integral_blockAverage mu block hblock X mean
      (fun i hi ↦ (hX i hi).integrable (by norm_num)) hmean
  rw [← hmeanAverage]
  have hvar := variance_blockAverage_le mu block hblock X varianceBound hX hindep hvariance
  refine (measure_deviation_le_of_variance_le mu (blockAverage block X)
    (blockAverage_memLp_two mu block X hX) radius
    (varianceBound / block.card) hradius hvar).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hcardpos : 0 < (block.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hblock
  have hscale : varianceBound / block.card ≤ radius ^ 2 / 8 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).2
    calc
      (varianceBound / (block.card : ℝ)) * 8 =
          8 * varianceBound / (block.card : ℝ) := by ring
      _ ≤ radius ^ 2 := hradius_sq
  have hradius_sq_pos : 0 < radius ^ 2 := sq_pos_of_pos hradius
  calc
    (varianceBound / block.card) / radius ^ 2 ≤
        (radius ^ 2 / 8) / radius ^ 2 :=
      (div_le_div_iff_of_pos_right hradius_sq_pos).2 hscale
    _ = 1 / 8 := by field_simp

end ScalarBlockAverage

end TomographyOracleCore
