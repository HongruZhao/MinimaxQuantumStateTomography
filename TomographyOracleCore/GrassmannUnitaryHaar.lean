import TomographyOracleCore.GrassmannHaarOverlap
import TomographyOracleCore.UnitaryHaarOrientation
import TomographyOracleCore.HaarOverlapChernoff

namespace TomographyOracleCore

open MatrixReduction MeasureTheory Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-!
# Normalized unitary Haar realization of the Grassmann sampler

This module reduces every center in the random-projector orbit to one
canonical scalar overlap tail.  The tail itself is deliberately a premise;
all compact-Haar normalization and invariance steps are proved here.
-/

/-- Left invariance of the normalized unitary Haar law, in preimage form. -/
theorem unitaryHaarProbability_preimage_mul (k : ℕ)
    (V : unitary (Matrix (Fin k) (Fin k) ℂ))
    (A : Set (unitary (Matrix (Fin k) (Fin k) ℂ))) :
    unitaryHaarProbability k ((fun U => V * U) ⁻¹' A) =
      unitaryHaarProbability k A := by
  exact measure_preimage_mul (unitaryHaarProbability k) V A

/-- The scalar overlap observable at the canonical center.  Naming it keeps
the analytic Laplace-transform statement independent of the bundled
projector implementation. -/
def canonicalUnitaryComplementOverlap (k m : ℕ) (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) : ℝ :=
  projectorComplementOverlap (canonicalRankMProjector k m hmk)
    (rankMProjectorSampler k m hmk U)

/-- The canonical overlap is a continuous function of the unitary. -/
theorem continuous_canonicalUnitaryComplementOverlap
    (k m : ℕ) (hmk : m ≤ k) :
    Continuous (canonicalUnitaryComplementOverlap k m hmk) := by
  change Continuous (fun U =>
    (((1 - (canonicalRankMProjector k m hmk).matrix) *
      unitaryConjugateMatrix U
        (canonicalRankMProjector k m hmk).matrix).trace.re))
  have hconj : Continuous (fun U => unitaryConjugateMatrix U
      (canonicalRankMProjector k m hmk).matrix) :=
    continuous_unitaryConjugateMatrix_fixed _
  fun_prop

/-- Every exponential tilt of the canonical overlap is Haar-integrable.
This removes all regularity side conditions from the later Chernoff step. -/
theorem integrable_exp_mul_canonicalUnitaryComplementOverlap
    (k m : ℕ) (hmk : m ≤ k) (s : ℝ) :
    Integrable
      (fun U => Real.exp
        (s * canonicalUnitaryComplementOverlap k m hmk U))
      (unitaryHaarProbability k) := by
  have hcont : Continuous
      (fun U => Real.exp
        (s * canonicalUnitaryComplementOverlap k m hmk U)) :=
    Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_canonicalUnitaryComplementOverlap k m hmk))
  simpa [IntegrableOn] using
    hcont.continuousOn.integrableOn_compact (μ := unitaryHaarProbability k)
      isCompact_univ

/-- The exact one-point Laplace estimate left by the source proof at
`t = 1/4`.  Hayden--Leung--Winter obtain this from Gaussianization of a
rank-`m` random subspace.  Everything after this scalar integral inequality
is proved below. -/
def CanonicalUnitaryQuarterLaplaceBound
    (k m : ℕ) (hmk : m ≤ k) : Prop :=
  (∫ U, Real.exp
      ((-((k : ℝ) / 3)) * canonicalUnitaryComplementOverlap k m hmk U)
      ∂unitaryHaarProbability k) ≤
    Real.exp
      ((((k - m : ℕ) : ℝ) * (m : ℝ)) * Real.log (3 / 4 : ℝ))

/-- The one remaining probabilistic statement, specialized exactly to the
canonical rank-`m` projector and the `t = 1/4` Lowe--Nayak lower tail. -/
def CanonicalUnitaryLownayakQuarterTail (k m : ℕ) (hmk : m ≤ k) : Prop :=
  (unitaryHaarProbability k).real
      {U | projectorComplementOverlap (canonicalRankMProjector k m hmk)
          (rankMProjectorSampler k m hmk U) <
        lownayakQuarterComplementThreshold k m} ≤
    lownayakQuarterComplementTailBound k m

/-- The specialized Laplace estimate implies the complete Lowe--Nayak
quarter lower tail.  This theorem discharges integrability, Chernoff,
threshold cancellation, and the logarithmic constant `1/32`; only the
single scalar integral inequality remains. -/
theorem canonicalUnitaryLownayakQuarterTail_of_laplace
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hlaplace : CanonicalUnitaryQuarterLaplaceBound k m (by omega)) :
    CanonicalUnitaryLownayakQuarterTail k m (by omega) := by
  let hmk : m ≤ k := by omega
  let X : unitary (Matrix (Fin k) (Fin k) ℂ) → ℝ :=
    canonicalUnitaryComplementOverlap k m hmk
  let a : ℝ := lownayakQuarterComplementThreshold k m
  let s : ℝ := (k : ℝ) / 3
  let B : ℝ :=
    (((k - m : ℕ) : ℝ) * (m : ℝ)) * Real.log (3 / 4 : ℝ)
  have hkpos_nat : 0 < k := by omega
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
  have hs : 0 ≤ s := by
    dsimp [s]
    positivity
  have hint : Integrable (fun U => Real.exp ((-s) * X U))
      (unitaryHaarProbability k) := by
    dsimp [s, X]
    exact integrable_exp_mul_canonicalUnitaryComplementOverlap
      k m hmk (-((k : ℝ) / 3))
  have hlaplace' :
      (∫ U, Real.exp ((-s) * X U) ∂unitaryHaarProbability k) ≤
        Real.exp B := by
    simpa [CanonicalUnitaryQuarterLaplaceBound, s, X, B] using hlaplace
  have hchernoff := measure_lowerTail_le_exp_of_laplace_bound
    (unitaryHaarProbability k) X a s B hs hint hlaplace'
  have hsub : ((k - m : ℕ) : ℝ) = (k : ℝ) - (m : ℝ) := by
    rw [Nat.cast_sub hmk]
  have hlog :
      (1 / 4 : ℝ) + Real.log (3 / 4 : ℝ) ≤ -(1 / 32 : ℝ) := by
    have h := add_log_one_sub_le_neg_half_sq
      (t := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hprod : 0 ≤ ((k - m : ℕ) : ℝ) * (m : ℝ) := by positivity
  have hlogmul := mul_le_mul_of_nonneg_left hlog hprod
  have hexponent :
      s * a + B ≤ -(((k - m : ℕ) : ℝ) * (m : ℝ) / 32) := by
    have hcancel :
        s * a + B =
          (((k - m : ℕ) : ℝ) * (m : ℝ)) *
            ((1 / 4 : ℝ) + Real.log (3 / 4 : ℝ)) := by
      dsimp [s, a, B]
      rw [lownayakQuarterComplementThreshold, hsub]
      field_simp [ne_of_gt hkpos]
    rw [hcancel]
    nlinarith
  unfold CanonicalUnitaryLownayakQuarterTail
  change (unitaryHaarProbability k).real {U | X U < a} ≤
    lownayakQuarterComplementTailBound k m
  calc
    (unitaryHaarProbability k).real {U | X U < a} ≤
        (unitaryHaarProbability k).real {U | X U ≤ a} :=
      measureReal_mono (by
        intro U hU
        change X U < a at hU
        change X U ≤ a
        exact hU.le)
    _ ≤ Real.exp (s * a + B) := hchernoff
    _ ≤ lownayakQuarterComplementTailBound k m := by
      rw [lownayakQuarterComplementTailBound]
      exact Real.exp_le_exp.mpr hexponent

/-- Haar left invariance and simultaneous-conjugation invariance transfer
the canonical scalar tail to every center in the same projector orbit. -/
theorem unitaryHaar_lownayakComplementTail_of_canonical
    {k m : ℕ} (hmk : m ≤ k)
    (hcanonical : CanonicalUnitaryLownayakQuarterTail k m hmk) :
    ∀ U₀ : unitary (Matrix (Fin k) (Fin k) ℂ),
      (unitaryHaarProbability k).real
          {U | projectorComplementOverlap
              (rankMProjectorSampler k m hmk U₀)
              (rankMProjectorSampler k m hmk U) <
            lownayakQuarterComplementThreshold k m} ≤
        lownayakQuarterComplementTailBound k m := by
  intro U₀
  let centerEvent : Set (unitary (Matrix (Fin k) (Fin k) ℂ)) :=
    {U | projectorComplementOverlap
        (rankMProjectorSampler k m hmk U₀)
        (rankMProjectorSampler k m hmk U) <
      lownayakQuarterComplementThreshold k m}
  let canonicalEvent : Set (unitary (Matrix (Fin k) (Fin k) ℂ)) :=
    {U | projectorComplementOverlap (canonicalRankMProjector k m hmk)
        (rankMProjectorSampler k m hmk U) <
      lownayakQuarterComplementThreshold k m}
  have hpre : (fun U => U₀ * U) ⁻¹' centerEvent = canonicalEvent := by
    ext U
    change projectorComplementOverlap
        (rankMProjectorSampler k m hmk U₀)
        (rankMProjectorSampler k m hmk (U₀ * U)) <
          lownayakQuarterComplementThreshold k m ↔
      projectorComplementOverlap (canonicalRankMProjector k m hmk)
        (rankMProjectorSampler k m hmk U) <
          lownayakQuarterComplementThreshold k m
    rw [rankMProjectorSampler_left_equivariant]
    have hcenter : rankMProjectorSampler k m hmk U₀ =
        unitaryConjugateRankMProjector U₀
          (canonicalRankMProjector k m hmk) := by
      rfl
    rw [hcenter, projectorComplementOverlap_unitaryConjugate]
  have hmeasure := unitaryHaarProbability_preimage_mul k U₀ centerEvent
  rw [hpre] at hmeasure
  have hreal := congrArg ENNReal.toReal hmeasure
  change ((unitaryHaarProbability k) centerEvent).toReal ≤
      lownayakQuarterComplementTailBound k m
  change ((unitaryHaarProbability k) canonicalEvent).toReal ≤
      lownayakQuarterComplementTailBound k m at hcanonical
  rw [← hreal]
  exact hcanonical

/-- The exact Grassmann packing now follows from only the canonical
unitary-Haar overlap tail. -/
theorem exists_complexGrassmannPackingWitness_card_eq_of_canonicalUnitaryTail
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hcanonical : CanonicalUnitaryLownayakQuarterTail k m (by omega)) :
    ∃ V : ComplexGrassmannPackingWitness k m,
      V.card = grassmannPackingCard k m := by
  let hmk : m ≤ k := by omega
  exact exists_complexGrassmannPackingWitness_card_eq_of_lownayakComplementTail
    (unitaryHaarProbability k) (rankMProjectorSampler k m hmk) hm hkm
      (unitaryHaar_lownayakComplementTail_of_canonical hmk hcanonical)

/-- The complete Grassmann packing endpoint, with the source-specific
Laplace transform as its sole probabilistic input. -/
theorem exists_complexGrassmannPackingWitness_card_eq_of_canonicalUnitaryLaplace
    {k m : ℕ} (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (hlaplace : CanonicalUnitaryQuarterLaplaceBound k m (by omega)) :
    ∃ V : ComplexGrassmannPackingWitness k m,
      V.card = grassmannPackingCard k m := by
  exact exists_complexGrassmannPackingWitness_card_eq_of_canonicalUnitaryTail
    hm hkm (canonicalUnitaryLownayakQuarterTail_of_laplace hm hkm hlaplace)

end

end TomographyOracleCore
