import TomographyOracleCore.GrassmannGreedy
import TomographyOracleCore.UnitaryConjugation

namespace TomographyOracleCore

open MatrixReduction

/-!
# Spectral-decay hard families from Grassmann projector packings

This module composes a finite projector packing with one common unitary
orientation of the hard density states.  The resulting finite family carries
all three properties needed downstream: exact spectral-decay membership,
pairwise Hermitian trace-distance separation, and logarithmic cardinality.

No metric-exclusion or packing hypothesis is asserted here.  The final
theorems retain `FlammiaQuarterMetricExclusionInput` as an explicit premise.
-/

/-- A finite family of actual density operators obtained from a rank-`m`
Grassmann packing, bundled with the manuscript class, size, and separation
properties. -/
structure GrassmannHardFamilyWitness
    (k m : ℕ) (alpha L b : ℝ) where
  card : ℕ
  state : Fin card → DensityOperator (Fin (k + 2))
  state_mem : ∀ a, state a ∈ spectralDecayClass (k + 2) alpha L
  log_cardinality_lower :
    (25 / 4608 : ℝ) * (m : ℝ) * (k : ℝ) ≤ Real.log (card : ℝ)
  pairwise_traceDistance : ∀ a c, a ≠ c →
    b / 2 ≤
      hermitianTraceNorm
        ((state a).matrix - (state c).matrix)
        ((state a).sub_isHermitian (state c))

/-- Turn a supplied projector packing into its commonly oriented hard density
family.  Every proof field is discharged by the projector-state and unitary
invariance modules. -/
noncomputable def grassmannHardFamilyOfPacking
    {k m : ℕ} (W : ComplexGrassmannPackingWitness k m)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    GrassmannHardFamilyWitness k m alpha L b where
  card := W.card
  state := fun a ↦
    orientedHardProjectorDensityOperator U (W.projector a) b hm hb0 hbquarter
  state_mem := fun a ↦
    orientedHardProjectorDensityOperator_mem_spectralDecayClass U
      (W.projector a) alpha L b hm halpha hL hb0 hbquarter hbscaled
  log_cardinality_lower := W.log_cardinality_lower
  pairwise_traceDistance := fun a c hac ↦
    orientedHardProjectorDensityOperator_traceDistance_ge_half_mass U
      (W.projector a) (W.projector c) b hm hb0 hbquarter
      (W.pairwise_separated a c hac)

@[simp] theorem grassmannHardFamilyOfPacking_card
    {k m : ℕ} (W : ComplexGrassmannPackingWitness k m)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    (grassmannHardFamilyOfPacking W U alpha L b hm halpha hL hb0 hbquarter
      hbscaled).card = W.card := rfl

@[simp] theorem grassmannHardFamilyOfPacking_state
    {k m : ℕ} (W : ComplexGrassmannPackingWitness k m)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha))
    (a : Fin W.card) :
    (grassmannHardFamilyOfPacking W U alpha L b hm halpha hL hb0 hbquarter
      hbscaled).state a =
      orientedHardProjectorDensityOperator U (W.projector a) b hm hb0
        hbquarter := rfl

/-- At fixed `(k,m)`, the sole one-step exclusion premise constructs an
actual hard density family of exactly the ceiling cardinality. -/
theorem exists_grassmannHardFamilyWitness_card_eq_of_oneStep
    {k m : ℕ} (hstep : FlammiaQuarterMetricExclusionAt k m)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    ∃ F : GrassmannHardFamilyWitness k m alpha L b,
      F.card = grassmannPackingCard k m := by
  obtain ⟨W, hWcard⟩ :=
    exists_complexGrassmannPackingWitness_card_eq_of_oneStep hm hstep
  exact ⟨grassmannHardFamilyOfPacking W U alpha L b hm halpha hL hb0
    hbquarter hbscaled, by simpa using hWcard⟩

/-- Dimension-uniform metric exclusion gives the exact-card hard family.
The quantifier order leaves the common orientation explicit, so it may later
be selected after a fixed design and estimator as required by the minimax
argument. -/
theorem exists_grassmannHardFamilyWitness_card_eq_of_metricExclusion
    (hmetric : FlammiaQuarterMetricExclusionInput)
    (k m : ℕ) (_hk : 3 ≤ k) (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    ∃ F : GrassmannHardFamilyWitness k m alpha L b,
      F.card = grassmannPackingCard k m := by
  exact exists_grassmannHardFamilyWitness_card_eq_of_oneStep
    (hmetric k m hm hkm) U alpha L b hm halpha hL hb0 hbquarter hbscaled

/-- Nonempty form of the complete hard-family construction, retaining the
metric-exclusion input as its only geometric premise. -/
theorem exists_grassmannHardFamilyWitness_of_metricExclusion
    (hmetric : FlammiaQuarterMetricExclusionInput)
    (k m : ℕ) (hk : 3 ≤ k) (hm : 1 ≤ m) (hkm : 3 * m ≤ k)
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (alpha L b : ℝ)
    (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    Nonempty (GrassmannHardFamilyWitness k m alpha L b) := by
  obtain ⟨F, hFcard⟩ :=
    exists_grassmannHardFamilyWitness_card_eq_of_metricExclusion hmetric
      k m hk hm hkm U alpha L b halpha hL hb0 hbquarter hbscaled
  exact ⟨F⟩

end TomographyOracleCore
