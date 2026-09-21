import TomographyOracleCore.GrassmannHaarJensen
import Mathlib.LinearAlgebra.Matrix.Permutation

namespace TomographyOracleCore

open MeasureTheory Real Set
open scoped BigOperators

noncomputable section

/-!
# Cyclic symmetrization of a weighted Haar orbit

This file removes the eigenvalue-independence step from the
Hayden--Leung--Winter comparison.  Cyclically permuting an arbitrary
trace-one vector of weights has uniform barycenter.  Haar right invariance
then identifies all cyclic terms after integration.
-/

/-- Extend a permutation of the first `m` coordinates by the identity on
the remaining `k-m` coordinates. -/
def extendInitialFinPermutation {k m : ℕ} (hmk : m ≤ k)
    (sigma : Equiv.Perm (Fin m)) : Equiv.Perm (Fin k) :=
  sigma.extendDomain (Fin.castLEEmb hmk).toEquivRange

@[simp] theorem extendInitialFinPermutation_apply_castLE
    {k m : ℕ} (hmk : m ≤ k) (sigma : Equiv.Perm (Fin m)) (i : Fin m) :
    extendInitialFinPermutation hmk sigma (Fin.castLE hmk i) =
      Fin.castLE hmk (sigma i) := by
  exact Equiv.Perm.extendDomain_apply_image sigma
    (Fin.castLEEmb hmk).toEquivRange i

/-- A permutation matrix, bundled as a unitary matrix. -/
def permutationUnitary {k : ℕ} (sigma : Equiv.Perm (Fin k)) :
    unitary (Matrix (Fin k) (Fin k) ℂ) :=
  ⟨sigma.permMatrix ℂ, by
    constructor <;>
      simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_permMatrix,
        ← Matrix.permMatrix_mul] <;> simp⟩

@[simp] theorem permutationUnitary_coe {k : ℕ}
    (sigma : Equiv.Perm (Fin k)) :
    (permutationUnitary sigma : Matrix (Fin k) (Fin k) ℂ) =
      sigma.permMatrix ℂ := rfl

/-- Right multiplication by the extended permutation unitary permutes the
first `m` columns in the expected contravariant direction. -/
theorem mul_permutationUnitary_apply_castLE
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (sigma : Equiv.Perm (Fin m)) (i : Fin k) (j : Fin m) :
    (U * permutationUnitary (extendInitialFinPermutation hmk sigma)).1
        i (Fin.castLE hmk j) =
      U.1 i (Fin.castLE hmk (sigma.symm j)) := by
  change (U.1 * (extendInitialFinPermutation hmk sigma).permMatrix ℂ)
      i (Fin.castLE hmk j) = _
  change Matrix.vecMul (fun q => U.1 i q)
      ((extendInitialFinPermutation hmk sigma).permMatrix ℂ)
      (Fin.castLE hmk j) = _
  rw [Matrix.vecMul_permMatrix]
  change U.1 i ((sigma.extendDomain
      (Fin.castLEEmb hmk).toEquivRange).symm (Fin.castLE hmk j)) = _
  rw [Equiv.Perm.extendDomain_symm]
  exact congrArg (fun q => U.1 i q)
    (Equiv.Perm.extendDomain_apply_image sigma.symm
      (Fin.castLEEmb hmk).toEquivRange j)

/-- Consequently the complementary mass of a first-block column is
permuted by the same inverse permutation. -/
theorem canonicalUnitaryComplementColumnMass_mul_permutationUnitary
    {k m : ℕ} (hmk : m ≤ k)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (sigma : Equiv.Perm (Fin m)) (j : Fin m) :
    canonicalUnitaryComplementColumnMass k m hmk
        (U * permutationUnitary (extendInitialFinPermutation hmk sigma)) j =
      canonicalUnitaryComplementColumnMass k m hmk U (sigma.symm j) := by
  unfold canonicalUnitaryComplementColumnMass
  apply Finset.sum_congr rfl
  intro i hi
  by_cases him : m ≤ (i : ℕ)
  · simp [him, mul_permutationUnitary_apply_castLE]
  · simp [him]

/-- A weighted complementary-column overlap. -/
def weightedCanonicalUnitaryComplementOverlap
    (k m : ℕ) (hmk : m ≤ k) (lambda : Fin m → ℝ)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ)) : ℝ :=
  ∑ i, lambda i * canonicalUnitaryComplementColumnMass k m hmk U i

theorem continuous_weightedCanonicalUnitaryComplementOverlap
    (k m : ℕ) (hmk : m ≤ k) (lambda : Fin m → ℝ) :
    Continuous (weightedCanonicalUnitaryComplementOverlap k m hmk lambda) := by
  unfold weightedCanonicalUnitaryComplementOverlap
  unfold canonicalUnitaryComplementColumnMass
  refine continuous_finsetSum Finset.univ ?_
  intro j hj
  apply Continuous.const_mul
  refine continuous_finsetSum Finset.univ ?_
  intro i hi
  by_cases him : m ≤ (i : ℕ)
  · simp only [him, if_true]
    exact Complex.continuous_normSq.comp
      ((continuous_apply _).comp
        ((continuous_apply _).comp continuous_subtype_val))
  · simpa [him] using
      (continuous_const : Continuous
        (fun _ : unitary (Matrix (Fin k) (Fin k) ℂ) => (0 : ℝ)))

theorem integrable_exp_mul_weightedCanonicalUnitaryComplementOverlap
    (k m : ℕ) (hmk : m ≤ k) (lambda : Fin m → ℝ) (t : ℝ) :
    Integrable (fun U => Real.exp
      (t * weightedCanonicalUnitaryComplementOverlap k m hmk lambda U))
      (unitaryHaarProbability k) := by
  have hcont : Continuous (fun U => Real.exp
      (t * weightedCanonicalUnitaryComplementOverlap k m hmk lambda U)) :=
    Real.continuous_exp.comp
      (continuous_const.mul
        (continuous_weightedCanonicalUnitaryComplementOverlap
          k m hmk lambda))
  simpa [IntegrableOn] using
    hcont.continuousOn.integrableOn_compact (μ := unitaryHaarProbability k)
      isCompact_univ

/-- Right multiplication by an extended permutation permutes the weighted
column observable. -/
theorem weightedCanonicalUnitaryComplementOverlap_mul_permutationUnitary
    {k m : ℕ} (hmk : m ≤ k) (lambda : Fin m → ℝ)
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (sigma : Equiv.Perm (Fin m)) :
    weightedCanonicalUnitaryComplementOverlap k m hmk lambda
        (U * permutationUnitary (extendInitialFinPermutation hmk sigma)) =
      ∑ i, lambda i *
        canonicalUnitaryComplementColumnMass k m hmk U (sigma.symm i) := by
  unfold weightedCanonicalUnitaryComplementOverlap
  simp_rw [canonicalUnitaryComplementColumnMass_mul_permutationUnitary]

/-- The cyclic average of every trace-one spectrum has uniform barycenter,
and normalized Haar right invariance makes all cyclic relabelings have the
same integral.  Therefore the rank-`m` projector Laplace transform is
dominated by the weighted rank-at-most-`m` orbit for every fixed spectrum.

This is the complete deterministic/Haar part of the induced-state step; it
does not assume independence or measurability of random eigenvalues. -/
theorem canonicalUnitaryLaplace_le_weightedOrbit
    {k m : ℕ} (hm : 1 ≤ m) (hmk : m ≤ k)
    (lambda : Fin m → ℝ) (t : ℝ)
    (hlambdaSum : (∑ i, lambda i) = 1) :
    (∫ U, Real.exp
        (t * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
      ∫ U, Real.exp
        ((t * (m : ℝ)) *
          weightedCanonicalUnitaryComplementOverlap k m hmk lambda U)
        ∂unitaryHaarProbability k := by
  let pi : Fin m → Equiv.Perm (Fin m) := fun r => (finRotate m) ^ (r : ℕ)
  let P : Fin m → unitary (Matrix (Fin k) (Fin k) ℂ) := fun r =>
    permutationUnitary
      (extendInitialFinPermutation hmk (pi r).symm)
  let f : unitary (Matrix (Fin k) (Fin k) ℂ) → ℝ := fun U =>
    Real.exp ((t * (m : ℝ)) *
      weightedCanonicalUnitaryComplementOverlap k m hmk lambda U)
  let g : Fin m → unitary (Matrix (Fin k) (Fin k) ℂ) → ℝ := fun r U =>
    Real.exp ((t * (m : ℝ)) * ∑ i, lambda i *
      canonicalUnitaryComplementColumnMass k m hmk U (pi r i))
  have hf : Integrable f (unitaryHaarProbability k) := by
    simpa only [f] using
      integrable_exp_mul_weightedCanonicalUnitaryComplementOverlap
        k m hmk lambda (t * (m : ℝ))
  have hg_eq (r : Fin m) (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
      g r U = f (U * P r) := by
    simp only [g, f, P, pi]
    rw [weightedCanonicalUnitaryComplementOverlap_mul_permutationUnitary]
    simp
  have hg (r : Fin m) : Integrable (g r) (unitaryHaarProbability k) := by
    rw [show g r = fun U => f (U * P r) by
      funext U
      exact hg_eq r U]
    have hcontMul : Continuous
        (fun U : unitary (Matrix (Fin k) (Fin k) ℂ) => U * P r) := by
      fun_prop
    have hcontF : Continuous f := by
      dsimp only [f]
      exact Real.continuous_exp.comp
        (continuous_const.mul
          (continuous_weightedCanonicalUnitaryComplementOverlap
            k m hmk lambda))
    have hcont := hcontF.comp hcontMul
    change Continuous (fun U => f (U * P r)) at hcont
    simpa [IntegrableOn] using
      hcont.continuousOn.integrableOn_compact
        (μ := unitaryHaarProbability k) isCompact_univ
  have hright : Integrable
      (fun U => (1 / (m : ℝ)) * ∑ r, g r U)
      (unitaryHaarProbability k) := by
    exact (integrable_finsetSum Finset.univ fun r _ => hg r).const_mul _
  have hleft : Integrable
      (fun U => Real.exp
        (t * canonicalUnitaryComplementOverlap k m hmk U))
      (unitaryHaarProbability k) :=
    integrable_exp_mul_canonicalUnitaryComplementOverlap k m hmk t
  have hpoint (U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
      Real.exp (t * canonicalUnitaryComplementOverlap k m hmk U) ≤
        (1 / (m : ℝ)) * ∑ r, g r U := by
    have h := hLW_cyclic_eigenvalue_jensen hm lambda
      (fun i => canonicalUnitaryComplementColumnMass k m hmk U i) t
      hlambdaSum
    simpa only [canonicalUnitaryComplementOverlap_eq_sum_columnMass,
      g, pi] using h
  have hmono := integral_mono hleft hright hpoint
  have hgintegral (r : Fin m) :
      (∫ U, g r U ∂unitaryHaarProbability k) =
        ∫ U, f U ∂unitaryHaarProbability k := by
    have hinv := integral_comp_unitaryHaarProbability_mul_right
      k (P r) f hf.aestronglyMeasurable
    simpa only [hg_eq] using hinv
  calc
    (∫ U, Real.exp
        (t * canonicalUnitaryComplementOverlap k m hmk U)
        ∂unitaryHaarProbability k) ≤
        ∫ U, (1 / (m : ℝ)) * ∑ r, g r U
          ∂unitaryHaarProbability k := hmono
    _ = (1 / (m : ℝ)) *
        ∑ r, ∫ U, g r U ∂unitaryHaarProbability k := by
      rw [integral_const_mul]
      rw [integral_finsetSum Finset.univ (fun r _ => hg r)]
    _ = (1 / (m : ℝ)) *
        ∑ _r : Fin m, ∫ U, f U ∂unitaryHaarProbability k := by
      congr 1
      apply Finset.sum_congr rfl
      intro r hr
      exact hgintegral r
    _ = ∫ U, f U ∂unitaryHaarProbability k := by
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      simp [hm0]
    _ = ∫ U, Real.exp
        ((t * (m : ℝ)) *
          weightedCanonicalUnitaryComplementOverlap k m hmk lambda U)
        ∂unitaryHaarProbability k := rfl

end

end TomographyOracleCore
