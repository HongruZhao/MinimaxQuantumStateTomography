import TomographyOracleCore.GrassmannHaarCoordinates
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.GroupTheory.Perm.Fin

namespace TomographyOracleCore

open MeasureTheory Real Set
open scoped BigOperators

noncomputable section

/-!
# The Jensen step in the Hayden--Leung--Winter Grassmann argument

The source proof compares a random rank-`m` projector with the reduced state
of a random bipartite pure state.  Conditional on the eigenbasis, the reduced
state has random eigenvalues whose individual means are `1 / m`.  Convexity
of the exponential then gives the comparison below.  This file proves that
analytic step without assuming positivity of the coefficient or of the
observables, so it applies directly to the negative Laplace tilt needed for
the lower tail.
-/

/-- Jensen's inequality for the exponential under a probability measure,
with the exact integrability hypotheses needed by the Bochner integral. -/
theorem exp_integral_le_integral_exp
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (f : Omega -> Real)
    (hf : Integrable f mu)
    (hexp : Integrable (fun omega => Real.exp (f omega)) mu) :
    Real.exp (∫ omega, f omega ∂mu) <=
      ∫ omega, Real.exp (f omega) ∂mu := by
  simpa [Function.comp_def] using
    convexOn_exp.map_integral_le continuousOn_exp isClosed_univ
      (by simp) hf hexp

/-- The source-faithful eigenvalue Jensen comparison.  If each of `m`
exchangeable weights has mean `1/m`, then the exponential moment of the
random weighted combination dominates the exponential evaluated at the
uniform combination.  No sign restriction on `t` or `a` is needed. -/
theorem hLW_eigenvalue_jensen
    {Omega : Type*} [MeasurableSpace Omega]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    {m : Nat} (hm : 1 <= m)
    (lambda : Omega -> Fin m -> Real) (a : Fin m -> Real) (t : Real)
    (hlambda : forall i, Integrable (fun omega => lambda omega i) mu)
    (hmean : forall i,
      (∫ omega, lambda omega i ∂mu) = 1 / (m : Real))
    (hexp : Integrable
      (fun omega => Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i * a i)) mu) :
    Real.exp (t * ∑ i, a i) <=
      ∫ omega, Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i * a i) ∂mu := by
  let f : Omega -> Real := fun omega =>
    (t * (m : Real)) * ∑ i, lambda omega i * a i
  have hf : Integrable f mu := by
    dsimp [f]
    exact (integrable_finsetSum Finset.univ (fun i _ =>
      (hlambda i).mul_const (a i))).const_mul _
  have hint : (∫ omega, f omega ∂mu) = t * ∑ i, a i := by
    dsimp [f]
    rw [integral_const_mul]
    rw [integral_finsetSum Finset.univ (fun i _ =>
      (hlambda i).mul_const (a i))]
    simp_rw [integral_mul_const, hmean]
    rw [<- Finset.mul_sum]
    have hm0 : (m : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hm)
    field_simp [hm0]
  rw [<- hint]
  exact exp_integral_le_integral_exp mu f hf (by simpa [f] using hexp)

/-- A distribution-free finite version of the HLW eigenvalue step.  Averaging
only over the cyclic permutations of any vector of weights with total mass
one already has coordinate mean `1/m`.  This form avoids any independence or
measurable-eigenvalue assertion. -/
theorem hLW_cyclic_eigenvalue_jensen
    {m : Nat} (hm : 1 <= m)
    (lambda a : Fin m -> Real) (t : Real)
    (hlambdaSum : (∑ i, lambda i) = 1) :
    Real.exp (t * ∑ i, a i) <=
      (1 / (m : Real)) * ∑ r : Fin m, Real.exp
        ((t * (m : Real)) * ∑ i, lambda i *
          a (((finRotate m) ^ (r : Nat)) i)) := by
  rcases (show m = 1 ∨ 2 <= m by omega) with rfl | hm2
  · have hlambda0 : lambda 0 = 1 := by simpa using hlambdaSum
    simpa [hlambda0]
  · have hcycle : (finRotate m).IsCycleOn
        (Finset.univ : Finset (Fin m)) := by
      rw [← support_finRotate_of_le hm2]
      have hc := (isCycle_finRotate_of_le hm2).isCycleOn
      convert hc using 1
      ext i
      simp only [Finset.mem_coe, Equiv.Perm.mem_support, Set.mem_setOf_eq]
    have hproduct := Finset.sum_mul_sum_eq_sum_perm hcycle lambda a
    have hdouble :
        (∑ r : Fin m, ∑ i : Fin m, lambda i *
          a (((finRotate m) ^ (r : Nat)) i)) = ∑ i, a i := by
      rw [Fin.sum_univ_eq_sum_range (fun r : Nat =>
        ∑ i : Fin m, lambda i * a (((finRotate m) ^ r) i))]
      simpa [hlambdaSum] using hproduct.symm
    have hm0 : (m : Real) ≠ 0 := by positivity
    have hweight :
        (∑ _r : Fin m, (1 / (m : Real))) = 1 := by
      simp [hm0]
    have havg :
        (∑ r : Fin m, (1 / (m : Real)) *
          ((t * (m : Real)) * ∑ i, lambda i *
            a (((finRotate m) ^ (r : Nat)) i))) =
          t * ∑ i, a i := by
      calc
        (∑ r : Fin m, (1 / (m : Real)) *
            ((t * (m : Real)) * ∑ i, lambda i *
              a (((finRotate m) ^ (r : Nat)) i))) =
            ((1 / (m : Real)) * (t * (m : Real))) *
              ∑ r : Fin m, ∑ i : Fin m, lambda i *
                a (((finRotate m) ^ (r : Nat)) i) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = ((1 / (m : Real)) * (t * (m : Real))) * ∑ i, a i := by
          rw [hdouble]
        _ = t * ∑ i, a i := by
          field_simp [hm0]
    have hj := convexOn_exp.map_sum_le
      (t := Finset.univ) (w := fun _r : Fin m => (1 / (m : Real)))
      (p := fun r => (t * (m : Real)) * ∑ i, lambda i *
        a (((finRotate m) ^ (r : Nat)) i))
      (by intro i hi; positivity) (by simpa using hweight) (by simp)
    simp only [smul_eq_mul] at hj
    rw [havg, ← Finset.mul_sum] at hj
    exact hj

/-- The integrated eigenbasis form of the Hayden--Leung--Winter comparison.
The eigenvalue law is independent of the eigenbasis law, and its coordinates
have uniform mean.  Integrating the pointwise Jensen inequality over the
eigenbasis gives the Grassmann-to-pure-state exponential-moment comparison.
The remaining probabilistic work is therefore only to identify the two laws
with Haar projectors and Haar bipartite pure states. -/
theorem hLW_eigenbasis_eigenvalue_jensen
    {Omega BasisSample : Type*}
    [MeasurableSpace Omega] [MeasurableSpace BasisSample]
    (muLambda : Measure Omega) [IsProbabilityMeasure muLambda]
    (muBasis : Measure BasisSample) [IsProbabilityMeasure muBasis]
    {m : Nat} (hm : 1 <= m)
    (lambda : Omega -> Fin m -> Real)
    (a : BasisSample -> Fin m -> Real) (t : Real)
    (hlambda : forall i, Integrable (fun omega => lambda omega i) muLambda)
    (hmean : forall i,
      (∫ omega, lambda omega i ∂muLambda) = 1 / (m : Real))
    (hinner : forall e, Integrable
      (fun omega => Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i * a e i)) muLambda)
    (hleft : Integrable
      (fun e => Real.exp (t * ∑ i, a e i)) muBasis)
    (hright : Integrable
      (fun e => ∫ omega, Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i * a e i)
        ∂muLambda) muBasis) :
    (∫ e, Real.exp (t * ∑ i, a e i) ∂muBasis) <=
      ∫ e, (∫ omega, Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i * a e i)
        ∂muLambda) ∂muBasis := by
  exact integral_mono hleft hright fun e =>
    hLW_eigenvalue_jensen muLambda hm lambda (a e) t
      hlambda hmean (hinner e)

/-- The HLW Jensen comparison instantiated with the actual Haar-unitary
Grassmann eigenbasis.  Its left side is exactly the canonical projector
overlap.  Thus the only remaining source-specific bridge is to identify the
right-hand mixture with the complementary-coordinate mass of a Haar random
bipartite pure state. -/
theorem canonicalUnitaryLaplace_le_hLW_mixture
    {Omega : Type*} [MeasurableSpace Omega]
    (muLambda : Measure Omega) [IsProbabilityMeasure muLambda]
    {k m : Nat} (hm : 1 <= m) (hmk : m <= k)
    (lambda : Omega -> Fin m -> Real) (t : Real)
    (hlambda : forall i, Integrable (fun omega => lambda omega i) muLambda)
    (hmean : forall i,
      (∫ omega, lambda omega i ∂muLambda) = 1 / (m : Real))
    (hinner : forall U, Integrable
      (fun omega => Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i *
          canonicalUnitaryComplementColumnMass k m hmk U i)) muLambda)
    (hright : Integrable
      (fun U => ∫ omega, Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i *
          canonicalUnitaryComplementColumnMass k m hmk U i)
        ∂muLambda) (unitaryHaarProbability k)) :
    (∫ U, Real.exp (t * canonicalUnitaryComplementOverlap k m hmk U)
      ∂unitaryHaarProbability k) <=
      ∫ U, (∫ omega, Real.exp
        ((t * (m : Real)) * ∑ i, lambda omega i *
          canonicalUnitaryComplementColumnMass k m hmk U i)
        ∂muLambda) ∂unitaryHaarProbability k := by
  have hleft : Integrable
      (fun U => Real.exp
        (t * ∑ i, canonicalUnitaryComplementColumnMass k m hmk U i))
      (unitaryHaarProbability k) := by
    simpa only [canonicalUnitaryComplementOverlap_eq_sum_columnMass] using
      integrable_exp_mul_canonicalUnitaryComplementOverlap k m hmk t
  have h := hLW_eigenbasis_eigenvalue_jensen muLambda
    (unitaryHaarProbability k) hm lambda
    (fun U i => canonicalUnitaryComplementColumnMass k m hmk U i) t
    hlambda hmean hinner hleft hright
  simpa only [canonicalUnitaryComplementOverlap_eq_sum_columnMass] using h

end

end TomographyOracleCore
