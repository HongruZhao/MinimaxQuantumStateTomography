import TomographyOracleCore.RelativeDesignApproximationCalculus
import TomographyOracleCore.ChoKimGluingProductArithmetic

namespace TomographyOracleCore

open scoped CStarAlgebra

noncomputable section

/-!
# Pairwise actual-Haar gluing through approximate-Haar references

The directions here are deliberate: the two local actual Haar maps use
B.21 (`Haar -> Phi_a`), B.27 glues the two references, and the union
reference uses B.22 (`Phi_a -> Haar`).
-/

/-- Algebraic assembly of one actual-Haar gluing step at order three.

The two local B.21 errors have already been weakened to
`d = (9/(4q))/(1-9/(4q))`; the B.27 error is `exp(9/(2q))-1`; and the final
B.22 error has already been weakened to `9/(2q)`.  The audited scalar product
bound then gives exactly `choKimFThree q`. -/
theorem relativeCPApproximation_pairwiseActualHaar_of_references
    {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A]
    (q : ℝ) (hq : 18 ≤ q)
    (HAB RAB HBC RBC RABC HABC : A →CP A)
    (hAB : RelativeCPApproximation
      ((9 / (4 * q)) / (1 - 9 / (4 * q)))
      HAB.toLinearMap RAB.toLinearMap)
    (hBC : RelativeCPApproximation
      ((9 / (4 * q)) / (1 - 9 / (4 * q)))
      HBC.toLinearMap RBC.toLinearMap)
    (hreference : RelativeCPApproximation
      (Real.exp (9 / (2 * q)) - 1)
      (CompletelyPositiveMap.comp RAB RBC).toLinearMap
      RABC.toLinearMap)
    (hglobal : RelativeCPApproximation (9 / (2 * q))
      RABC.toLinearMap HABC.toLinearMap) :
    RelativeCPApproximation (choKimFThree q)
      (CompletelyPositiveMap.comp HAB HBC).toLinearMap
      HABC.toLinearMap := by
  let d : ℝ := (9 / (4 * q)) / (1 - 9 / (4 * q))
  let b : ℝ := 9 / (2 * q)
  let delta : ℝ := Real.exp b - 1
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hden : 0 < 1 - 9 / (4 * q) := by
    rw [sub_pos]
    apply (div_lt_one (by positivity : 0 < 4 * q)).2
    nlinarith
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hd1 : d ≤ 1 := by
    dsimp only [d]
    rw [div_le_one hden]
    field_simp
    nlinarith
  have hb0 : 0 ≤ b := by dsimp only [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp only [b]
    rw [div_le_one (by positivity : 0 < 2 * q)]
    nlinarith
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    exact sub_nonneg.mpr (Real.one_le_exp hb0)
  have hthroughReference :=
    relativeCPApproximation_twoUnitary_of_reference_gluing
      HAB RAB HBC RBC RABC d d delta
      hd0 hd1 hd0 hd1 hdelta0
      (by simpa [d] using hAB)
      (by simpa [d] using hBC)
      (by simpa [delta, b] using hreference)
  let epsilonReference : ℝ :=
    (1 + d) * (1 + d) * (1 + delta) - 1
  have hepsilonReference0 : 0 ≤ epsilonReference := by
    dsimp only [epsilonReference]
    have hfac : 1 ≤
        (1 + d) * (1 + d) * (1 + delta) := by
      have hdFac : 1 ≤ 1 + d := by linarith
      have hdeltaFac : 1 ≤ 1 + delta := by linarith
      nlinarith [mul_nonneg hd0 hd0,
        mul_nonneg (by linarith : 0 ≤ 1 + d) hdelta0]
    linarith
  have htotal := relativeCPApproximation_trans
    (CompletelyPositiveMap.comp HAB HBC) RABC HABC
    epsilonReference b hepsilonReference0 hb0
    (by simpa [epsilonReference] using hthroughReference)
    (by simpa [b] using hglobal)
  have herrorIdentity :
      (1 + epsilonReference) * (1 + b) - 1 =
        (1 + d) ^ 2 * Real.exp b * (1 + b) - 1 := by
    dsimp only [epsilonReference, delta]
    ring
  rw [herrorIdentity] at htotal
  apply htotal.mono_error
  have hproduct := choKimGluingProduct_le_one_add_fThree hq
  dsimp only [d, b] at htotal ⊢
  linarith

end

end TomographyOracleCore
