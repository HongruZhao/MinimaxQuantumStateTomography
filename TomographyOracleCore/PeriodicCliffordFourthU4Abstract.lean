import TomographyOracleCore.PeriodicCliffordFourthAssembly
import TomographyOracleCore.PeriodicCliffordFourthConstant

namespace TomographyOracleCore

/-!
# Abstract normalized U4 endpoint

This is the narrow endpoint obtained after the concrete Clifford expansion
has supplied a 30-sector nonnegative Gram matrix, its constant row sum, and
the boundary coefficient.  All subsequent cycle, scalar, accumulation, and
constant-normalization steps are discharged here.
-/

noncomputable section

theorem periodicCliffordFourthU4_of_concreteExpansion
    {D m : ℕ} {s moment boundary : ℝ}
    (G : Matrix (Fin 30) (Fin 30) ℝ)
    (hD : 65536 ≤ D)
    (hdim : (D : ℝ) = (s ^ 2) ^ m)
    (hblock : PeriodicCliffordFourthBlockPredicate m s)
    (hG : ∀ i j, 0 ≤ G i j)
    (hrow : ∀ i, ∑ j, G i j = cliffordFourthGramRowSum s)
    (hboundary0 : 0 ≤ boundary) (hboundary1 : boundary ≤ 1)
    (hmoment : moment ≤
      boundary * cliffordFourthWgSignedRowSum (s ^ 2) ^ m *
        cliffordFourthWgAbsoluteRowSum (s ^ 2) ^ m *
          Matrix.trace (G ^ (2 * m))) :
    moment ≤
      34 / ((D : ℝ) * ((D : ℝ) + 1) * ((D : ℝ) + 2) *
        ((D : ℝ) + 3)) := by
  have hraw := periodicCliffordFourthContraction_dimension_form G
    hblock hG hrow hboundary0 hboundary1 hmoment
  rw [← hdim] at hraw
  exact hraw.trans (periodicCliffordFourth_constant34_conversion hD)

end

end TomographyOracleCore
