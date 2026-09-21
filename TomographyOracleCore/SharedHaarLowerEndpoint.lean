import TomographyOracleCore.SharedHaarFanoAssembly
import TomographyOracleCore.PhysicalLowerAssembly

namespace TomographyOracleCore

open MatrixReduction
open scoped ENNReal

noncomputable section

namespace PhysicalRisk

/-!
# Optimized physical lower endpoint from procedurewise shared-Haar families

`SharedHaarFanoAssembly` proves the unrestricted-risk lower bound for one
fixed hard-family radius.  This module performs the remaining effective-rank
optimization.  Its sole premise is the literal procedurewise shared-Haar
family at every admissible rank; no packing, one-copy information estimate,
or minimax conclusion is hidden in the assembly.
-/

/-- Per-effective-rank procedurewise shared-Haar families imply the exact
spectral-decay lower rate and manuscript constant.  The orientation space is
fixed by the ambient dimension, while the family, reference, orientation law,
and one-shot budgets may depend on the design, estimator, and effective rank.
-/
theorem explicitSpectralDecayRateENNReal_le_unrestrictedRisk_of_procedurewiseSharedHaar
    {Orientation : Type*} [MeasurableSpace Orientation]
    [StandardBorelSpace Orientation]
    (D T : ℕ) (L alpha : ℝ)
    (hD : 514 ≤ D) (hT : 1 ≤ T) (hL : 1 ≤ L) (halpha : 1 < alpha)
    (hfamily : ∀ m : ℕ,
      1 ≤ m → m ≤ lowerEffectiveRankCap D →
      ProcedurewiseSharedHaarFanoFamily Orientation D T alpha L
        (hardFamilyMass m L
          (Real.sqrt
            ((lowerAmbientDimension D : ℝ) / (T : ℝ))) alpha / 4)) :
    ENNReal.ofReal
        (explicitDecayLowerConstant alpha *
          spectralDecayMinimaxRate D (T : ℝ) L alpha) ≤
      unrestrictedRisk D T alpha L := by
  have hTreal : 0 < (T : ℝ) := by
    exact_mod_cast (show 0 < T by omega)
  apply explicitSpectralDecayRateENNReal_le_of_perRankFanoMass
    (unrestrictedRisk D T alpha L) D (T : ℝ) L alpha
      hD hTreal hL halpha
  intro m hm1 hmcap
  let eta : ℝ :=
    Real.sqrt ((lowerAmbientDimension D : ℝ) / (T : ℝ))
  have heta : 0 ≤ eta := Real.sqrt_nonneg _
  have hmass : 0 ≤ hardFamilyMass m L eta alpha :=
    hardFamilyMass_nonnegative m L eta alpha
      (le_trans zero_le_one hL) heta
  have hradius : 0 ≤ hardFamilyMass m L eta alpha / 4 :=
    div_nonneg hmass (by norm_num)
  have hfano :=
    ofReal_eleven_mul_radius_div_sixteen_le_unrestrictedRisk_of_procedurewiseSharedHaar
      hradius (hfamily m hm1 hmcap)
  simpa only [eta,
    show 11 *
        (hardFamilyMass m L
          (Real.sqrt
            ((lowerAmbientDimension D : ℝ) / (T : ℝ))) alpha / 4) /
          16 =
        11 * hardFamilyMass m L
          (Real.sqrt
            ((lowerAmbientDimension D : ℝ) / (T : ℝ))) alpha /
          64 by ring] using hfano

end PhysicalRisk

end

end TomographyOracleCore
