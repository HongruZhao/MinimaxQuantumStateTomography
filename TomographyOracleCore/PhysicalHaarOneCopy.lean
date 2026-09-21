import TomographyOracleCore.PhysicalReferencePearson
import TomographyOracleCore.ProjectiveHaarHardRatio
import TomographyOracleCore.UnitaryHaarOrientation

namespace TomographyOracleCore

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace PhysicalPOVM.DominatedPOVM

variable {D : ℕ} {Outcome : Type*} [MeasurableSpace Outcome]
  [StandardBorelSpace Outcome]

/-!
# Measure-theoretic normalization for arbitrary dominated POVMs

The physical POVM representation uses an effect density of trace one almost
everywhere.  Consequently its scalar dominating measure has total mass
exactly the Hilbert-space dimension.  This is the cancellation needed after
the pointwise Haar rank-one calculation: a `1 / D` directional moment is
integrated against base mass `D`.
-/

/-- The trace-dominating scalar measure of a normalized `D`-dimensional POVM
has real total mass exactly `D`. -/
theorem base_real_univ_eq_dimension
    (M : PhysicalPOVM.DominatedPOVM D Outcome) :
    M.base.real univ = (D : ℝ) := by
  have hdiag (i : Fin D) :
      ∫ z, M.effect z i i ∂M.base = 1 := by
    simpa using M.integral_effect_eq_one i i
  have htrace :
      ∫ z, Matrix.trace (M.effect z) ∂M.base = (D : ℂ) := by
    unfold Matrix.trace
    calc
      (∫ z, ∑ i : Fin D, M.effect z i i ∂M.base) =
          ∑ i : Fin D, ∫ z, M.effect z i i ∂M.base := by
        exact integral_finsetSum Finset.univ
          (fun i _ ↦ M.effect_integrable i i)
      _ = ∑ _i : Fin D, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hdiag i
      _ = (D : ℂ) := by simp
  have hone :
      ∫ _z : Outcome, (1 : ℂ) ∂M.base = (D : ℂ) := by
    rw [← htrace]
    apply integral_congr_ae
    filter_upwards [M.effect_ae_trace_one] with z hz
    exact hz.symm
  rw [integral_const] at hone
  have hre := congrArg Complex.re hone
  simpa using hre

end PhysicalPOVM.DominatedPOVM

end

end TomographyOracleCore
