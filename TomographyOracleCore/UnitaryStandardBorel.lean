import TomographyOracleCore.UnitaryHaarOrientation
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.MetricSpace.Polish

namespace TomographyOracleCore

/-!
# Standard-Borel structure for finite-dimensional unitary groups

The matrix topology is the finite product topology on its complex entries,
so it is Polish.  The unitary group is a closed subset of that matrix space
and is therefore Polish as well.  Its existing measurable structure is the
Borel structure inherited from the matrix subtype.
-/

noncomputable instance unitaryMatrixPolishSpace (D : ℕ) :
    PolishSpace (unitary (Matrix (Fin D) (Fin D) ℂ)) := by
  letI : PolishSpace (Matrix (Fin D) (Fin D) ℂ) := by
    change PolishSpace (Fin D → Fin D → ℂ)
    infer_instance
  exact isClosed_unitary.polishSpace

noncomputable instance unitaryMatrixStandardBorelSpace (D : ℕ) :
    StandardBorelSpace (unitary (Matrix (Fin D) (Fin D) ℂ)) := by
  apply StandardBorelSpace.mk
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end TomographyOracleCore
