import TomographyOracleCore.CliffordPauliCounting
import Mathlib.Algebra.BigOperators.Fin

/-! An explicit binary computational-basis numbering, with no choice-based enumeration. -/

namespace TomographyOracleCore

/-- The little-endian binary index of a computational word. Both directions
are executable; `finFunctionFinEquiv` proves that the digit maps are inverse. -/
def computableBinaryWordIndex (n : ℕ) : PauliBinaryWord n ≃ Fin (2 ^ n) :=
  (Equiv.piCongrRight (fun _ : Fin n => (ZMod.finEquiv 2).symm.toEquiv)).trans
    finFunctionFinEquiv

/-- The same explicit numbering under the paper's exact block divisibility condition. -/
def computableChoKimBlockIndex {n K : ℕ} (hdiv : K ∣ n) :
    PauliBinaryWord ((n / K) * K) ≃ Fin (2 ^ n) :=
  (computableBinaryWordIndex ((n / K) * K)).trans
    (finCongr (congrArg (fun N => 2 ^ N) (Nat.div_mul_cancel hdiv)))

theorem computableBinaryWordIndex_injective (n : ℕ) :
    Function.Injective (computableBinaryWordIndex n) := (computableBinaryWordIndex n).injective

theorem computableChoKimBlockIndex_bijective {n K : ℕ} (hdiv : K ∣ n) :
    Function.Bijective (computableChoKimBlockIndex hdiv) :=
  (computableChoKimBlockIndex hdiv).bijective

#print axioms computableChoKimBlockIndex_bijective

end TomographyOracleCore
