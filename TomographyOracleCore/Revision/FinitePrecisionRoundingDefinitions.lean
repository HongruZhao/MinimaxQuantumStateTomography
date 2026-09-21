import TomographyOracleCore.Revision.AlgorithmResourcesPowerArithmetic
import TomographyOracleCore.Revision.AlgorithmResourcesDyadic

/-! Executable fixed-precision rounding and trace-normalized PSD repair.
Correctness is proved in `FinitePrecisionRounding`; the definitions here
are separated so that word-size analysis can use the exact arithmetic.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open AlgorithmResources Matrix
open scoped BigOperators

/-- Independently round both rational coordinates to denominator `2^s`. -/
def qRoundEntry (s : ℕ) (z : QComplex) : QComplex :=
  ⟨dyadicRound s z.re, dyadicRound s z.im⟩

def qRoundRawMatrix {D : ℕ} (s : ℕ)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  A.map (qRoundEntry s)

/-- Symmetrization makes Hermitian symmetry exact after coordinate rounding.
All coordinates have denominator dividing `2^(s+1)`. -/
def qHermitianRound {D : ℕ} (s : ℕ)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  (1 / 2 : ℚ) • (qRoundRawMatrix s A + (qRoundRawMatrix s A).conjTranspose)

/-- An explicit bound for the sum of absolute entry errors. -/
def qRoundingEta (D s : ℕ) : ℚ := 2 * (D : ℚ) ^ 2 / (2 : ℚ) ^ s

def qRepairDenominator {D : ℕ}
    (H : Matrix (Fin D) (Fin D) QComplex) (eta : ℚ) : ℚ :=
  (∑ i, (H i i).re) + (D : ℚ) * eta

/-- Exact rational shift and trace normalization. -/
def qShiftNormalize {D : ℕ}
    (H : Matrix (Fin D) (Fin D) QComplex) (eta : ℚ) :
    Matrix (Fin D) (Fin D) QComplex :=
  (qRepairDenominator H eta)⁻¹ • (H + eta • (1 : Matrix (Fin D) (Fin D) QComplex))

/-- Fixed precision approximation of a density matrix, with PSD and trace
repair. Every operation is executable rational arithmetic. -/
def qRoundDensity {D : ℕ} (s : ℕ)
    (A : Matrix (Fin D) (Fin D) QComplex) : Matrix (Fin D) (Fin D) QComplex :=
  qShiftNormalize (qHermitianRound s A) (qRoundingEta D s)

end TomographyOracleCore.Revision.FinitePrecision
