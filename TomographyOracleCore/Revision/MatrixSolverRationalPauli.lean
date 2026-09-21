import TomographyOracleCore.Revision.MatrixSolverRationalInput

/-! Executable Gaussian-rational Pauli matrices and channel application.

The channel application reads the `d²` supplied rational multipliers and
uses the explicit Pauli reconstruction. It never enumerates a Clifford
group. Correctness for the periodic channel is reduced precisely to the
multiplier-table identity, which is the two-state transfer calculation in
the paper; that preprocessing identity is not assumed by the executable
definition and is displayed as a premise of the interpretation theorem.
-/

namespace TomographyOracleCore.Revision.MatrixSolver

open MatrixReduction AlgorithmResources FinitePrecision
open scoped BigOperators

set_option maxHeartbeats 1000000

@[simp] theorem cast_qRat (r : ℚ) : qComplexToComplex (r : QComplex) = (r : ℂ) := by
  change qComplexToComplex (algebraMap ℚ QComplex r) = algebraMap ℚ ℂ r
  exact qComplexToComplex.map_rat_algebraMap r

def rationalImaginaryUnit : QComplex := ⟨0, 1⟩

@[simp] theorem cast_rationalImaginaryUnit :
    qComplexToComplex rationalImaginaryUnit = Complex.I := by
  simp [rationalImaginaryUnit, qComplexToComplex_apply]

def rationalWordCharacter (K : ℕ) (x y : PauliBinaryWord K) : ℚ :=
  if binaryDotProduct K x y = 0 then 1 else -1

@[simp] theorem cast_rationalWordCharacter (K : ℕ) (x y : PauliBinaryWord K) :
    (rationalWordCharacter K x y : ℝ) = binaryWordCharacter K x y := by
  unfold rationalWordCharacter binaryWordCharacter binarySign
  split_ifs <;> norm_num

theorem wordCharacter_eq_one_iff (K : ℕ) (x y : PauliBinaryWord K) :
    binaryWordCharacter K x y = 1 ↔ binaryDotProduct K x y = 0 := by
  by_cases h : binaryDotProduct K x y = 0 <;>
    norm_num [binaryWordCharacter, binarySign, h]

def rationalPauliPhase (K : ℕ) (p : PauliLabel K) : QComplex :=
  if binaryDotProduct K p.2 p.1 = 0 then 1 else rationalImaginaryUnit

@[simp] theorem cast_rationalPauliPhase (K : ℕ) (p : PauliLabel K) :
    qComplexToComplex (rationalPauliPhase K p) = hermitianPauliPhase K p := by
  simp only [rationalPauliPhase, hermitianPauliPhase, wordCharacter_eq_one_iff]
  split_ifs
  · exact map_one _
  · exact cast_rationalImaginaryUnit

def rationalBinaryPauliMatrix (K : ℕ) (p : PauliLabel K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex :=
  fun a b => if a = b + p.1 then (rationalWordCharacter K p.2 b : QComplex) else 0

theorem cast_rationalBinaryPauliMatrix (K : ℕ) (p : PauliLabel K) :
    castQMatrix (rationalBinaryPauliMatrix K p) = binaryPauliMatrix K p := by
  ext a b
  simp only [castQMatrix_apply, rationalBinaryPauliMatrix, binaryPauliMatrix]
  split_ifs
  · rw [cast_qRat]
    have hc := congrArg Complex.ofReal (cast_rationalWordCharacter K p.2 b)
    simpa only [Complex.ofReal_ratCast] using hc
  · exact map_zero _

/-- All Pauli entries are computed with the four Gaussian-rational phases. -/
def rationalHermitianPauliMatrix (K : ℕ) (p : PauliLabel K) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex :=
  rationalPauliPhase K p • rationalBinaryPauliMatrix K p

@[simp] theorem cast_rationalHermitianPauliMatrix (K : ℕ) (p : PauliLabel K) :
    castQMatrix (rationalHermitianPauliMatrix K p) = hermitianBinaryPauliMatrix K p := by
  rw [rationalHermitianPauliMatrix, castQMatrix_qcomplex_smul,
    cast_rationalPauliPhase, cast_rationalBinaryPauliMatrix, hermitianBinaryPauliMatrix]

def rationalPauliCoefficient (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex)
    (p : PauliLabel K) : QComplex :=
  (rationalHermitianPauliMatrix K p * A).trace

@[simp] theorem cast_rationalPauliCoefficient (K : ℕ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex) (p : PauliLabel K) :
    qComplexToComplex (rationalPauliCoefficient K A p) =
      binaryHermitianPauliCoefficient K (castQMatrix A) p := by
  rw [rationalPauliCoefficient, qComplexToComplex_trace, castQMatrix_mul,
    cast_rationalHermitianPauliMatrix, binaryHermitianPauliCoefficient]

/-- Explicit rational channel evaluation from a rational Pauli multiplier
table. The only finite enumeration is over the `d²` Pauli labels. -/
def rationalPauliChannel (K : ℕ) (lambda : PauliLabel K → ℚ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex) :
    Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex :=
  ((2 : ℚ) ^ K)⁻¹ • ∑ p : PauliLabel K,
    (rationalPauliCoefficient K A p * (lambda p : QComplex)) •
      rationalHermitianPauliMatrix K p

theorem cast_rationalPauliChannel (K : ℕ) (lambda : PauliLabel K → ℚ)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex) :
    castQMatrix (rationalPauliChannel K lambda A) =
      ((2 : ℂ) ^ K)⁻¹ • ∑ p : PauliLabel K,
        (binaryHermitianPauliCoefficient K (castQMatrix A) p * ((lambda p : ℝ) : ℂ)) •
          hermitianBinaryPauliMatrix K p := by
  rw [rationalPauliChannel, castQMatrix_rat_smul]
  simp only [castQMatrix_sum, castQMatrix_qcomplex_smul, map_mul,
    cast_rationalPauliCoefficient, cast_qRat, cast_rationalHermitianPauliMatrix,
    Complex.ofReal_ratCast]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  congr 1
  change (((((2 : ℚ) ^ K)⁻¹ : ℚ) : ℝ) : ℂ) = ((2 : ℂ) ^ K)⁻¹
  simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat, Complex.ofReal_inv,
    Complex.ofReal_pow, Complex.ofReal_ofNat]

theorem rationalPauliChannel_correct (K : ℕ) (lambda : PauliLabel K → ℚ)
    (channel : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)
    (hdiagonal : ∀ p, channel (hermitianBinaryPauliMatrix K p) =
      ((lambda p : ℝ) : ℂ) • hermitianBinaryPauliMatrix K p)
    (A : Matrix (PauliBinaryWord K) (PauliBinaryWord K) QComplex) :
    castQMatrix (rationalPauliChannel K lambda A) = channel (castQMatrix A) := by
  rw [cast_rationalPauliChannel,
    complexLinearPauliChannel_apply_reconstruction K channel (fun p => (lambda p : ℝ)) hdiagonal]

/-- Exact interpretation for the paper's periodic channel. The sole
remaining preprocessing premise names the multiplier values explicitly;
there is no hidden real-arithmetic or channel oracle. -/
theorem rationalPauliChannel_periodic_correct {n K : ℕ} (hdiv : K ∣ n)
    (lambda : PauliLabel ((n / K) * K) → ℚ)
    (hlambda : ∀ p, (lambda p : ℝ) = choKimPeriodicFullCalibratedEigenvalue p)
    (A : Matrix (PauliBinaryWord ((n / K) * K)) (PauliBinaryWord ((n / K) * K)) QComplex) :
    castQMatrix (rationalPauliChannel ((n / K) * K) lambda A) =
      choKimPeriodicFullCalibratedBinaryLinearChannel hdiv (castQMatrix A) := by
  apply rationalPauliChannel_correct
  intro p
  rw [hlambda p]
  exact choKimPeriodicFullCalibratedBinaryLinearChannel_hermitianPauli hdiv p

end TomographyOracleCore.Revision.MatrixSolver
