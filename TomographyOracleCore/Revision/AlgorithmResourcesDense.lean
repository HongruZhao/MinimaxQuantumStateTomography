import TomographyOracleCore.Revision.AlgorithmResourcesPowerArithmetic

/-!
# Materialized executable dense matrix powers and cached Rayleigh search

`Matrix` is a function type. Repeated products of unevaluated matrix
functions can recompute earlier powers at every entry access. This module
materializes every matrix product into nested array-backed `Vector`s.
The input, each power, and the final d Rayleigh scores are computed once.
The mathematical result is proved equal to the previous reference formula.
-/

namespace TomographyOracleCore.Revision.AlgorithmResources

open Matrix
open scoped BigOperators

/-- An eager array of eager rows. Array lookup is the only entry access. -/
abbrev DenseMatrix (d : ℕ) (α : Type*) := Vector (Vector α d) d

def denseOfMatrix {d : ℕ} {α : Type*} (A : Matrix (Fin d) (Fin d) α) : DenseMatrix d α :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => A i j))

def denseToMatrix {d : ℕ} {α : Type*} (A : DenseMatrix d α) : Matrix (Fin d) (Fin d) α :=
  fun i j => (A.get i).get j

@[simp] theorem denseToMatrix_ofMatrix {d : ℕ} {α : Type*}
    (A : Matrix (Fin d) (Fin d) α) : denseToMatrix (denseOfMatrix A) = A := by
  funext i j
  simp [denseToMatrix, denseOfMatrix, Vector.get, Fin.cast]

/-- A reusable materialization barrier for outer and inner iterative
algorithms. Its denotation is exactly the original matrix. -/
def materializeMatrix {d : ℕ} {α : Type*} (A : Matrix (Fin d) (Fin d) α) :
    Matrix (Fin d) (Fin d) α := denseToMatrix (denseOfMatrix A)

@[simp] theorem materializeMatrix_eq {d : ℕ} {α : Type*}
    (A : Matrix (Fin d) (Fin d) α) : materializeMatrix A = A := denseToMatrix_ofMatrix A

/-- Standard dense multiplication, forcing all d² output entries. -/
def denseMul {d : ℕ} {α : Type*} [Semiring α]
    (A B : DenseMatrix d α) : DenseMatrix d α :=
  denseOfMatrix (denseToMatrix A * denseToMatrix B)

@[simp] theorem denseToMatrix_mul {d : ℕ} {α : Type*} [Semiring α]
    (A B : DenseMatrix d α) :
    denseToMatrix (denseMul A B) = denseToMatrix A * denseToMatrix B :=
  denseToMatrix_ofMatrix _

/-- Materialized repeated multiplication. The previous power is an actual
array value, so this recursion does not rebuild earlier matrix entries. -/
def densePower {d : ℕ} {α : Type*} [Semiring α]
    (A : DenseMatrix d α) : ℕ → DenseMatrix d α
  | 0 => denseOfMatrix 1
  | k + 1 => denseMul (densePower A k) A

@[simp] theorem denseToMatrix_power {d : ℕ} {α : Type*} [Semiring α]
    (A : DenseMatrix d α) (k : ℕ) :
    denseToMatrix (densePower A k) = denseToMatrix A ^ k := by
  induction k with
  | zero => simp [densePower]
  | succ k ih => simp [densePower, ih, pow_succ]

/-- Cached column scores, computed once per starting basis vector. -/
def denseRayleighScores {d : ℕ}
    (A P : DenseMatrix d QComplex) : Vector ℚ d :=
  Vector.ofFn (fun j => qRayleigh (denseToMatrix A) (fun i => denseToMatrix P i j))

@[simp] theorem denseRayleighScores_get {d : ℕ}
    (A P : DenseMatrix d QComplex) (j : Fin d) :
    (denseRayleighScores A P).get j =
      qRayleigh (denseToMatrix A) (fun i => denseToMatrix P i j) := by
  simp [denseRayleighScores, Vector.get, Fin.cast]

/-- Actual eager power search: materialize input and powers, cache all
Rayleigh scores, then compare cached rational values. -/
def qDenseBestPowerVector {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) : Fin d → QComplex :=
  let input := denseOfMatrix A
  let power := densePower input k
  let scores := denseRayleighScores input power
  let best := ((List.finRange d).argmax (fun j => scores.get j)).getD ⟨0, hD⟩
  fun i => denseToMatrix power i best

/-- Exact agreement with the reference best-column formula, including its
tie-breaking rule. All existing accuracy proofs can rewrite by this lemma. -/
theorem qDenseBestPowerVector_eq {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) :
    qDenseBestPowerVector hD A k =
      qPowerColumn A k (qBestPowerColumn hD A k) := by
  simp only [qDenseBestPowerVector, denseToMatrix_power,
    denseToMatrix_ofMatrix, denseRayleighScores_get, qBestPowerColumn]
  rfl

theorem qDenseBestPowerVector_max {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) (j : Fin d) :
    qRayleigh A (qPowerColumn A k j) ≤ qRayleigh A (qDenseBestPowerVector hD A k) := by
  rw [qDenseBestPowerVector_eq]
  exact qBestPowerColumn_max hD A k j

/-- Array-valued output interface. Callers should retain this value across
entry accesses; unlike a returned function, the output cannot be eta
expanded into a recomputation of the search at each coordinate. -/
def qDenseBestPowerColumn {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) : Vector QComplex d :=
  let input := denseOfMatrix A
  let power := densePower input k
  let scores := denseRayleighScores input power
  let best := ((List.finRange d).argmax (fun j => scores.get j)).getD ⟨0, hD⟩
  Vector.ofFn (fun i => denseToMatrix power i best)

@[simp] theorem qDenseBestPowerColumn_get {d : ℕ} (hD : 0 < d)
    (A : Matrix (Fin d) (Fin d) QComplex) (k : ℕ) (i : Fin d) :
    (qDenseBestPowerColumn hD A k).get i = qDenseBestPowerVector hD A k i := by
  simp [qDenseBestPowerColumn, qDenseBestPowerVector, Vector.get, Fin.cast]

#print axioms qDenseBestPowerVector_eq
#print axioms qDenseBestPowerVector_max
#print axioms qDenseBestPowerColumn_get

end TomographyOracleCore.Revision.AlgorithmResources
