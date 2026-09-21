import TomographyOracleCore.MatrixReduction

namespace TomographyOracleCore

open MatrixReduction

/-!
# Dimension-agnostic complex Grassmann packing statement

This module only gives a typed formulation of the basic Grassmann packing
input.  It does not assert that the input is inhabited and does not state a
tomography or minimax conclusion.
-/

/-- A complex square matrix is an orthogonal projector when it is Hermitian
and idempotent. -/
def IsComplexOrthogonalProjector {k : ℕ}
    (P : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  P.IsHermitian ∧ IsIdempotentElem P

/-- The rank-`m` specialization of `IsComplexOrthogonalProjector`. -/
def IsRankMComplexOrthogonalProjector {k : ℕ} (m : ℕ)
    (P : Matrix (Fin k) (Fin k) ℂ) : Prop :=
  IsComplexOrthogonalProjector P ∧ P.rank = m

/-- A bundled rank-`m` complex orthogonal projector.  Bundling the proof makes
the Hermitian trace norm of the difference of two projectors a total
definition. -/
structure RankMComplexOrthogonalProjector (k m : ℕ) where
  matrix : Matrix (Fin k) (Fin k) ℂ
  property : IsRankMComplexOrthogonalProjector m matrix

namespace RankMComplexOrthogonalProjector

theorem isOrthogonalProjector {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    IsComplexOrthogonalProjector P.matrix :=
  P.property.1

theorem isHermitian {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) : P.matrix.IsHermitian :=
  P.property.1.1

theorem isIdempotent {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    IsIdempotentElem P.matrix :=
  P.property.1.2

theorem rank_eq {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) : P.matrix.rank = m :=
  P.property.2

@[ext]
theorem ext {k m : ℕ} {P Q : RankMComplexOrthogonalProjector k m}
    (h : P.matrix = Q.matrix) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

end RankMComplexOrthogonalProjector

/-- Hermitian Schatten-one distance between two bundled orthogonal
projectors. -/
noncomputable def projectorHermitianTraceDistance {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) : ℝ :=
  hermitianTraceNorm (P.matrix - Q.matrix) (P.isHermitian.sub Q.isHermitian)

theorem projectorHermitianTraceDistance_nonnegative {k m : ℕ}
    (P Q : RankMComplexOrthogonalProjector k m) :
    0 ≤ projectorHermitianTraceDistance P Q :=
  hermitianTraceNorm_nonneg _ _

/-- Concrete finite witness for the dimension-`k`, rank-`m` complex
Grassmann packing input.  The family is indexed by `Fin card`, so `card` is
its stated cardinality. -/
structure ComplexGrassmannPackingWitness (k m : ℕ) where
  card : ℕ
  projector : Fin card → RankMComplexOrthogonalProjector k m
  log_cardinality_lower :
    (25 / 4608 : ℝ) * (m : ℝ) * (k : ℝ) ≤ Real.log (card : ℝ)
  pairwise_separated : ∀ i j, i ≠ j →
    (m : ℝ) / 2 ≤
      projectorHermitianTraceDistance (projector i) (projector j)

/-- Exact dimension-agnostic basic input: for `k ≥ 3`, `m ≥ 1`, and
`3m ≤ k`, a rank-`m` complex orthogonal-projector packing exists with
log-cardinality at least `(25/4608)mk` and pairwise Hermitian trace-norm
separation at least `m/2`.

This is only a proposition naming the statement; no inhabitant is supplied in
this module. -/
def ComplexGrassmannPackingInput : Prop :=
  ∀ k m : ℕ, 3 ≤ k → 1 ≤ m → 3 * m ≤ k →
    Nonempty (ComplexGrassmannPackingWitness k m)

/-- Specialize a supplied Grassmann packing input to one admissible pair of
dimensions. -/
theorem complexGrassmannPackingWitness_of_input
    (h : ComplexGrassmannPackingInput)
    (k m : ℕ) (hk : 3 ≤ k) (hm : 1 ≤ m) (hkm : 3 * m ≤ k) :
    Nonempty (ComplexGrassmannPackingWitness k m) :=
  h k m hk hm hkm

end TomographyOracleCore
