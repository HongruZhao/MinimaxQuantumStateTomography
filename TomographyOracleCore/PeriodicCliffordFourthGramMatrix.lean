import TomographyOracleCore.PeriodicCliffordFourthSectors

namespace TomographyOracleCore

noncomputable section

/-!
# The certified 30-sector Gram matrix

This module turns the finite intersection certificate into the literal scalar
Gram matrix used by the periodic trace-cycle argument.  It deliberately makes
no assertion yet that these scalars are Hilbert--Schmidt products of concrete
fourth-copy Clifford sector operators; that representation-theoretic
identification remains separate.
-/

/-- Scalar Gram matrix attached to the certified fourth-copy intersection
table: `G_x(T,S) = x ^ dim(T \cap S)`. -/
def qubitFourthGramMatrix (x : ℝ) : Matrix (Fin 30) (Fin 30) ℝ :=
  fun i j ↦ x ^ qubitFourthIntersectionEntry i j

@[simp] theorem qubitFourthGramMatrix_apply
    (x : ℝ) (i j : Fin 30) :
    qubitFourthGramMatrix x i j =
      x ^ qubitFourthIntersectionEntry i j := rfl

/-- The table-defined Gram entry is the corresponding power of the actual
intersection dimension of the explicit binary spans. -/
theorem qubitFourthGramMatrix_eq_intersectionDimensionPow
    (x : ℝ) (i j : Fin 30) :
    qubitFourthGramMatrix x i j =
      x ^ qubitFourthIntersectionDimension i j := by
  rw [qubitFourthGramMatrix_apply,
    qubitFourthIntersectionMatrix_exact i j]

/-- Every certified intersection dimension is one of `1,2,3,4`. -/
theorem qubitFourthIntersectionEntry_bounds : ∀ i j : Fin 30,
    1 ≤ qubitFourthIntersectionEntry i j ∧
      qubitFourthIntersectionEntry i j ≤ 4 := by
  decide

/-- The explicit intersection table is symmetric. -/
theorem qubitFourthIntersectionEntry_comm : ∀ i j : Fin 30,
    qubitFourthIntersectionEntry i j =
      qubitFourthIntersectionEntry j i := by
  decide

/-- The certified scalar Gram matrix is symmetric. -/
theorem qubitFourthGramMatrix_comm
    (x : ℝ) (i j : Fin 30) :
    qubitFourthGramMatrix x i j = qubitFourthGramMatrix x j i := by
  simp only [qubitFourthGramMatrix_apply]
  rw [qubitFourthIntersectionEntry_comm i j]

/-- For a nonnegative local Hilbert-space dimension, every Gram entry is
nonnegative.  This is the `hG` input required by the abstract trace-cycle
endpoint. -/
theorem qubitFourthGramMatrix_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    ∀ i j, 0 ≤ qubitFourthGramMatrix x i j := by
  intro i j
  exact pow_nonneg hx _

/-- Positive local dimension gives strictly positive Gram entries. -/
theorem qubitFourthGramMatrix_pos
    {x : ℝ} (hx : 0 < x) :
    ∀ i j, 0 < qubitFourthGramMatrix x i j := by
  intro i j
  exact pow_pos hx _

end

end TomographyOracleCore
