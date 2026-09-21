import TomographyOracleCore.HardProjectorState

namespace TomographyOracleCore

open MatrixReduction
open scoped ComplexOrder

/-!
# Unitary conjugation of finite density operators

This module proves, without an external invariance premise, that the map
`A ↦ U A Uᴴ` preserves positivity, trace, characteristic roots, ordered
eigenvalues, Hermitian trace distance, and the manuscript spectral-decay
class.  The final section applies one common ambient unitary to the complete
projector hard family.
-/

/-- Conjugation of a square matrix by an ambient unitary. -/
noncomputable def unitaryConjugateMatrix {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  Unitary.conjStarAlgAut ℂ _ U A

theorem unitaryConjugateMatrix_apply {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) :
    unitaryConjugateMatrix U A =
      (U : Matrix (Fin D) (Fin D) ℂ) * A *
        star (U : Matrix (Fin D) (Fin D) ℂ) := by
  rfl

/-- Unitary conjugation preserves positive semidefiniteness. -/
theorem unitaryConjugateMatrix_posSemidef {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.PosSemidef) :
    (unitaryConjugateMatrix U A).PosSemidef := by
  rw [unitaryConjugateMatrix_apply]
  exact hA.mul_mul_conjTranspose_same (U : Matrix (Fin D) (Fin D) ℂ)

/-- Unitary conjugation preserves Hermiticity, independently of positivity. -/
theorem unitaryConjugateMatrix_isHermitian {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    {A : Matrix (Fin D) (Fin D) ℂ} (hA : A.IsHermitian) :
    (unitaryConjugateMatrix U A).IsHermitian := by
  let e := Unitary.conjStarAlgAut ℂ _ U
  rw [Matrix.IsHermitian]
  change star (e A) = e A
  rw [← map_star]
  simpa only [Matrix.star_eq_conjTranspose] using congrArg e hA.eq

/-- Matrix trace is invariant under unitary conjugation. -/
theorem unitaryConjugateMatrix_trace {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (unitaryConjugateMatrix U A).trace = A.trace := by
  rw [unitaryConjugateMatrix_apply, Matrix.trace_mul_cycle]
  simp only [Unitary.coe_star_mul_self, one_mul]

/-- Characteristic polynomial is invariant under unitary conjugation. -/
theorem unitaryConjugateMatrix_charpoly {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (unitaryConjugateMatrix U A).charpoly = A.charpoly := by
  rw [unitaryConjugateMatrix_apply, Matrix.charpoly_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul]

/-- The full complex characteristic-root multiset, with multiplicities, is
invariant under unitary conjugation. -/
theorem unitaryConjugateMatrix_roots {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (unitaryConjugateMatrix U A).charpoly.roots = A.charpoly.roots := by
  rw [unitaryConjugateMatrix_charpoly]

/-- The real characteristic-root multiset used by the Hermitian spectral
formulas is invariant as well. -/
theorem unitaryConjugateMatrix_roots_re {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) :
    (unitaryConjugateMatrix U A).charpoly.roots.map RCLike.re =
      A.charpoly.roots.map RCLike.re := by
  rw [unitaryConjugateMatrix_charpoly]

/-- Unitary conjugation respects subtraction. -/
theorem unitaryConjugateMatrix_sub {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A B : Matrix (Fin D) (Fin D) ℂ) :
    unitaryConjugateMatrix U A - unitaryConjugateMatrix U B =
      unitaryConjugateMatrix U (A - B) := by
  exact ((Unitary.conjStarAlgAut ℂ _ U).map_sub A B).symm

/-- Conjugation by a unitary sends density operators to density operators. -/
noncomputable def unitaryConjugateDensityOperator {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) : DensityOperator (Fin D) where
  matrix := unitaryConjugateMatrix U ρ.matrix
  posSemidef := unitaryConjugateMatrix_posSemidef U ρ.posSemidef
  trace_eq_one := by
    rw [unitaryConjugateMatrix_trace, ρ.trace_eq_one]

@[simp] theorem unitaryConjugateDensityOperator_matrix {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) :
    (unitaryConjugateDensityOperator U ρ).matrix =
      unitaryConjugateMatrix U ρ.matrix := rfl

@[simp] theorem unitaryConjugateDensityOperator_trace {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) :
    (unitaryConjugateDensityOperator U ρ).matrix.trace = 1 := by
  exact (unitaryConjugateDensityOperator U ρ).trace_eq_one

/-- Hermitian trace norm is exactly unitary invariant. -/
theorem hermitianTraceNorm_unitaryConjugate {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (A : Matrix (Fin D) (Fin D) ℂ) (hA : A.IsHermitian) :
    hermitianTraceNorm (unitaryConjugateMatrix U A)
        (unitaryConjugateMatrix_isHermitian U hA) =
      hermitianTraceNorm A hA := by
  rw [hermitianTraceNorm_eq_roots_abs_sum,
    hermitianTraceNorm_eq_roots_abs_sum, unitaryConjugateMatrix_charpoly]

/-- Applying one common unitary to two density operators preserves their
Hermitian Schatten-one distance exactly. -/
theorem unitaryConjugateDensityOperator_traceDistance {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (σ ρ : DensityOperator (Fin D)) :
    hermitianTraceNorm
        ((unitaryConjugateDensityOperator U σ).matrix -
          (unitaryConjugateDensityOperator U ρ).matrix)
        ((unitaryConjugateDensityOperator U σ).sub_isHermitian
          (unitaryConjugateDensityOperator U ρ)) =
      hermitianTraceNorm (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ) := by
  calc
    _ = hermitianTraceNorm (unitaryConjugateMatrix U (σ.matrix - ρ.matrix))
          (unitaryConjugateMatrix_isHermitian U (σ.sub_isHermitian ρ)) := by
      apply hermitianTraceNorm_congr
      exact unitaryConjugateMatrix_sub U σ.matrix ρ.matrix
    _ = _ := hermitianTraceNorm_unitaryConjugate U _ _

/-- The ordered eigenvalue function itself is unchanged by unitary
conjugation. -/
theorem unitaryConjugateDensityOperator_eigenvalues₀ {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) :
    (unitaryConjugateDensityOperator U ρ).isHermitian.eigenvalues₀ =
      ρ.isHermitian.eigenvalues₀ := by
  rw [← List.ofFn_inj,
    ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀,
    ← Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀]
  change ((unitaryConjugateMatrix U ρ.matrix).charpoly.roots.map
      RCLike.re).sort (· ≥ ·) =
    (ρ.matrix.charpoly.roots.map RCLike.re).sort (· ≥ ·)
  rw [unitaryConjugateMatrix_charpoly]

/-- Every ordered spectral tail is unchanged by unitary conjugation. -/
theorem unitaryConjugateDensityOperator_orderedSpectralTail {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) (s : ℕ) :
    orderedSpectralTail (unitaryConjugateDensityOperator U ρ) s =
      orderedSpectralTail ρ s := by
  unfold orderedSpectralTail
  rw [unitaryConjugateDensityOperator_eigenvalues₀]

/-- Spectral-decay membership is preserved in the forward direction. -/
theorem unitaryConjugateDensityOperator_mem_spectralDecayClass {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) (alpha L : ℝ)
    (hρ : ρ ∈ spectralDecayClass D alpha L) :
    unitaryConjugateDensityOperator U ρ ∈ spectralDecayClass D alpha L := by
  rw [mem_spectralDecayClass_iff] at hρ ⊢
  intro s hs hsD
  rw [unitaryConjugateDensityOperator_orderedSpectralTail]
  exact hρ s hs hsD

/-- In fact spectral-decay membership is exactly invariant. -/
theorem unitaryConjugateDensityOperator_mem_spectralDecayClass_iff {D : ℕ}
    (U : unitary (Matrix (Fin D) (Fin D) ℂ))
    (ρ : DensityOperator (Fin D)) (alpha L : ℝ) :
    unitaryConjugateDensityOperator U ρ ∈ spectralDecayClass D alpha L ↔
      ρ ∈ spectralDecayClass D alpha L := by
  rw [mem_spectralDecayClass_iff, mem_spectralDecayClass_iff]
  constructor
  · intro h s hs hsD
    rw [← unitaryConjugateDensityOperator_orderedSpectralTail U ρ s]
    exact h s hs hsD
  · intro h s hs hsD
    rw [unitaryConjugateDensityOperator_orderedSpectralTail]
    exact h s hs hsD

/-! ## Common unitary orientation of the hard projector family -/

/-- Apply one common ambient unitary orientation to a projector hard state. -/
noncomputable def orientedHardProjectorDensityOperator {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    DensityOperator (Fin (k + 2)) :=
  unitaryConjugateDensityOperator U
    (hardProjectorDensityOperator P b hm hb0 hbquarter)

@[simp] theorem orientedHardProjectorDensityOperator_matrix {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    (orientedHardProjectorDensityOperator U P b hm hb0 hbquarter).matrix =
      unitaryConjugateMatrix U (hardProjectorMatrix P b) := rfl

/-- Every commonly oriented hard projector state remains in the exact
spectral-decay class. -/
theorem orientedHardProjectorDensityOperator_mem_spectralDecayClass
    {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P : RankMComplexOrthogonalProjector k m) (alpha L b : ℝ)
    (hm : 1 ≤ m) (halpha : 1 < alpha) (hL : 1 ≤ L)
    (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hbscaled :
      b ≤ (2 : ℝ) ^ (1 - alpha) * L * (m : ℝ) ^ (1 - alpha)) :
    orientedHardProjectorDensityOperator U P b hm hb0 hbquarter ∈
      spectralDecayClass (k + 2) alpha L := by
  apply unitaryConjugateDensityOperator_mem_spectralDecayClass
  exact hardProjectorDensityOperator_mem_spectralDecayClass P alpha L b hm
    halpha hL hb0 hbquarter hbscaled

/-- The exact Grassmann-to-state distance scaling survives one common
ambient unitary orientation. -/
theorem orientedHardProjectorDensityOperator_traceDistance_eq {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P Q : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4) :
    hermitianTraceNorm
        ((orientedHardProjectorDensityOperator U P b hm hb0 hbquarter).matrix -
          (orientedHardProjectorDensityOperator U Q b hm hb0 hbquarter).matrix)
        ((orientedHardProjectorDensityOperator U P b hm hb0 hbquarter).sub_isHermitian
          (orientedHardProjectorDensityOperator U Q b hm hb0 hbquarter)) =
      (b / (m : ℝ)) * projectorHermitianTraceDistance P Q := by
  unfold orientedHardProjectorDensityOperator
  rw [unitaryConjugateDensityOperator_traceDistance]
  exact hardProjectorDensityOperator_traceDistance_eq P Q b hm hb0 hbquarter

/-- Pairwise Grassmann separation at least `m/2` remains physical state
separation at least `b/2` after a common unitary orientation. -/
theorem orientedHardProjectorDensityOperator_traceDistance_ge_half_mass
    {k m : ℕ}
    (U : unitary (Matrix (Fin (k + 2)) (Fin (k + 2)) ℂ))
    (P Q : RankMComplexOrthogonalProjector k m) (b : ℝ)
    (hm : 1 ≤ m) (hb0 : 0 ≤ b) (hbquarter : b ≤ 1 / 4)
    (hsep : (m : ℝ) / 2 ≤ projectorHermitianTraceDistance P Q) :
    b / 2 ≤
      hermitianTraceNorm
        ((orientedHardProjectorDensityOperator U P b hm hb0 hbquarter).matrix -
          (orientedHardProjectorDensityOperator U Q b hm hb0 hbquarter).matrix)
        ((orientedHardProjectorDensityOperator U P b hm hb0 hbquarter).sub_isHermitian
          (orientedHardProjectorDensityOperator U Q b hm hb0 hbquarter)) := by
  unfold orientedHardProjectorDensityOperator
  rw [unitaryConjugateDensityOperator_traceDistance]
  exact hardProjectorDensityOperator_traceDistance_ge_half_mass P Q b hm hb0
    hbquarter hsep

end TomographyOracleCore
