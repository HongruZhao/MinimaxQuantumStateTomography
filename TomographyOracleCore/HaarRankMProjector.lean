import TomographyOracleCore.ProjectiveHaarPOVM
import TomographyOracleCore.UnitaryConjugation

namespace TomographyOracleCore

open MeasureTheory Set
open scoped Matrix.Norms.L2Operator

noncomputable section

/-!
# Canonical rank-m projectors and their unitary Haar orbit

This module supplies the exact compact-group infrastructure behind a Haar
random rank-`m` orthogonal projector.  It constructs the coordinate
projector, proves that unitary conjugation preserves every bundled projector
field, equips the compact unitary matrix group with its normalized Haar
probability measure, and proves both left and right invariance.
-/

section Canonical

/-- The `0`/`1` diagonal of the coordinate projector onto the first `m`
coordinates. -/
def canonicalRankMProjectorDiagonal (m k : ℕ) (i : Fin k) : ℂ :=
  if (i : ℕ) < m then 1 else 0

/-- The coordinate projector onto the first `m` standard basis vectors. -/
def canonicalRankMProjectorMatrix (k m : ℕ) : Matrix (Fin k) (Fin k) ℂ :=
  Matrix.diagonal (canonicalRankMProjectorDiagonal m k)

theorem canonicalRankMProjectorMatrix_isHermitian (k m : ℕ) :
    (canonicalRankMProjectorMatrix k m).IsHermitian := by
  rw [canonicalRankMProjectorMatrix, Matrix.isHermitian_diagonal_iff]
  intro i
  simp [canonicalRankMProjectorDiagonal, isSelfAdjoint_iff]

theorem canonicalRankMProjectorMatrix_isIdempotent (k m : ℕ) :
    IsIdempotentElem (canonicalRankMProjectorMatrix k m) := by
  rw [isIdempotentElem_iff]
  rw [canonicalRankMProjectorMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  simp [canonicalRankMProjectorDiagonal]

theorem canonicalRankMProjectorMatrix_rank (k m : ℕ) (hmk : m ≤ k) :
    (canonicalRankMProjectorMatrix k m).rank = m := by
  rw [canonicalRankMProjectorMatrix, Matrix.rank_diagonal]
  let e :
      {i : Fin k // canonicalRankMProjectorDiagonal m k i ≠ 0} ≃
        {i : Fin k // (i : ℕ) < m} :=
    Equiv.subtypeEquivRight fun i => by
      simp [canonicalRankMProjectorDiagonal]
  calc
    Fintype.card {i : Fin k // canonicalRankMProjectorDiagonal m k i ≠ 0} =
        Fintype.card {i : Fin k // (i : ℕ) < m} :=
      Fintype.card_congr e
    _ = Fintype.card (Fin m) :=
      Fintype.card_congr (Fin.castLEquiv hmk).symm
    _ = m := Fintype.card_fin m

/-- The canonical bundled rank-`m` complex orthogonal projector. -/
def canonicalRankMProjector (k m : ℕ) (hmk : m ≤ k) :
    RankMComplexOrthogonalProjector k m where
  matrix := canonicalRankMProjectorMatrix k m
  property := ⟨⟨canonicalRankMProjectorMatrix_isHermitian k m,
    canonicalRankMProjectorMatrix_isIdempotent k m⟩,
    canonicalRankMProjectorMatrix_rank k m hmk⟩

@[simp] theorem canonicalRankMProjector_matrix (k m : ℕ) (hmk : m ≤ k) :
    (canonicalRankMProjector k m hmk).matrix =
      canonicalRankMProjectorMatrix k m := rfl

end Canonical

section Conjugation

/-- Unitary conjugation of a bundled rank-`m` projector. -/
def unitaryConjugateRankMProjector {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (P : RankMComplexOrthogonalProjector k m) :
    RankMComplexOrthogonalProjector k m where
  matrix := unitaryConjugateMatrix U P.matrix
  property := by
    refine ⟨⟨unitaryConjugateMatrix_isHermitian U P.isHermitian, ?_⟩, ?_⟩
    · let e := Unitary.conjStarAlgAut ℂ _ U
      change IsIdempotentElem (e P.matrix)
      rw [isIdempotentElem_iff, ← map_mul, P.isIdempotent.eq]
    · rw [unitaryConjugateMatrix_apply]
      have hUdet : IsUnit (U : Matrix (Fin k) (Fin k) ℂ).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe
      have hSUdet : IsUnit (star (U : Matrix (Fin k) (Fin k) ℂ)).det :=
        (Matrix.isUnit_iff_isUnit_det _).mp Unitary.isUnit_coe.star
      calc
        ((U : Matrix (Fin k) (Fin k) ℂ) * P.matrix *
            star (U : Matrix (Fin k) (Fin k) ℂ)).rank =
            ((U : Matrix (Fin k) (Fin k) ℂ) * P.matrix).rank :=
          Matrix.rank_mul_eq_left_of_isUnit_det _ _ hSUdet
        _ = P.matrix.rank :=
          Matrix.rank_mul_eq_right_of_isUnit_det _ _ hUdet
        _ = m := P.rank_eq

@[simp] theorem unitaryConjugateRankMProjector_matrix {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (P : RankMComplexOrthogonalProjector k m) :
    (unitaryConjugateRankMProjector U P).matrix =
      unitaryConjugateMatrix U P.matrix := rfl

theorem unitaryConjugateMatrix_compose {k : ℕ}
    (U V : unitary (Matrix (Fin k) (Fin k) ℂ))
    (A : Matrix (Fin k) (Fin k) ℂ) :
    unitaryConjugateMatrix U (unitaryConjugateMatrix V A) =
      unitaryConjugateMatrix (U * V) A := by
  simp only [unitaryConjugateMatrix_apply, map_mul, map_star,
    Submonoid.coe_mul, star_mul]
  noncomm_ring

@[simp] theorem unitaryConjugateRankMProjector_compose {k m : ℕ}
    (U V : unitary (Matrix (Fin k) (Fin k) ℂ))
    (P : RankMComplexOrthogonalProjector k m) :
    unitaryConjugateRankMProjector U (unitaryConjugateRankMProjector V P) =
      unitaryConjugateRankMProjector (U * V) P := by
  apply RankMComplexOrthogonalProjector.ext
  exact unitaryConjugateMatrix_compose U V P.matrix

@[simp] theorem unitaryConjugateRankMProjector_one {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    unitaryConjugateRankMProjector 1 P = P := by
  apply RankMComplexOrthogonalProjector.ext
  simp [unitaryConjugateMatrix_apply]

theorem projectorHermitianTraceDistance_unitaryConjugate {k m : ℕ}
    (U : unitary (Matrix (Fin k) (Fin k) ℂ))
    (P Q : RankMComplexOrthogonalProjector k m) :
    projectorHermitianTraceDistance
        (unitaryConjugateRankMProjector U P)
        (unitaryConjugateRankMProjector U Q) =
      projectorHermitianTraceDistance P Q := by
  unfold projectorHermitianTraceDistance
  calc
    _ = MatrixReduction.hermitianTraceNorm
          (unitaryConjugateMatrix U (P.matrix - Q.matrix))
          (unitaryConjugateMatrix_isHermitian U
            (P.isHermitian.sub Q.isHermitian)) := by
      apply MatrixReduction.hermitianTraceNorm_congr
      exact unitaryConjugateMatrix_sub U P.matrix Q.matrix
    _ = _ := hermitianTraceNorm_unitaryConjugate U _ _

end Conjugation

section MeasurableSampler

/-- The bundled projector space carries the sigma algebra generated by its
matrix coordinates. -/
noncomputable instance rankMComplexOrthogonalProjectorMeasurableSpace
    (k m : ℕ) : MeasurableSpace (RankMComplexOrthogonalProjector k m) :=
  MeasurableSpace.comap RankMComplexOrthogonalProjector.matrix inferInstance

theorem continuous_unitaryConjugateMatrix_fixed {k : ℕ}
    (A : Matrix (Fin k) (Fin k) ℂ) :
    Continuous (fun U : unitary (Matrix (Fin k) (Fin k) ℂ) =>
      unitaryConjugateMatrix U A) := by
  simp only [unitaryConjugateMatrix_apply]
  fun_prop

theorem measurable_unitaryConjugateRankMProjector {k m : ℕ}
    (P : RankMComplexOrthogonalProjector k m) :
    Measurable (fun U : unitary (Matrix (Fin k) (Fin k) ℂ) =>
      unitaryConjugateRankMProjector U P) := by
  apply measurable_comap_iff.mpr
  exact (continuous_unitaryConjugateMatrix_fixed P.matrix).measurable

/-- The source-faithful random projector sampler `U ↦ U P₀ U*`. -/
def rankMProjectorSampler (k m : ℕ) (hmk : m ≤ k) :
    unitary (Matrix (Fin k) (Fin k) ℂ) →
      RankMComplexOrthogonalProjector k m :=
  fun U => unitaryConjugateRankMProjector U
    (canonicalRankMProjector k m hmk)

@[simp] theorem rankMProjectorSampler_one (k m : ℕ) (hmk : m ≤ k) :
    rankMProjectorSampler k m hmk 1 = canonicalRankMProjector k m hmk :=
  unitaryConjugateRankMProjector_one _

theorem rankMProjectorSampler_measurable (k m : ℕ) (hmk : m ≤ k) :
    Measurable (rankMProjectorSampler k m hmk) :=
  measurable_unitaryConjugateRankMProjector _

theorem rankMProjectorSampler_left_equivariant (k m : ℕ) (hmk : m ≤ k)
    (V U : unitary (Matrix (Fin k) (Fin k) ℂ)) :
    rankMProjectorSampler k m hmk (V * U) =
      unitaryConjugateRankMProjector V
        (rankMProjectorSampler k m hmk U) := by
  symm
  exact unitaryConjugateRankMProjector_compose V U _

end MeasurableSampler

end

end TomographyOracleCore
