import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceB23
import TomographyOracleCore.RelativeDesignReverseApproximation

namespace TomographyOracleCore

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

set_option maxHeartbeats 800000

local instance haarReferenceRelativeCPSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance haarReferenceRelativeCPStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Structural support and relative-CP endpoint for B.21--B.23 -/

theorem normalizedWeingartenDeltaThree_left_mul
    (D : ℕ) (a sigma tau : Equiv.Perm (Fin 3)) :
    normalizedWeingartenDeltaThree D (a * sigma) (a * tau) =
      normalizedWeingartenDeltaThree D sigma tau := by
  unfold normalizedWeingartenDeltaThree normalizedWeingartenThree
  have hprod : (a * sigma) * (a * tau)⁻¹ =
      a * (sigma * tau⁻¹) * a⁻¹ := by group
  rw [hprod, finThreeFullCycleCount_conj]
  simp

theorem normalizedWeingartenDeltaThree_right_mul
    (D : ℕ) (a sigma tau : Equiv.Perm (Fin 3)) :
    normalizedWeingartenDeltaThree D (sigma * a) (tau * a) =
      normalizedWeingartenDeltaThree D sigma tau := by
  unfold normalizedWeingartenDeltaThree normalizedWeingartenThree
  have hprod : (sigma * a) * (tau * a)⁻¹ = sigma * tau⁻¹ := by group
  rw [hprod]
  simp

theorem normalizedWeingartenDeltaThree_inv
    (D : ℕ) (sigma tau : Equiv.Perm (Fin 3)) :
    normalizedWeingartenDeltaThree D sigma⁻¹ tau⁻¹ =
      normalizedWeingartenDeltaThree D sigma tau := by
  unfold normalizedWeingartenDeltaThree normalizedWeingartenThree
  have hcount :
      finThreeFullCycleCount (sigma⁻¹ * (tau⁻¹)⁻¹) =
        finThreeFullCycleCount (sigma * tau⁻¹) := by
    calc
      finThreeFullCycleCount (sigma⁻¹ * (tau⁻¹)⁻¹) =
          finThreeFullCycleCount
            (sigma⁻¹ * (sigma * tau⁻¹)⁻¹ * (sigma⁻¹)⁻¹) := by
              congr 1
              group
      _ = finThreeFullCycleCount (sigma * tau⁻¹)⁻¹ :=
        finThreeFullCycleCount_conj _ _
      _ = finThreeFullCycleCount (sigma * tau⁻¹) :=
        finThreeFullCycleCount_inv _
  rw [hcount]
  simp

theorem diagonalQ_mul_normalizedWeingartenWeightedErrorThree
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (a : Equiv.Perm (Fin 3)) :
    Q a a * normalizedWeingartenWeightedErrorThree D Q =
      normalizedWeingartenWeightedErrorThree D Q := by
  unfold normalizedWeingartenWeightedErrorThree
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, mul_smul_comm, hmul]
  calc
    (∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma tau : ℂ) •
          Q (a * sigma) (a * tau)) =
      ∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D (a * sigma) (a * tau) : ℂ) •
          Q (a * sigma) (a * tau) := by
            apply Fintype.sum_congr
            intro sigma
            apply Fintype.sum_congr
            intro tau
            rw [normalizedWeingartenDeltaThree_left_mul]
    _ = ∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau :=
      finThree_sum_sum_mulLeft a
        (fun sigma tau ↦
          (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau)

theorem normalizedWeingartenWeightedErrorThree_mul_diagonalQ
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (a : Equiv.Perm (Fin 3)) :
    normalizedWeingartenWeightedErrorThree D Q * Q a a =
      normalizedWeingartenWeightedErrorThree D Q := by
  unfold normalizedWeingartenWeightedErrorThree
  rw [Finset.sum_mul]
  simp_rw [Finset.sum_mul, smul_mul_assoc, hmul]
  calc
    (∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma tau : ℂ) •
          Q (sigma * a) (tau * a)) =
      ∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D (sigma * a) (tau * a) : ℂ) •
          Q (sigma * a) (tau * a) := by
            apply Fintype.sum_congr
            intro sigma
            apply Fintype.sum_congr
            intro tau
            rw [normalizedWeingartenDeltaThree_right_mul]
    _ = ∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau :=
      finThree_sum_sum_mulRight a
        (fun sigma tau ↦
          (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau)

theorem finiteThreeMomentReferenceProjection_weingartenError_support
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau')) :
    finiteThreeMomentReferenceProjection Q *
        normalizedWeingartenWeightedErrorThree D Q *
        finiteThreeMomentReferenceProjection Q =
      normalizedWeingartenWeightedErrorThree D Q := by
  have hleft : finiteThreeMomentReferenceProjection Q *
      normalizedWeingartenWeightedErrorThree D Q =
      normalizedWeingartenWeightedErrorThree D Q := by
    change (((6 : ℂ)⁻¹ • ∑ sigma, Q sigma sigma) *
      normalizedWeingartenWeightedErrorThree D Q = _)
    rw [smul_mul_assoc, Finset.sum_mul]
    simp_rw [diagonalQ_mul_normalizedWeingartenWeightedErrorThree D Q hmul]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num [Fintype.card_perm, Nat.factorial]
  have hright : normalizedWeingartenWeightedErrorThree D Q *
      finiteThreeMomentReferenceProjection Q =
      normalizedWeingartenWeightedErrorThree D Q := by
    change (normalizedWeingartenWeightedErrorThree D Q *
      ((6 : ℂ)⁻¹ • ∑ sigma, Q sigma sigma) = _)
    rw [mul_smul_comm, Finset.mul_sum]
    simp_rw [normalizedWeingartenWeightedErrorThree_mul_diagonalQ D Q hmul]
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    norm_num [Fintype.card_perm, Nat.factorial]
  rw [hleft, hright]

theorem normalizedWeingartenWeightedErrorThree_isSelfAdjoint
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹) :
    IsSelfAdjoint (normalizedWeingartenWeightedErrorThree D Q) := by
  unfold IsSelfAdjoint normalizedWeingartenWeightedErrorThree
  rw [star_sum]
  simp_rw [star_sum, star_smul, hstar]
  simp only [Complex.star_def, Complex.conj_ofReal]
  calc
    (∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma tau : ℂ) •
          Q sigma⁻¹ tau⁻¹) =
      ∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma⁻¹ tau⁻¹ : ℂ) •
          Q sigma⁻¹ tau⁻¹ := by
            apply Fintype.sum_congr
            intro sigma
            apply Fintype.sum_congr
            intro tau
            rw [normalizedWeingartenDeltaThree_inv]
    _ = ∑ sigma, ∑ tau,
        (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau :=
      finThree_sum_sum_inv
        (fun sigma tau ↦
          (normalizedWeingartenDeltaThree D sigma tau : ℂ) • Q sigma tau)

theorem finiteThreeMomentApproximateHaarRawChoi_eq_flat
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ) :
    finiteThreeMomentApproximateHaarRawChoi D Q =
      ((6 * ((D : ℝ) ^ 3)⁻¹ : ℝ) : ℂ) •
        finiteThreeMomentReferenceProjection Q := by
  unfold finiteThreeMomentApproximateHaarRawChoi
    finiteThreeMomentReferenceProjection
  module

/-- B.21 from the literal Haar Weingarten Choi identity.  This theorem's
only analytic input is the concrete equality `hHaarChoi`; all norm and
support estimates are discharged above. -/
theorem relativeCPApproximation_haar_of_weingartenChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ) (hD : 18 ≤ D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹)
    (Haar Reference : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (hHaarChoi : finiteChoiMatrix Haar.toLinearMap =
      finiteThreeMomentWeingartenRawChoi D Q)
    (hReferenceChoi : finiteChoiMatrix Reference.toLinearMap =
      finiteThreeMomentApproximateHaarRawChoi D Q) :
    RelativeCPApproximation (9 / (2 * (D : ℝ) - 9))
      Haar.toLinearMap Reference.toLinearMap := by
  let epsilon : ℝ := 9 / (2 * (D : ℝ) - 9)
  let scale : ℝ := ((D : ℝ) ^ 3)⁻¹
  let c : ℝ := 6 * scale
  let P := finiteThreeMomentReferenceProjection Q
  have hDpos : 0 < D := by omega
  have hDr : (18 : ℝ) ≤ D := by exact_mod_cast hD
  have hden : 0 < 2 * (D : ℝ) - 9 := by linarith
  have hscale : 0 ≤ scale := by dsimp [scale]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hepsilon : 0 ≤ epsilon := by
    dsimp [epsilon]
    exact div_nonneg (by norm_num) hden.le
  have hPself : IsSelfAdjoint P :=
    finiteThreeMomentReferenceProjection_isSelfAdjoint Q hstar
  have hPid : P * P = P :=
    finiteThreeMomentReferenceProjection_isIdempotent Q hmul
  have hflat : finiteChoiMatrix Reference.toLinearMap = (c : ℂ) • P := by
    rw [hReferenceChoi, finiteThreeMomentApproximateHaarRawChoi_eq_flat]
  have herror : finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap) =
      (scale : ℂ) • normalizedWeingartenWeightedErrorThree D Q := by
    rw [finiteChoiMatrix_sub, hHaarChoi, hReferenceChoi,
      finiteThreeMomentWeingartenRawChoi_sub_approximateHaar]
  have herrorSelf : IsSelfAdjoint
      (finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap)) := by
    rw [herror]
    unfold IsSelfAdjoint
    rw [star_smul,
      (normalizedWeingartenWeightedErrorThree_isSelfAdjoint D Q hstar).star_eq]
    simp
  have herrorSupport :
      P * finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap) * P =
        finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap) := by
    rw [herror, mul_smul_comm, smul_mul_assoc,
      finiteThreeMomentReferenceProjection_weingartenError_support D Q hmul]
  have herrorNorm :
      ‖finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap)‖ ≤
        epsilon * c := by
    rw [herror]
    have hbound :=
      norm_scaled_normalizedWeingartenWeightedErrorThree_le D hD Q hQ
    simpa [epsilon, c, scale] using hbound
  exact relativeCPApproximation_of_finiteChoi_flatSupport_norm
    epsilon c Haar.toLinearMap Reference.toLinearMap P hepsilon hc hflat
    herrorSelf hPself hPid herrorSupport herrorNorm

/-- B.22 orientation, now relative to the actual Haar twirl. -/
theorem relativeCPApproximation_reference_of_weingartenChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ) (hD : 18 ≤ D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹)
    (Haar Reference : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (hHaarChoi : finiteChoiMatrix Haar.toLinearMap =
      finiteThreeMomentWeingartenRawChoi D Q)
    (hReferenceChoi : finiteChoiMatrix Reference.toLinearMap =
      finiteThreeMomentApproximateHaarRawChoi D Q) :
    RelativeCPApproximation (9 / (2 * (D : ℝ) - 18))
      Reference.toLinearMap Haar.toLinearMap := by
  let epsilon : ℝ := 9 / (2 * (D : ℝ) - 9)
  have hforward := relativeCPApproximation_haar_of_weingartenChoi
    D hD Q hQ hmul hstar Haar Reference hHaarChoi hReferenceChoi
  have hDr : (18 : ℝ) ≤ D := by exact_mod_cast hD
  have hden1 : 0 < 2 * (D : ℝ) - 9 := by linarith
  have hden2 : 0 < 2 * (D : ℝ) - 18 := by linarith
  have hepsilon0 : 0 ≤ epsilon := by
    dsimp [epsilon]
    exact div_nonneg (by norm_num) hden1.le
  have hepsilonHalf : epsilon ≤ 1 / 2 := by
    dsimp [epsilon]
    rw [div_le_iff₀ hden1]
    linarith
  have hreverse := relativeCPApproximation_reverse Haar Reference epsilon
    hepsilon0 hepsilonHalf hforward
  have heq : epsilon / (1 - epsilon) = 9 / (2 * (D : ℝ) - 18) := by
    dsimp [epsilon]
    have hsub : 1 - 9 / (2 * (D : ℝ) - 9) =
        (2 * (D : ℝ) - 18) / (2 * (D : ℝ) - 9) := by
      field_simp [hden1.ne']
      ring
    rw [hsub]
    field_simp [hden1.ne', hden2.ne']
  rw [← heq]
  exact hreverse

end

end TomographyOracleCore
