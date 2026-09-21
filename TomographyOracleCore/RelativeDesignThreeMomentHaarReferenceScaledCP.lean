import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceRelativeCP

namespace TomographyOracleCore

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator

noncomputable section

local instance scaledHaarReferenceSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance scaledHaarReferenceStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Common positive scaling of the B.21--B.23 Choi formulas

This is the exact form needed after tensoring a local Haar/reference pair
with an untouched-register identity map: the untouched EPR factor supplies
one common positive scalar to both Choi matrices.
-/

/-- B.21 is unchanged when both literal Choi formulas carry the same
nonnegative real scalar. -/
theorem relativeCPApproximation_haar_of_scaled_weingartenChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ) (hD : 18 ≤ D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹)
    (s : ℝ) (hs : 0 ≤ s)
    (Haar Reference : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (hHaarChoi : finiteChoiMatrix Haar.toLinearMap =
      (s : ℂ) • finiteThreeMomentWeingartenRawChoi D Q)
    (hReferenceChoi : finiteChoiMatrix Reference.toLinearMap =
      (s : ℂ) • finiteThreeMomentApproximateHaarRawChoi D Q) :
    RelativeCPApproximation (9 / (2 * (D : ℝ) - 9))
      Haar.toLinearMap Reference.toLinearMap := by
  let epsilon : ℝ := 9 / (2 * (D : ℝ) - 9)
  let scale : ℝ := ((D : ℝ) ^ 3)⁻¹
  let c : ℝ := s * (6 * scale)
  let P := finiteThreeMomentReferenceProjection Q
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
    rw [hReferenceChoi, finiteThreeMomentApproximateHaarRawChoi_eq_flat,
      smul_smul]
    congr 1
    dsimp [c, scale]
    push_cast
    ring
  have herror : finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap) =
      (s : ℂ) • (((scale : ℝ) : ℂ) •
        normalizedWeingartenWeightedErrorThree D Q) := by
    rw [finiteChoiMatrix_sub, hHaarChoi, hReferenceChoi, ← smul_sub,
      finiteThreeMomentWeingartenRawChoi_sub_approximateHaar]
  have herrorSelf : IsSelfAdjoint
      (finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap)) := by
    rw [herror]
    unfold IsSelfAdjoint
    rw [star_smul, star_smul,
      (normalizedWeingartenWeightedErrorThree_isSelfAdjoint D Q hstar).star_eq]
    simp
  have herrorSupport :
      P * finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap) * P =
        finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap) := by
    rw [herror, mul_smul_comm, mul_smul_comm, smul_mul_assoc,
      smul_mul_assoc,
      finiteThreeMomentReferenceProjection_weingartenError_support D Q hmul]
  have herrorNorm :
      ‖finiteChoiMatrix (Haar.toLinearMap - Reference.toLinearMap)‖ ≤
        epsilon * c := by
    rw [herror, norm_smul]
    have hsNorm : ‖(s : ℂ)‖ = s := by
      simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]
    rw [hsNorm]
    calc
      s * ‖(((scale : ℝ) : ℂ) •
          normalizedWeingartenWeightedErrorThree D Q)‖ ≤
        s * ((9 / (2 * (D : ℝ) - 9)) *
          (6 * ((D : ℝ) ^ 3)⁻¹)) :=
        mul_le_mul_of_nonneg_left
          (norm_scaled_normalizedWeingartenWeightedErrorThree_le D hD Q hQ) hs
      _ = epsilon * c := by dsimp [epsilon, c, scale]; ring
  exact relativeCPApproximation_of_finiteChoi_flatSupport_norm
    epsilon c Haar.toLinearMap Reference.toLinearMap P hepsilon hc hflat
    herrorSelf hPself hPid herrorSupport herrorNorm

/-- B.22 in the reverse orientation, with the same common Choi scaling. -/
theorem relativeCPApproximation_reference_of_scaled_weingartenChoi
    {I : Type*} [Fintype I] [DecidableEq I]
    (D : ℕ) (hD : 18 ≤ D)
    (Q : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3) →
      CStarMatrix (I × I) (I × I) ℂ)
    (hQ : ∀ sigma tau, ‖Q sigma tau‖ ≤ 1)
    (hmul : ∀ sigma tau sigma' tau',
      Q sigma tau * Q sigma' tau' = Q (sigma * sigma') (tau * tau'))
    (hstar : ∀ sigma tau, star (Q sigma tau) = Q sigma⁻¹ tau⁻¹)
    (s : ℝ) (hs : 0 ≤ s)
    (Haar Reference : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (hHaarChoi : finiteChoiMatrix Haar.toLinearMap =
      (s : ℂ) • finiteThreeMomentWeingartenRawChoi D Q)
    (hReferenceChoi : finiteChoiMatrix Reference.toLinearMap =
      (s : ℂ) • finiteThreeMomentApproximateHaarRawChoi D Q) :
    RelativeCPApproximation (9 / (2 * (D : ℝ) - 18))
      Reference.toLinearMap Haar.toLinearMap := by
  let epsilon : ℝ := 9 / (2 * (D : ℝ) - 9)
  have hforward := relativeCPApproximation_haar_of_scaled_weingartenChoi
    D hD Q hQ hmul hstar s hs Haar Reference hHaarChoi hReferenceChoi
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
