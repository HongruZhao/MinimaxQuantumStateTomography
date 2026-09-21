import TomographyOracleCore.Revision.FinitePrecisionRoundingDefinitions
import TomographyOracleCore.Revision.FinitePrecisionRationalProjection
import TomographyOracleCore.Revision.FinitePrecisionRepair

/-! Certified fixed-precision rounding of actual rational density matrices.
The constructed output is exactly PSD and trace one, and the denominator
used in its rational normalization is proved positive. -/

namespace TomographyOracleCore.Revision.FinitePrecision

open AlgorithmResources MatrixReduction MatrixSolver Candidate2FeasibilityRepair Matrix
open scoped ComplexOrder InnerProductSpace BigOperators

noncomputable section
set_option maxHeartbeats 1000000

variable {D : ℕ}

@[simp] theorem castQMatrix_conjTranspose (A : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix A.conjTranspose = (castQMatrix A).conjTranspose := by
  ext i j
  exact qComplexToComplex_star (A j i)

@[simp] theorem castQMatrix_one :
    castQMatrix (1 : Matrix (Fin D) (Fin D) QComplex) = 1 := by
  ext i j
  by_cases hij : i = j
  · simpa only [castQMatrix_apply, Matrix.one_apply, if_pos hij] using map_one qComplexToComplex
  · simpa only [castQMatrix_apply, Matrix.one_apply, if_neg hij] using map_zero qComplexToComplex

theorem cast_qHermitianRound (s : ℕ) (A : Matrix (Fin D) (Fin D) QComplex) :
    castQMatrix (qHermitianRound s A) =
      (1 / 2 : ℝ) • (castQMatrix (qRoundRawMatrix s A) +
        (castQMatrix (qRoundRawMatrix s A)).conjTranspose) := by
  rw [qHermitianRound, castQMatrix_rat_smul, castQMatrix_add, castQMatrix_conjTranspose]
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

theorem qHermitianRound_isHermitian (s : ℕ) (A : Matrix (Fin D) (Fin D) QComplex) :
    (castQMatrix (qHermitianRound s A)).IsHermitian := by
  rw [cast_qHermitianRound]
  change ((1 / 2 : ℝ) • (castQMatrix (qRoundRawMatrix s A) +
    (castQMatrix (qRoundRawMatrix s A)).conjTranspose)).conjTranspose = _
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  simp only [star_trivial]
  rw [add_comm]

theorem qRoundEntry_error (s : ℕ) (z : QComplex) :
    ‖qComplexToComplex (qRoundEntry s z) - qComplexToComplex z‖ ≤ 2 / (2 : ℝ) ^ s := by
  have hre := dyadicRound_real_error s z.re
  have him := dyadicRound_real_error s z.im
  have hnorm := Complex.norm_le_abs_re_add_abs_im
    (qComplexToComplex (qRoundEntry s z) - qComplexToComplex z)
  simp only [Complex.sub_re, Complex.sub_im, qComplexToComplex_re,
    qComplexToComplex_im, qRoundEntry] at hnorm
  rw [abs_sub_comm (dyadicRound s z.re : ℝ), abs_sub_comm (dyadicRound s z.im : ℝ)] at hnorm
  dsimp only [qRoundEntry]
  calc
    _ ≤ |(z.re : ℝ) - (dyadicRound s z.re : ℝ)| +
        |(z.im : ℝ) - (dyadicRound s z.im : ℝ)| := hnorm
    _ ≤ 1 / (2 : ℝ) ^ s + 1 / (2 : ℝ) ^ s := add_le_add hre.le him.le
    _ = 2 / (2 : ℝ) ^ s := by ring

theorem qHermitianRound_entry_error
    (s : ℕ) (A : Matrix (Fin D) (Fin D) QComplex) (hA : (castQMatrix A).IsHermitian)
    (i j : Fin D) :
    ‖castQMatrix (qHermitianRound s A) i j - castQMatrix A i j‖ ≤ 2 / (2 : ℝ) ^ s := by
  let B := castQMatrix (qRoundRawMatrix s A)
  let C := castQMatrix A
  have hraw (a b : Fin D) : ‖B a b - C a b‖ ≤ 2 / (2 : ℝ) ^ s :=
    qRoundEntry_error s (A a b)
  have hsym : star (C j i) = C i j := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M i j) hA.eq
  have hid : castQMatrix (qHermitianRound s A) i j - C i j =
      (1 / 2 : ℝ) • ((B i j - C i j) + star (B j i - C j i)) := by
    rw [cast_qHermitianRound]
    change (1 / 2 : ℝ) • (B i j + star (B j i)) - C i j = _
    rw [star_sub, hsym]
    simp [Complex.real_smul]
    ring
  change ‖castQMatrix (qHermitianRound s A) i j - C i j‖ ≤ _
  rw [hid, norm_smul]
  have htri := norm_add_le (B i j - C i j) (star (B j i - C j i))
  rw [norm_star] at htri
  norm_num only [Real.norm_eq_abs] at *
  nlinarith [hraw i j, hraw j i]

theorem qHermitianRound_entryNormSum_error
    (s : ℕ) (A : Matrix (Fin D) (Fin D) QComplex) (hA : (castQMatrix A).IsHermitian) :
    entryNormSum (castQMatrix (qHermitianRound s A) - castQMatrix A) ≤
      (qRoundingEta D s : ℝ) := by
  calc
    entryNormSum (castQMatrix (qHermitianRound s A) - castQMatrix A) ≤
        ∑ i : Fin D, ∑ j : Fin D, 2 / (2 : ℝ) ^ s := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact qHermitianRound_entry_error s A hA i j
    _ = (qRoundingEta D s : ℝ) := by
      simp [qRoundingEta]
      ring

theorem qRoundingEta_nonneg (D s : ℕ) : (0 : ℝ) ≤ qRoundingEta D s := by
  unfold qRoundingEta
  push_cast
  positivity

theorem qRepairDenominator_cast
    (H : Matrix (Fin D) (Fin D) QComplex) (eta : ℚ) :
    (qRepairDenominator H eta : ℝ) = repairDenominator (castQMatrix H) (eta : ℝ) := by
  simp only [qRepairDenominator, repairDenominator, Rat.cast_add, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast, Fintype.card_fin, Matrix.trace,
    Matrix.diag_apply, Complex.re_sum, castQMatrix_apply, qComplexToComplex_re]

theorem cast_qShiftNormalize
    (H : Matrix (Fin D) (Fin D) QComplex) (eta : ℚ) :
    castQMatrix (qShiftNormalize H eta) = repairedMatrix (castQMatrix H) (eta : ℝ) := by
  rw [qShiftNormalize, castQMatrix_rat_smul, castQMatrix_add, castQMatrix_rat_smul,
    castQMatrix_one, Rat.cast_inv, qRepairDenominator_cast]
  rfl

/-- The normalization denominator is uniformly bounded away from zero on
the actual inputs to fixed-precision density rounding. -/
theorem qRoundDensity_denominator_ge_one
    (hD : 0 < D) (s : ℕ) (A : Matrix (Fin D) (Fin D) QComplex)
    (hA : (castQMatrix A).PosSemidef) (htrace : (castQMatrix A).trace = 1) :
    (1 : ℚ) ≤ qRepairDenominator (qHermitianRound s A) (qRoundingEta D s) := by
  let rho : DensityOperator (Fin D) := ⟨castQMatrix A, hA, htrace⟩
  have h := repairDenominator_ge_one_of_entrywise_error hD rho
    (castQMatrix (qHermitianRound s A)) (qRoundingEta D s)
    (qRoundingEta_nonneg D s) (qHermitianRound_entryNormSum_error s A hA.isHermitian)
  rw [← qRepairDenominator_cast] at h
  exact_mod_cast h

/-- The implemented fixed-precision map preserves density-matrix
feasibility exactly and approximates its input at an explicit dyadic rate. -/
theorem qRoundDensity_correct
    (hD : 0 < D) (s : ℕ) (A : Matrix (Fin D) (Fin D) QComplex)
    (hA : (castQMatrix A).PosSemidef) (htrace : (castQMatrix A).trace = 1) :
    (castQMatrix (qRoundDensity s A)).PosSemidef ∧
      (castQMatrix (qRoundDensity s A)).trace = 1 ∧
      ‖encode (castQMatrix (qRoundDensity s A) - castQMatrix A)‖ ≤
        (2 * (D : ℝ) + 2) * (qRoundingEta D s : ℝ) := by
  let rho : DensityOperator (Fin D) := ⟨castQMatrix A, hA, htrace⟩
  rw [qRoundDensity, cast_qShiftNormalize]
  exact repair_from_entrywise_error hD rho (castQMatrix (qHermitianRound s A))
    (qHermitianRound_isHermitian s A) (qRoundingEta D s)
    (qRoundingEta_nonneg D s) (qHermitianRound_entryNormSum_error s A hA.isHermitian)

end

end TomographyOracleCore.Revision.FinitePrecision
