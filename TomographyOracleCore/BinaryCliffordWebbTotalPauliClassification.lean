import TomographyOracleCore.BinaryCliffordWebbIdentityPlacements

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Exhaustive Pauli-tensor classification for the finite Clifford third twirl

This module combines the three matrix cases in Webb's proof.  The input is
an arbitrary tensor of three Hermitian binary Paulis.  A nonzero label sum
is the Pauli-cancellation case.  When the sum is zero, an identity label is
handled by the exact second-moment formulas, and three nonidentity labels
reduce to the fixed-commutation pair-class formulas.
-/

/-- Tensor-cube conjugation is complex-linear in the third input. -/
theorem conjugatedMatrixTensorThree_smul_right
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) (c : ℂ)
    (A B C : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorThree K e A B (c • C) =
      c • conjugatedMatrixTensorThree K e A B C := by
  unfold conjugatedMatrixTensorThree
  rw [matrixTensorThree_smul_right, Matrix.mul_smul, Matrix.smul_mul]

/-- Tensor-cube conjugation pulls out the product of three complex scalars. -/
theorem conjugatedMatrixTensorThree_smul
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) (a b c : ℂ)
    (A B C : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorThree K e (a • A) (b • B) (c • C) =
      (a * b * c) • conjugatedMatrixTensorThree K e A B C := by
  unfold conjugatedMatrixTensorThree
  rw [matrixTensorThree_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- The Hermitian-Pauli third moment differs from the unphased-Pauli third
moment only by the product of the three fixed Hermitian phases. -/
theorem averagedHermitianPauliThirdMoment_eq_phase_smul_binary
    (K : ℕ) (p q r : PauliLabel K) :
    averagedHermitianPauliThirdMoment K p q r =
      (hermitianPauliPhase K p * hermitianPauliPhase K q *
          hermitianPauliPhase K r) •
        averagedPauliCosetThirdMoment K p q r := by
  unfold averagedHermitianPauliThirdMoment averagedPauliCosetThirdMoment
    hermitianBinaryPauliMatrix
  have hpoint (e : PauliCosetCliffordEnsemble K) :
      conjugatedMatrixTensorThree K e
          (hermitianPauliPhase K p • binaryPauliMatrix K p)
          (hermitianPauliPhase K q • binaryPauliMatrix K q)
          (hermitianPauliPhase K r • binaryPauliMatrix K r) =
        (hermitianPauliPhase K p * hermitianPauliPhase K q *
            hermitianPauliPhase K r) •
          conjugatedBinaryPauliTensorThree K e p q r := by
    rw [conjugatedMatrixTensorThree_smul]
    rfl
  simp_rw [hpoint]
  rw [← Finset.smul_sum, smul_smul]
  module

/-- Webb's Pauli-invariance case in the Hermitian Pauli basis. -/
theorem averagedHermitianPauliThirdMoment_eq_zero_of_sum_ne
    (K : ℕ) (p q r : PauliLabel K) (hsum : p + q + r ≠ 0) :
    averagedHermitianPauliThirdMoment K p q r = 0 := by
  rw [averagedHermitianPauliThirdMoment_eq_phase_smul_binary,
    averagedPauliCosetThirdMoment_eq_zero K p q r hsum, smul_zero]

/-- Webb's product tensor is the ordinary Hermitian Pauli tensor at the sum
label, multiplied by the explicit Pauli product phase. -/
theorem averagedHermitianPauliProductThirdMoment_eq_phase_smul
    (K : ℕ) (p q : PauliLabel K) :
    averagedHermitianPauliProductThirdMoment K p q =
      hermitianPauliProductPhase K p q •
        averagedHermitianPauliThirdMoment K p q (p + q) := by
  unfold averagedHermitianPauliProductThirdMoment
    conjugatedHermitianPauliProductTensorThree
    averagedHermitianPauliThirdMoment
  rw [hermitianBinaryPauliMatrix_mul]
  simp_rw [conjugatedMatrixTensorThree_smul_right]
  rw [← Finset.smul_sum, smul_smul]
  module

/-- Inverse form of the product-phase reduction. -/
theorem averagedHermitianPauliThirdMoment_sum_eq_phase_inv_smul
    (K : ℕ) (p q : PauliLabel K) :
    averagedHermitianPauliThirdMoment K p q (p + q) =
      (hermitianPauliProductPhase K p q)⁻¹ •
        averagedHermitianPauliProductThirdMoment K p q := by
  rw [averagedHermitianPauliProductThirdMoment_eq_phase_smul]
  rw [smul_smul, inv_mul_cancel₀ (hermitianPauliProductPhase_ne_zero K p q),
    one_smul]

/-- Explicit six-permutation formula for every Hermitian Pauli tensor. -/
noncomputable def webbHermitianPauliThirdMomentFormula
    (K : ℕ) (p q r : PauliLabel K) : ThirdM K :=
  if p + q + r ≠ 0 then 0
  else if p = 0 then
    if q = 0 then 1
    else
      ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
        (((2 : ℂ) ^ K) • registerSwap23 K - 1)
  else if q = 0 then
    ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
      (((2 : ℂ) ^ K) • registerSwap13 K - 1)
  else if r = 0 then
    ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
      (((2 : ℂ) ^ K) • registerSwap12 K - 1)
  else if pauliSymplecticForm K p q = 0 then
    (hermitianPauliProductPhase K p q)⁻¹ •
      (((Fintype.card (PauliPairClass K 0) : ℂ)⁻¹) •
        (((((2 : ℂ) ^ K) ^ 2) / 2) •
              (registerCycle123 K + registerCycle132 K) -
            ((2 : ℂ) ^ K) •
              (registerSwap12 K + registerSwap23 K + registerSwap13 K) +
            (2 : ℂ) • (1 : ThirdM K)))
  else
    (hermitianPauliProductPhase K p q)⁻¹ •
      (((Fintype.card (PauliPairClass K 1) : ℂ)⁻¹) •
        (((((2 : ℂ) ^ K) ^ 2) / 2) •
          (registerCycle123 K - registerCycle132 K)))

/-- The standard six-permutation subspace on three tensor registers. -/
noncomputable def webbPermutationSubmodule (K : ℕ) : Submodule ℂ (ThirdM K) :=
  Submodule.span ℂ
    ({(1 : ThirdM K), registerSwap12 K, registerSwap23 K,
        registerSwap13 K, registerCycle123 K, registerCycle132 K} :
      Set (ThirdM K))

theorem one_mem_webbPermutationSubmodule (K : ℕ) :
    (1 : ThirdM K) ∈ webbPermutationSubmodule K := by
  unfold webbPermutationSubmodule
  apply Submodule.subset_span
  simp

theorem swap12_mem_webbPermutationSubmodule (K : ℕ) :
    registerSwap12 K ∈ webbPermutationSubmodule K := by
  unfold webbPermutationSubmodule
  apply Submodule.subset_span
  simp

theorem swap23_mem_webbPermutationSubmodule (K : ℕ) :
    registerSwap23 K ∈ webbPermutationSubmodule K := by
  unfold webbPermutationSubmodule
  apply Submodule.subset_span
  simp

theorem swap13_mem_webbPermutationSubmodule (K : ℕ) :
    registerSwap13 K ∈ webbPermutationSubmodule K := by
  unfold webbPermutationSubmodule
  apply Submodule.subset_span
  simp

theorem cycle123_mem_webbPermutationSubmodule (K : ℕ) :
    registerCycle123 K ∈ webbPermutationSubmodule K := by
  unfold webbPermutationSubmodule
  apply Submodule.subset_span
  simp

theorem cycle132_mem_webbPermutationSubmodule (K : ℕ) :
    registerCycle132 K ∈ webbPermutationSubmodule K := by
  unfold webbPermutationSubmodule
  apply Submodule.subset_span
  simp

/-- Every value of the exhaustive Webb formula belongs to the span of the six
register-permutation matrices. -/
theorem webbHermitianPauliThirdMomentFormula_mem_permutationSubmodule
    (K : ℕ) (p q r : PauliLabel K) :
    webbHermitianPauliThirdMomentFormula K p q r ∈
      webbPermutationSubmodule K := by
  classical
  have hI := one_mem_webbPermutationSubmodule K
  have h12 := swap12_mem_webbPermutationSubmodule K
  have h23 := swap23_mem_webbPermutationSubmodule K
  have h13 := swap13_mem_webbPermutationSubmodule K
  have h123 := cycle123_mem_webbPermutationSubmodule K
  have h132 := cycle132_mem_webbPermutationSubmodule K
  unfold webbHermitianPauliThirdMomentFormula
  split_ifs
  · exact Submodule.zero_mem _
  · exact hI
  · exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ h23) hI)
  · exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ h13) hI)
  · exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.smul_mem _ _ h12) hI)
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.add_mem _
        (Submodule.sub_mem _
          (Submodule.smul_mem _ _ (Submodule.add_mem _ h123 h132))
          (Submodule.smul_mem _ _
            (Submodule.add_mem _ (Submodule.add_mem _ h12 h23) h13)))
        (Submodule.smul_mem _ _ hI)))
  · exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ h123 h132)))

/-- Exhaustive Webb case split: the concrete finite third twirl of every
Hermitian Pauli tensor is the displayed combination of the six register
permutations. -/
theorem averagedHermitianPauliThirdMoment_eq_webbFormula
    (K : ℕ) (p q r : PauliLabel K) :
    averagedHermitianPauliThirdMoment K p q r =
      webbHermitianPauliThirdMomentFormula K p q r := by
  classical
  by_cases hsum : p + q + r ≠ 0
  · rw [averagedHermitianPauliThirdMoment_eq_zero_of_sum_ne K p q r hsum]
    simp [webbHermitianPauliThirdMomentFormula, hsum]
  · have hsum0 : p + q + r = 0 := not_ne_iff.mp hsum
    by_cases hp : p = 0
    · subst p
      by_cases hq : q = 0
      · subst q
        have hr : r = 0 := by simpa using hsum0
        subst r
        rw [averagedHermitianPauliThirdMoment_zero_zero_zero]
        simp [webbHermitianPauliThirdMomentFormula]
      · have hrq : r = q := by
          have hqr : q + r = 0 := by simpa using hsum0
          calc
            r = 0 + r := by simp
            _ = (q + q) + r := by rw [pauliLabel_add_self]
            _ = q + (q + r) := by abel
            _ = q := by rw [hqr, add_zero]
        subst r
        rw [averagedHermitianPauliThirdMoment_zero_same_eq_swap23
          K (⟨q, hq⟩ : NonidentityPauliLabel K)]
        simp [webbHermitianPauliThirdMomentFormula, hq,
          pauliLabel_add_self]
    · by_cases hq : q = 0
      · subst q
        have hrp : r = p := by
          have hpr : p + r = 0 := by simpa using hsum0
          calc
            r = 0 + r := by simp
            _ = (p + p) + r := by rw [pauliLabel_add_self]
            _ = p + (p + r) := by abel
            _ = p := by rw [hpr, add_zero]
        subst r
        rw [averagedHermitianPauliThirdMoment_same_zero_eq_swap13
          K (⟨p, hp⟩ : NonidentityPauliLabel K)]
        simp [webbHermitianPauliThirdMomentFormula, hp,
          pauliLabel_add_self]
      · by_cases hr : r = 0
        · subst r
          have hpqeq : p = q := by
            have hpq0 : p + q = 0 := by simpa using hsum0
            calc
              p = p + 0 := by simp
              _ = p + (p + q) := by rw [hpq0]
              _ = (p + p) + q := by abel
              _ = q := by rw [pauliLabel_add_self, zero_add]
          subst q
          rw [averagedHermitianPauliThirdMoment_same_zero_eq_swap12
            K (⟨p, hp⟩ : NonidentityPauliLabel K)]
          simp [webbHermitianPauliThirdMomentFormula, hp,
            pauliLabel_add_self]
        · have hrpq : r = p + q := by
            calc
              r = 0 + r := by simp
              _ = (p + q + r) + r := by rw [hsum0]
              _ = p + q + (r + r) := by abel
              _ = p + q := by rw [pauliLabel_add_self, add_zero]
          have hpq : p ≠ q := by
            intro hpqeq
            apply hr
            rw [hrpq, hpqeq, pauliLabel_add_self]
          subst r
          rw [averagedHermitianPauliThirdMoment_sum_eq_phase_inv_smul]
          have htot : ¬ (p + q + (p + q) ≠ 0) := by
            simp [pauliLabel_add_self]
          by_cases hc : pauliSymplecticForm K p q = 0
          · let x : PauliPairClass K 0 :=
              ⟨(p, q), hp, hq, hpq, hc⟩
            rw [averagedHermitianPauliProductThirdMoment_commuting_eq K x]
            unfold webbHermitianPauliThirdMomentFormula
            rw [if_neg htot, if_neg hp, if_neg hq, if_neg hr, if_pos hc]
          · have hc1 : pauliSymplecticForm K p q = 1 := by
              rcases zmodTwo_eq_zero_or_one (pauliSymplecticForm K p q) with
                hc0 | hc1
              · exact (hc hc0).elim
              · exact hc1
            let x : PauliPairClass K 1 :=
              ⟨(p, q), hp, hq, hpq, hc1⟩
            rw [averagedHermitianPauliProductThirdMoment_anticommuting_eq K x]
            unfold webbHermitianPauliThirdMomentFormula
            rw [if_neg htot, if_neg hp, if_neg hq, if_neg hr, if_neg hc]

/-- The concrete finite Clifford third twirl of every Hermitian Pauli tensor
belongs to the six-permutation subspace. -/
theorem averagedHermitianPauliThirdMoment_mem_webbPermutationSubmodule
    (K : ℕ) (p q r : PauliLabel K) :
    averagedHermitianPauliThirdMoment K p q r ∈
      webbPermutationSubmodule K := by
  rw [averagedHermitianPauliThirdMoment_eq_webbFormula]
  exact webbHermitianPauliThirdMomentFormula_mem_permutationSubmodule K p q r

end TomographyOracleCore
