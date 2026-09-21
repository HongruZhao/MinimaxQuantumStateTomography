import TomographyOracleCore.BinaryPauliTensorPermutations

namespace TomographyOracleCore
open scoped BigOperators

abbrev ThirdM (K : ℕ) := Matrix (TripleIndex (PauliBinaryWord K))
  (TripleIndex (PauliBinaryWord K)) ℂ

noncomputable def reverseHermitianPauliProductTensorThree
    (K : ℕ) (p q : PauliLabel K) : ThirdM K :=
  matrixTensorThree (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)
    (hermitianBinaryPauliMatrix K q * hermitianBinaryPauliMatrix K p)

theorem hermitianBinaryPauliMatrix_mul_swap_full
    (K : ℕ) (p q : PauliLabel K) :
    hermitianBinaryPauliMatrix K q * hermitianBinaryPauliMatrix K p =
      (pauliCharacter K p q : ℂ) •
        (hermitianBinaryPauliMatrix K p * hermitianBinaryPauliMatrix K q) := by
  change hermitianBinaryPauliMatrix K q *
      (hermitianPauliPhase K p • binaryPauliMatrix K p) =
    (pauliCharacter K p q : ℂ) •
      ((hermitianPauliPhase K p • binaryPauliMatrix K p) *
        hermitianBinaryPauliMatrix K q)
  rw [Matrix.mul_smul, Matrix.smul_mul,
    hermitianBinaryPauliMatrix_mul_swap, smul_smul, smul_smul,
    pauliCharacter_comm]
  rw [mul_comm]

theorem matrixTensorThree_smul_right {ι : Type*}
    (a : ℂ) (A B C : Matrix ι ι ℂ) :
    matrixTensorThree A B (a • C) = a • matrixTensorThree A B C := by
  ext x y
  simp [matrixTensorThree]
  ring

theorem reverse_eq_character
    (K : ℕ) (p q : PauliLabel K) :
    reverseHermitianPauliProductTensorThree K p q =
      (pauliCharacter K p q : ℂ) •
        hermitianPauliProductTensorThree K p q := by
  unfold reverseHermitianPauliProductTensorThree
    hermitianPauliProductTensorThree
  rw [hermitianBinaryPauliMatrix_mul_swap_full,
    matrixTensorThree_smul_right]

noncomputable def hermitianPauliProductCommutationSum
    (K : ℕ) (c : ZMod 2) : ThirdM K :=
  ∑ p : PauliLabel K, ∑ q : PauliLabel K,
    if pauliSymplecticForm K p q = c then
      hermitianPauliProductTensorThree K p q else 0

theorem commutationSum_zero_eq_half_cycles (K : ℕ) :
    hermitianPauliProductCommutationSum K 0 =
      (1 / 2 : ℂ) •
        ((∑ p : PauliLabel K, ∑ q : PauliLabel K,
          hermitianPauliProductTensorThree K p q) +
        (∑ p : PauliLabel K, ∑ q : PauliLabel K,
          reverseHermitianPauliProductTensorThree K p q)) := by
  classical
  unfold hermitianPauliProductCommutationSum
  have hpoint (p q : PauliLabel K) :
      (if pauliSymplecticForm K p q = 0 then
          hermitianPauliProductTensorThree K p q else 0) =
        (1 / 2 : ℂ) •
          (hermitianPauliProductTensorThree K p q +
            reverseHermitianPauliProductTensorThree K p q) := by
    rw [reverse_eq_character]
    rcases zmodTwo_eq_zero_or_one (pauliSymplecticForm K p q) with h | h
    · simp [h, pauliCharacter]
      module
    · simp [h, pauliCharacter]
  calc
    (∑ p : PauliLabel K, ∑ q : PauliLabel K,
        if pauliSymplecticForm K p q = 0 then
          hermitianPauliProductTensorThree K p q else 0) =
        ∑ p : PauliLabel K, ∑ q : PauliLabel K,
          (1 / 2 : ℂ) •
            (hermitianPauliProductTensorThree K p q +
              reverseHermitianPauliProductTensorThree K p q) := by
      apply Fintype.sum_congr
      intro p
      apply Fintype.sum_congr
      exact hpoint p
    _ = (1 / 2 : ℂ) •
        (∑ p : PauliLabel K, ∑ q : PauliLabel K,
          (hermitianPauliProductTensorThree K p q +
            reverseHermitianPauliProductTensorThree K p q)) := by
      conv_lhs =>
        enter [2, p]
        rw [← Finset.smul_sum]
      rw [← Finset.smul_sum]
    _ = _ := by simp_rw [Finset.sum_add_distrib]

theorem commutationSum_one_eq_half_cycles (K : ℕ) :
    hermitianPauliProductCommutationSum K 1 =
      (1 / 2 : ℂ) •
        ((∑ p : PauliLabel K, ∑ q : PauliLabel K,
          hermitianPauliProductTensorThree K p q) -
        (∑ p : PauliLabel K, ∑ q : PauliLabel K,
          reverseHermitianPauliProductTensorThree K p q)) := by
  classical
  unfold hermitianPauliProductCommutationSum
  have hpoint (p q : PauliLabel K) :
      (if pauliSymplecticForm K p q = 1 then
          hermitianPauliProductTensorThree K p q else 0) =
        (1 / 2 : ℂ) •
          (hermitianPauliProductTensorThree K p q -
            reverseHermitianPauliProductTensorThree K p q) := by
    rw [reverse_eq_character]
    rcases zmodTwo_eq_zero_or_one (pauliSymplecticForm K p q) with h | h
    · simp [h, pauliCharacter]
    · simp [h, pauliCharacter]
      module
  calc
    (∑ p : PauliLabel K, ∑ q : PauliLabel K,
        if pauliSymplecticForm K p q = 1 then
          hermitianPauliProductTensorThree K p q else 0) =
        ∑ p : PauliLabel K, ∑ q : PauliLabel K,
          (1 / 2 : ℂ) •
            (hermitianPauliProductTensorThree K p q -
              reverseHermitianPauliProductTensorThree K p q) := by
      apply Fintype.sum_congr
      intro p
      apply Fintype.sum_congr
      exact hpoint p
    _ = (1 / 2 : ℂ) •
        (∑ p : PauliLabel K, ∑ q : PauliLabel K,
          (hermitianPauliProductTensorThree K p q -
            reverseHermitianPauliProductTensorThree K p q)) := by
      conv_lhs =>
        enter [2, p]
        rw [← Finset.smul_sum]
      rw [← Finset.smul_sum]
    _ = _ := by simp_rw [Finset.sum_sub_distrib]

theorem commutationSum_zero_eq_permutations (K : ℕ) :
    hermitianPauliProductCommutationSum K 0 =
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
        (registerCycle123 K + registerCycle132 K) := by
  have hf : (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      hermitianPauliProductTensorThree K p q) =
      (((2 : ℂ) ^ K) ^ 2) • registerCycle123 K := by
    simpa [hermitianPauliProductTensorThree] using
      sum_hermitianPauli_cycle123 K
  have hr : (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      reverseHermitianPauliProductTensorThree K p q) =
      (((2 : ℂ) ^ K) ^ 2) • registerCycle132 K := by
    simpa [reverseHermitianPauliProductTensorThree] using
      sum_hermitianPauli_cycle132 K
  rw [commutationSum_zero_eq_half_cycles, hf, hr]
  module

theorem commutationSum_one_eq_permutations (K : ℕ) :
    hermitianPauliProductCommutationSum K 1 =
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
        (registerCycle123 K - registerCycle132 K) := by
  have hf : (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      hermitianPauliProductTensorThree K p q) =
      (((2 : ℂ) ^ K) ^ 2) • registerCycle123 K := by
    simpa [hermitianPauliProductTensorThree] using
      sum_hermitianPauli_cycle123 K
  have hr : (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      reverseHermitianPauliProductTensorThree K p q) =
      (((2 : ℂ) ^ K) ^ 2) • registerCycle132 K := by
    simpa [reverseHermitianPauliProductTensorThree] using
      sum_hermitianPauli_cycle132 K
  rw [commutationSum_one_eq_half_cycles, hf, hr]
  module

noncomputable def hermitianPauliProductPairClassIndicatorSum
    (K : ℕ) (c : ZMod 2) : ThirdM K :=
  ∑ p : PauliLabel K, ∑ q : PauliLabel K,
    if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧ pauliSymplecticForm K p q = c then
      hermitianPauliProductTensorThree K p q else 0

theorem pairClassIndicatorSum_one_eq_commutationSum (K : ℕ) :
    hermitianPauliProductPairClassIndicatorSum K 1 =
      hermitianPauliProductCommutationSum K 1 := by
  classical
  unfold hermitianPauliProductPairClassIndicatorSum
    hermitianPauliProductCommutationSum
  apply Fintype.sum_congr
  intro p
  apply Fintype.sum_congr
  intro q
  by_cases hform : pauliSymplecticForm K p q = 1
  · have hp : p ≠ 0 := by
      intro hp
      subst p
      simp at hform
    have hq : q ≠ 0 := by
      intro hq
      subst q
      simp at hform
    have hpq : p ≠ q := by
      intro hpq
      subst q
      rw [pauliSymplecticForm_self] at hform
      norm_num at hform
    simp [hform, hp, hq, hpq]
  · rw [if_neg hform]
    rw [if_neg]
    intro h
    exact hform h.2.2.2

theorem commutation_zero_pointwise_inclusion_exclusion
    (K : ℕ) (p q : PauliLabel K) :
    (if pauliSymplecticForm K p q = 0 then
        hermitianPauliProductTensorThree K p q else 0) =
      (if p ≠ 0 ∧ q ≠ 0 ∧ p ≠ q ∧
          pauliSymplecticForm K p q = 0 then
        hermitianPauliProductTensorThree K p q else 0) +
      (if p = 0 then hermitianPauliProductTensorThree K p q else 0) +
      (if q = 0 then hermitianPauliProductTensorThree K p q else 0) +
      (if p = q then hermitianPauliProductTensorThree K p q else 0) -
      (2 : ℕ) •
        (if p = 0 ∧ q = 0 then
          hermitianPauliProductTensorThree K p q else 0) := by
  classical
  by_cases hform : pauliSymplecticForm K p q = 0
  · rw [if_pos hform]
    by_cases hp : p = 0
    · subst p
      by_cases hq : q = 0
      · subst q
        simp
        noncomm_ring
      · have hq' : ¬(0 : PauliLabel K) = q := Ne.symm hq
        simp [hq, hq']
    · by_cases hq : q = 0
      · subst q
        simp [hp]
      · by_cases hpq : p = q
        · subst q
          simp [hp, hform]
        · simp [hp, hq, hpq, hform]
  · rw [if_neg hform]
    have hp : p ≠ 0 := by
      intro hp
      subst p
      apply hform
      simp
    have hq : q ≠ 0 := by
      intro hq
      subst q
      apply hform
      simp
    have hpq : p ≠ q := by
      intro hpq
      subst q
      apply hform
      exact pauliSymplecticForm_self K p
    rw [if_neg]
    · simp [hp, hq, hpq]
    · intro h
      exact hform h.2.2.2

theorem commutationSum_zero_eq_indicator_add_degenerate (K : ℕ) :
    hermitianPauliProductCommutationSum K 0 =
      hermitianPauliProductPairClassIndicatorSum K 0 +
      (∑ q : PauliLabel K, hermitianPauliProductTensorThree K 0 q) +
      (∑ p : PauliLabel K, hermitianPauliProductTensorThree K p 0) +
      (∑ p : PauliLabel K, hermitianPauliProductTensorThree K p p) -
      (2 : ℕ) • hermitianPauliProductTensorThree K 0 0 := by
  classical
  unfold hermitianPauliProductCommutationSum
    hermitianPauliProductPairClassIndicatorSum
  simp_rw [commutation_zero_pointwise_inclusion_exclusion]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp
  rw [Finset.sum_eq_single 0]
  · simp
  · intro x hx hne
    simp [hne]
  · simp

theorem sum_hermitianPauliProduct_zero_left (K : ℕ) :
    (∑ q : PauliLabel K, hermitianPauliProductTensorThree K 0 q) =
      ((2 : ℂ) ^ K) • registerSwap23 K := by
  simpa [hermitianPauliProductTensorThree,
    hermitianBinaryPauliMatrix_zero] using sum_hermitianPauli_swap23 K

theorem sum_hermitianPauliProduct_zero_right (K : ℕ) :
    (∑ p : PauliLabel K, hermitianPauliProductTensorThree K p 0) =
      ((2 : ℂ) ^ K) • registerSwap13 K := by
  simpa [hermitianPauliProductTensorThree,
    hermitianBinaryPauliMatrix_zero] using sum_hermitianPauli_swap13 K

theorem sum_hermitianPauliProduct_diagonal (K : ℕ) :
    (∑ p : PauliLabel K, hermitianPauliProductTensorThree K p p) =
      ((2 : ℂ) ^ K) • registerSwap12 K := by
  simp_rw [hermitianPauliProductTensorThree,
    hermitianBinaryPauliMatrix_sq]
  exact sum_hermitianPauli_swap12 K

theorem hermitianPauliProductTensorThree_zero_zero (K : ℕ) :
    hermitianPauliProductTensorThree K 0 0 = 1 := by
  classical
  ext x y
  simp [hermitianPauliProductTensorThree,
    hermitianBinaryPauliMatrix_zero, matrixTensorThree,
    Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;>
    by_cases h2 : x.2.1 = y.2.1 <;>
      by_cases h3 : x.2.2 = y.2.2 <;>
        simp [h1, h2, h3] <;> aesop

theorem pairClassIndicatorSum_one_eq_permutations (K : ℕ) :
    hermitianPauliProductPairClassIndicatorSum K 1 =
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
        (registerCycle123 K - registerCycle132 K) := by
  rw [pairClassIndicatorSum_one_eq_commutationSum,
    commutationSum_one_eq_permutations]

theorem pairClassIndicatorSum_zero_eq_permutations (K : ℕ) :
    hermitianPauliProductPairClassIndicatorSum K 0 =
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
          (registerCycle123 K + registerCycle132 K) -
        ((2 : ℂ) ^ K) •
          (registerSwap12 K + registerSwap23 K + registerSwap13 K) +
        (2 : ℂ) • (1 : ThirdM K) := by
  have h := commutationSum_zero_eq_indicator_add_degenerate K
  rw [commutationSum_zero_eq_permutations,
    sum_hermitianPauliProduct_zero_left,
    sum_hermitianPauliProduct_zero_right,
    sum_hermitianPauliProduct_diagonal,
    hermitianPauliProductTensorThree_zero_zero] at h
  have hnormalized :
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
          (registerCycle123 K + registerCycle132 K) =
        hermitianPauliProductPairClassIndicatorSum K 0 +
          ((2 : ℂ) ^ K) •
            (registerSwap12 K + registerSwap23 K + registerSwap13 K) -
          (2 : ℂ) • (1 : ThirdM K) := by
    rw [h]
    module
  rw [hnormalized]
  module

theorem sum_pauliPairClass_eq_indicatorSum
    (K : ℕ) (c : ZMod 2) :
    (∑ x : PauliPairClass K c,
      hermitianPauliProductTensorThree K x.1.1 x.1.2) =
      hermitianPauliProductPairClassIndicatorSum K c := by
  classical
  let P : PauliLabel K × PauliLabel K → Prop := fun pq ↦
    pq.1 ≠ 0 ∧ pq.2 ≠ 0 ∧ pq.1 ≠ pq.2 ∧
      pauliSymplecticForm K pq.1 pq.2 = c
  let f : PauliLabel K × PauliLabel K → ThirdM K := fun pq ↦
    hermitianPauliProductTensorThree K pq.1 pq.2
  unfold hermitianPauliProductPairClassIndicatorSum
  change (∑ x : PauliPairClass K c, f x.1) =
    ∑ p : PauliLabel K, ∑ q : PauliLabel K,
      if P (p, q) then f (p, q) else 0
  have hprod :
      (∑ pq : PauliLabel K × PauliLabel K,
        if P pq then f pq else 0) =
        ∑ p : PauliLabel K, ∑ q : PauliLabel K,
          if P (p, q) then f (p, q) else 0 :=
    Fintype.sum_prod_type
      (fun pq : PauliLabel K × PauliLabel K ↦
        if P pq then f pq else 0)
  rw [← hprod]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  apply Finset.sum_congr
  · ext x
    constructor
    · intro _
      exact Finset.mem_subtype.mpr (Finset.mem_univ x.1)
    · intro _
      exact Finset.mem_univ x
  · intro x hx
    rfl

theorem sum_pauliPairClass_zero_eq_permutations (K : ℕ) :
    (∑ x : PauliPairClass K 0,
      hermitianPauliProductTensorThree K x.1.1 x.1.2) =
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
          (registerCycle123 K + registerCycle132 K) -
        ((2 : ℂ) ^ K) •
          (registerSwap12 K + registerSwap23 K + registerSwap13 K) +
        (2 : ℂ) • (1 : ThirdM K) := by
  rw [sum_pauliPairClass_eq_indicatorSum,
    pairClassIndicatorSum_zero_eq_permutations]

theorem sum_pauliPairClass_one_eq_permutations (K : ℕ) :
    (∑ x : PauliPairClass K 1,
      hermitianPauliProductTensorThree K x.1.1 x.1.2) =
      ((((2 : ℂ) ^ K) ^ 2) / 2) •
        (registerCycle123 K - registerCycle132 K) := by
  rw [sum_pauliPairClass_eq_indicatorSum,
    pairClassIndicatorSum_one_eq_permutations]

theorem averagedHermitianPauliProductThirdMoment_commuting_eq
    (K : ℕ) (x : PauliPairClass K 0) :
    averagedHermitianPauliProductThirdMoment K x.1.1 x.1.2 =
      ((Fintype.card (PauliPairClass K 0) : ℂ)⁻¹) •
        (((((2 : ℂ) ^ K) ^ 2) / 2) •
            (registerCycle123 K + registerCycle132 K) -
          ((2 : ℂ) ^ K) •
            (registerSwap12 K + registerSwap23 K + registerSwap13 K) +
          (2 : ℂ) • (1 : ThirdM K)) := by
  rw [averagedHermitianPauliProductThirdMoment_eq_pairClass,
    sum_pauliPairClass_zero_eq_permutations]

theorem averagedHermitianPauliProductThirdMoment_anticommuting_eq
    (K : ℕ) (x : PauliPairClass K 1) :
    averagedHermitianPauliProductThirdMoment K x.1.1 x.1.2 =
      ((Fintype.card (PauliPairClass K 1) : ℂ)⁻¹) •
        (((((2 : ℂ) ^ K) ^ 2) / 2) •
          (registerCycle123 K - registerCycle132 K)) := by
  rw [averagedHermitianPauliProductThirdMoment_eq_pairClass,
    sum_pauliPairClass_one_eq_permutations]

end TomographyOracleCore
