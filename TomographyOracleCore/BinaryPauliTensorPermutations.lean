import TomographyOracleCore.BinaryCliffordFiniteThirdMoment

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Binary Pauli completeness and three-register permutations

The Hermitian binary Paulis form a self-dual matrix basis.  We prove the
entrywise completeness relation directly and use it to identify the Pauli
tensor sums in Webb's third-moment argument with the concrete register
swaps and three-cycles.
-/

/-- The square of the Hermitian phase is its binary cocycle sign. -/
theorem hermitianPauliPhase_sq_eq_character
    (K : ℕ) (p : PauliLabel K) :
    hermitianPauliPhase K p * hermitianPauliPhase K p =
      (binaryWordCharacter K p.2 p.1 : ℂ) := by
  have hs := hermitianPauliPhase_sq_mul_character K p
  have hc : (binaryWordCharacter K p.2 p.1 : ℂ) *
      (binaryWordCharacter K p.2 p.1 : ℂ) = 1 := by
    exact_mod_cast binaryWordCharacter_sq K p.2 p.1
  calc
    hermitianPauliPhase K p * hermitianPauliPhase K p =
        (hermitianPauliPhase K p * hermitianPauliPhase K p) * 1 := by
      rw [mul_one]
    _ = (hermitianPauliPhase K p * hermitianPauliPhase K p) *
        ((binaryWordCharacter K p.2 p.1 : ℂ) *
          (binaryWordCharacter K p.2 p.1 : ℂ)) := by rw [hc]
    _ = (hermitianPauliPhase K p * hermitianPauliPhase K p *
        (binaryWordCharacter K p.2 p.1 : ℂ)) *
          (binaryWordCharacter K p.2 p.1 : ℂ) := by ring
    _ = (binaryWordCharacter K p.2 p.1 : ℂ) := by rw [hs, one_mul]

/-- Exact complex character sum on binary words. -/
theorem sum_complex_binaryWordCharacter
    (K : ℕ) (t : PauliBinaryWord K) :
    (∑ z : PauliBinaryWord K, (binaryWordCharacter K z t : ℂ)) =
      if t = 0 then (2 : ℂ) ^ K else 0 := by
  by_cases ht : t = 0
  · subst t
    simp [PauliBinaryWord]
  · rw [if_neg ht]
    have hr := sum_binaryWordCharacter_eq_zero K ht
    have hc := congrArg (fun x : ℝ ↦ (x : ℂ)) hr
    push_cast at hc
    simpa [binaryWordCharacter_comm] using hc

/-- Inner Walsh sum occurring in Pauli completeness. -/
theorem sum_hermitianPauliPhase_character_product
    (K : ℕ) (x b d : PauliBinaryWord K) :
    (∑ z : PauliBinaryWord K,
      hermitianPauliPhase K (x, z) *
          (binaryWordCharacter K z b : ℂ) *
        (hermitianPauliPhase K (x, z) *
          (binaryWordCharacter K z d : ℂ))) =
      if x + b + d = 0 then (2 : ℂ) ^ K else 0 := by
  have hpoint : ∀ z : PauliBinaryWord K,
      hermitianPauliPhase K (x, z) *
          (binaryWordCharacter K z b : ℂ) *
        (hermitianPauliPhase K (x, z) *
          (binaryWordCharacter K z d : ℂ)) =
      (binaryWordCharacter K z (x + b + d) : ℂ) := by
    intro z
    rw [show hermitianPauliPhase K (x, z) *
          (binaryWordCharacter K z b : ℂ) *
        (hermitianPauliPhase K (x, z) *
          (binaryWordCharacter K z d : ℂ)) =
        (hermitianPauliPhase K (x, z) *
          hermitianPauliPhase K (x, z)) *
        ((binaryWordCharacter K z b : ℂ) *
          (binaryWordCharacter K z d : ℂ)) by ring]
    rw [hermitianPauliPhase_sq_eq_character]
    norm_cast
    rw [binaryWordCharacter_add_right, binaryWordCharacter_add_right]
    ring
  simp_rw [hpoint]
  exact sum_complex_binaryWordCharacter K (x + b + d)

/-- Self-dual completeness of the Hermitian binary Pauli basis. -/
theorem hermitianBinaryPauli_completeness
    (K : ℕ) (a b c d : PauliBinaryWord K) :
    (∑ p : PauliLabel K,
      hermitianBinaryPauliMatrix K p a b *
        hermitianBinaryPauliMatrix K p c d) =
      if a = d ∧ b = c then (2 : ℂ) ^ K else 0 := by
  classical
  simp only [hermitianBinaryPauliMatrix, binaryPauliMatrix,
    Fintype.sum_prod_type, Matrix.smul_apply, smul_eq_mul]
  simp only [mul_ite, ite_mul, zero_mul, mul_zero]
  simp_rw [Finset.sum_ite_irrel,
    sum_hermitianPauliPhase_character_product]
  rw [Finset.sum_eq_single (a + b)]
  · have hab : a = b + (a + b) := by
      calc
        a = a + 0 := by simp
        _ = a + (b + b) := by rw [binaryWord_add_self]
        _ = b + (a + b) := by abel
    have hsum : a + b + b + d = 0 ↔ a = d := by
      constructor
      · intro h
        calc
          a = a + 0 := by simp
          _ = a + (a + b + b + d) := by rw [h]
          _ = d := by
            rw [show a + (a + b + b + d) =
                (a + a) + (b + b) + d by abel,
              binaryWord_add_self, binaryWord_add_self, zero_add]
            simp
      · rintro rfl
        rw [show a + b + b + a = (a + a) + (b + b) by abel,
          binaryWord_add_self, zero_add, binaryWord_add_self]
    by_cases had : a = d
    · subst d
      have hcollapse : a + (a + b) = b := by
        rw [← add_assoc, binaryWord_add_self, zero_add]
      by_cases hbc : b = c
      · subst c
        have hc1 : b = a + (a + b) := hcollapse.symm
        have hc3 : a + b + b + a = 0 := hsum.mpr rfl
        rw [if_pos hc1, if_pos hab, if_pos hc3]
        simp
      · have hc1 : ¬c = a + (a + b) := by
          intro h
          apply hbc
          rw [hcollapse] at h
          exact h.symm
        rw [if_neg hc1]
        simp [hbc]
    · have hc3 : ¬a + b + b + d = 0 := fun h => had (hsum.mp h)
      have hrhs : ¬(a = d ∧ b = c) := fun h => had h.1
      by_cases hc1 : c = d + (a + b)
      · rw [if_pos hc1, if_pos hab, if_neg hc3, if_neg hrhs]
      · rw [if_neg hc1, if_neg hrhs]
        simp
  · intro x hx hne
    have hnot : ¬a = b + x := by
      intro h
      apply hne
      calc
        x = 0 + x := by simp
        _ = (b + b) + x := by rw [binaryWord_add_self]
        _ = b + (b + x) := by rw [add_assoc]
        _ = b + a := by rw [h]
        _ = a + b := add_comm _ _
    simp [hnot]
  · simp

/-! ## Concrete register permutations -/

def registerSwap12 (K : ℕ) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  fun x y ↦ if x.1 = y.2.1 ∧ x.2.1 = y.1 ∧ x.2.2 = y.2.2 then 1 else 0

def registerSwap23 (K : ℕ) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  fun x y ↦ if x.1 = y.1 ∧ x.2.1 = y.2.2 ∧ x.2.2 = y.2.1 then 1 else 0

def registerSwap13 (K : ℕ) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  fun x y ↦ if x.1 = y.2.2 ∧ x.2.1 = y.2.1 ∧ x.2.2 = y.1 then 1 else 0

def registerCycle123 (K : ℕ) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  fun x y ↦ if x.1 = y.2.1 ∧ x.2.1 = y.2.2 ∧ x.2.2 = y.1 then 1 else 0

def registerCycle132 (K : ℕ) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  fun x y ↦ if x.1 = y.2.2 ∧ x.2.1 = y.1 ∧ x.2.2 = y.2.1 then 1 else 0

/-- Pauli expansion of the swap of registers one and two. -/
theorem sum_hermitianPauli_swap12 (K : ℕ) :
    (∑ p : PauliLabel K,
      matrixTensorThree (hermitianBinaryPauliMatrix K p)
        (hermitianBinaryPauliMatrix K p) 1) =
      ((2 : ℂ) ^ K) • registerSwap12 K := by
  classical
  ext x y
  rw [Matrix.sum_apply, Matrix.smul_apply]
  change (∑ p : PauliLabel K,
      hermitianBinaryPauliMatrix K p x.1 y.1 *
        hermitianBinaryPauliMatrix K p x.2.1 y.2.1 *
          (1 : Matrix (PauliBinaryWord K)
            (PauliBinaryWord K) ℂ) x.2.2 y.2.2) = _
  by_cases h3 : x.2.2 = y.2.2
  · simp only [Matrix.one_apply, if_pos h3, mul_one]
    rw [hermitianBinaryPauli_completeness]
    unfold registerSwap12
    by_cases h1 : x.1 = y.2.1 <;>
      by_cases h2 : x.2.1 = y.1 <;>
        simp [h1, h2, h3] <;> aesop
  · simp [h3, registerSwap12]

/-- Pauli expansion of the swap of registers two and three. -/
theorem sum_hermitianPauli_swap23 (K : ℕ) :
    (∑ p : PauliLabel K,
      matrixTensorThree 1 (hermitianBinaryPauliMatrix K p)
        (hermitianBinaryPauliMatrix K p)) =
      ((2 : ℂ) ^ K) • registerSwap23 K := by
  classical
  ext x y
  rw [Matrix.sum_apply, Matrix.smul_apply]
  change (∑ p : PauliLabel K,
      (1 : Matrix (PauliBinaryWord K)
          (PauliBinaryWord K) ℂ) x.1 y.1 *
        hermitianBinaryPauliMatrix K p x.2.1 y.2.1 *
          hermitianBinaryPauliMatrix K p x.2.2 y.2.2) = _
  by_cases h1 : x.1 = y.1
  · simp only [Matrix.one_apply, if_pos h1, one_mul]
    rw [hermitianBinaryPauli_completeness]
    unfold registerSwap23
    by_cases h2 : x.2.1 = y.2.2 <;>
      by_cases h3 : x.2.2 = y.2.1 <;>
        simp [h1, h2, h3] <;> aesop
  · simp [h1, registerSwap23]

/-- Pauli expansion of the swap of registers one and three. -/
theorem sum_hermitianPauli_swap13 (K : ℕ) :
    (∑ p : PauliLabel K,
      matrixTensorThree (hermitianBinaryPauliMatrix K p) 1
        (hermitianBinaryPauliMatrix K p)) =
      ((2 : ℂ) ^ K) • registerSwap13 K := by
  classical
  ext x y
  rw [Matrix.sum_apply, Matrix.smul_apply]
  change (∑ p : PauliLabel K,
      hermitianBinaryPauliMatrix K p x.1 y.1 *
        (1 : Matrix (PauliBinaryWord K)
          (PauliBinaryWord K) ℂ) x.2.1 y.2.1 *
          hermitianBinaryPauliMatrix K p x.2.2 y.2.2) = _
  by_cases h2 : x.2.1 = y.2.1
  · simp only [Matrix.one_apply, if_pos h2, mul_one]
    rw [hermitianBinaryPauli_completeness]
    unfold registerSwap13
    by_cases h1 : x.1 = y.2.2 <;>
      by_cases h3 : x.2.2 = y.1 <;>
        simp [h1, h2, h3] <;> aesop
  · simp [h2, registerSwap13]

/-- Pauli expansion of the forward three-register cycle. -/
theorem sum_hermitianPauli_cycle123 (K : ℕ) :
    (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      matrixTensorThree (hermitianBinaryPauliMatrix K p)
        (hermitianBinaryPauliMatrix K q)
        (hermitianBinaryPauliMatrix K p *
          hermitianBinaryPauliMatrix K q)) =
      (((2 : ℂ) ^ K) ^ 2) • registerCycle123 K := by
  classical
  ext x y
  simp_rw [Matrix.sum_apply]
  rw [Matrix.smul_apply]
  change (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      hermitianBinaryPauliMatrix K p x.1 y.1 *
        hermitianBinaryPauliMatrix K q x.2.1 y.2.1 *
          ((hermitianBinaryPauliMatrix K p *
            hermitianBinaryPauliMatrix K q) x.2.2 y.2.2)) = _
  simp_rw [Matrix.mul_apply, Finset.mul_sum]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [show ∀ (p q : PauliLabel K) (i : PauliBinaryWord K),
      hermitianBinaryPauliMatrix K p x.1 y.1 *
          hermitianBinaryPauliMatrix K q x.2.1 y.2.1 *
        (hermitianBinaryPauliMatrix K p x.2.2 i *
          hermitianBinaryPauliMatrix K q i y.2.2) =
      (hermitianBinaryPauliMatrix K p x.1 y.1 *
        hermitianBinaryPauliMatrix K p x.2.2 i) *
      (hermitianBinaryPauliMatrix K q x.2.1 y.2.1 *
        hermitianBinaryPauliMatrix K q i y.2.2) by intros; ring]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul,
    hermitianBinaryPauli_completeness]
  unfold registerCycle123
  by_cases h13 : y.1 = x.2.2 <;>
    by_cases h23 : x.2.1 = y.2.2 <;>
      simp [h13, h23] <;> aesop <;> ring

/-- Pauli expansion of the reverse three-register cycle. -/
theorem sum_hermitianPauli_cycle132 (K : ℕ) :
    (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      matrixTensorThree (hermitianBinaryPauliMatrix K p)
        (hermitianBinaryPauliMatrix K q)
        (hermitianBinaryPauliMatrix K q *
          hermitianBinaryPauliMatrix K p)) =
      (((2 : ℂ) ^ K) ^ 2) • registerCycle132 K := by
  classical
  ext x y
  simp_rw [Matrix.sum_apply]
  rw [Matrix.smul_apply]
  change (∑ p : PauliLabel K, ∑ q : PauliLabel K,
      hermitianBinaryPauliMatrix K p x.1 y.1 *
        hermitianBinaryPauliMatrix K q x.2.1 y.2.1 *
          ((hermitianBinaryPauliMatrix K q *
            hermitianBinaryPauliMatrix K p) x.2.2 y.2.2)) = _
  simp_rw [Matrix.mul_apply, Finset.mul_sum]
  conv_lhs =>
    enter [2, p]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp_rw [show ∀ (p q : PauliLabel K) (i : PauliBinaryWord K),
      hermitianBinaryPauliMatrix K p x.1 y.1 *
          hermitianBinaryPauliMatrix K q x.2.1 y.2.1 *
        (hermitianBinaryPauliMatrix K q x.2.2 i *
          hermitianBinaryPauliMatrix K p i y.2.2) =
      (hermitianBinaryPauliMatrix K p x.1 y.1 *
        hermitianBinaryPauliMatrix K p i y.2.2) *
      (hermitianBinaryPauliMatrix K q x.2.1 y.2.1 *
        hermitianBinaryPauliMatrix K q x.2.2 i) by intros; ring]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul,
    hermitianBinaryPauli_completeness]
  unfold registerCycle132
  by_cases h13 : x.1 = y.2.2 <;>
    by_cases h23 : y.2.1 = x.2.2 <;>
      simp [h13, h23] <;> aesop <;> ring

end TomographyOracleCore
