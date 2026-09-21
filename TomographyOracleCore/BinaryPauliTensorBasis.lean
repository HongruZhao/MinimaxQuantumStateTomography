import TomographyOracleCore.BinaryCliffordWebbClassExpansion

namespace TomographyOracleCore
open scoped BigOperators
noncomputable section

theorem sum_five_reorder
    {α β γ δ ε R : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [Fintype δ] [Fintype ε] [AddCommMonoid R]
    (f : α → β → γ → δ → ε → R) :
    (∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e) =
      ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, f a b c d e := by
  classical
  calc
    _ = ∑ a, ∑ b, ∑ d, ∑ c, ∑ e, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ a, ∑ d, ∑ b, ∑ c, ∑ e, f a b c d e := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ a, ∑ b, ∑ c, ∑ e, f a b c d e := by
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ a, ∑ b, ∑ e, ∑ c, f a b c d e := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ a, ∑ e, ∑ b, ∑ c, f a b c d e := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = ∑ d, ∑ e, ∑ a, ∑ b, ∑ c, f a b c d e := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]

theorem sum_three_mul_separable
    {α β γ R : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [CommSemiring R] (f : α → R) (g : β → R) (h : γ → R) :
    (∑ a, ∑ b, ∑ c, f a * g b * h c) =
      (∑ a, f a) * (∑ b, g b) * (∑ c, h c) := by
  calc
    _ = (∑ a, ∑ b, f a * g b) * (∑ c, h c) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
    _ = ((∑ a, f a) * (∑ b, g b)) * (∑ c, h c) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

theorem sum_three_mul_separable_left
    {α β γ R : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [CommSemiring R] (c : R) (f : α → R) (g : β → R) (h : γ → R) :
    (∑ a, ∑ b, ∑ d, c * f a * g b * h d) =
      c * (∑ a, f a) * (∑ b, g b) * (∑ d, h d) := by
  calc
    _ = c * (∑ a, ∑ b, ∑ d, f a * g b * h d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ = _ := by rw [sum_three_mul_separable]; ring

abbrev hermitianPauliTensorThree (K : ℕ) (p q r : PauliLabel K) : ThirdM K :=
  matrixTensorThree
    (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)
    (hermitianBinaryPauliMatrix K r)

theorem hermitianPauliTensorThree_reconstruction_unscaled
    (K : ℕ) (X : ThirdM K) :
    (∑ p : PauliLabel K, ∑ q : PauliLabel K, ∑ r : PauliLabel K,
      (∑ a : TripleIndex (PauliBinaryWord K),
        ∑ b : TripleIndex (PauliBinaryWord K),
          hermitianPauliTensorThree K p q r b a * X a b) •
        hermitianPauliTensorThree K p q r) =
      ((((2 : ℂ) ^ K) ^ 3)) • X := by
  classical
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    hermitianPauliTensorThree, matrixTensorThree]
  simp_rw [Finset.sum_mul]
  rw [sum_five_reorder]
  calc
    _ = ∑ a : TripleIndex (PauliBinaryWord K),
          ∑ b : TripleIndex (PauliBinaryWord K),
        X a b *
          (∑ p : PauliLabel K,
            hermitianBinaryPauliMatrix K p b.1 a.1 *
              hermitianBinaryPauliMatrix K p x.1 y.1) *
          (∑ q : PauliLabel K,
            hermitianBinaryPauliMatrix K q b.2.1 a.2.1 *
              hermitianBinaryPauliMatrix K q x.2.1 y.2.1) *
          (∑ r : PauliLabel K,
            hermitianBinaryPauliMatrix K r b.2.2 a.2.2 *
              hermitianBinaryPauliMatrix K r x.2.2 y.2.2) := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [← sum_three_mul_separable_left]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ = (2 ^ K) ^ 3 * X x y := by
      simp_rw [hermitianBinaryPauli_completeness]
      rw [Finset.sum_eq_single x]
      · rw [Finset.sum_eq_single y]
        · simp
          ring
        · intro b hb hby
          by_cases hb1 : b.1 = y.1
          · by_cases hb2 : b.2.1 = y.2.1
            · by_cases hb3 : b.2.2 = y.2.2
              · exfalso
                apply hby
                apply Prod.ext
                · exact hb1
                · apply Prod.ext
                  · exact hb2
                  · exact hb3
              · simp [hb3]
            · simp [hb2]
          · simp [hb1]
        · simp
      · intro a ha hax
        apply Finset.sum_eq_zero
        intro b hb
        by_cases ha1 : a.1 = x.1
        · by_cases ha2 : a.2.1 = x.2.1
          · by_cases ha3 : a.2.2 = x.2.2
            · exfalso
              apply hax
              apply Prod.ext
              · exact ha1
              · apply Prod.ext
                · exact ha2
                · exact ha3
            · simp [ha3]
          · simp [ha2]
        · simp [ha1]
      · simp

/-- Explicit reconstruction of an arbitrary matrix from the Hermitian Pauli
tensor basis.  This is the Pauli-basis linear-extension step in Webb's proof. -/
theorem hermitianPauliTensorThree_reconstruction
    (K : ℕ) (X : ThirdM K) :
    X = (((((2 : ℂ) ^ K) ^ 3))⁻¹) •
      (∑ p : PauliLabel K, ∑ q : PauliLabel K, ∑ r : PauliLabel K,
        (∑ a : TripleIndex (PauliBinaryWord K),
          ∑ b : TripleIndex (PauliBinaryWord K),
            hermitianPauliTensorThree K p q r b a * X a b) •
          hermitianPauliTensorThree K p q r) := by
  symm
  rw [hermitianPauliTensorThree_reconstruction_unscaled, smul_smul]
  have hD : ((((2 : ℂ) ^ K) ^ 3)) ≠ 0 := by norm_num
  rw [inv_mul_cancel₀ hD, one_smul]

end
end TomographyOracleCore
