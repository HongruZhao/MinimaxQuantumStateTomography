import TomographyOracleCore.BinaryCliffordPauliCosetMixing

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Pauli-character cancellation in Webb's three-fold twirl

This module isolates the Case 3 cancellation in Webb's Lemma 4.  It proves
only the finite Pauli-character identity: averaging the product of three
commutation signs over the free Pauli coordinate is zero unless the three
binary labels sum to zero.  The result is also transported through the
generated symplectic action and lifted to an arbitrary module-valued factor
that depends only on the symplectic coordinate.

These are ingredients for a matrix three-twirl calculation, not a unitary
three-design theorem.
-/

/-- The product of the three Pauli commutation signs used by the third
tensor power of conjugation. -/
noncomputable def pauliTripleCharacter (K : ℕ)
    (a p q r : PauliLabel K) : ℝ :=
  pauliCharacter K a p * pauliCharacter K a q *
    pauliCharacter K a r

/-- The binary symplectic commutation character is symmetric. -/
theorem pauliCharacter_comm (K : ℕ) (p q : PauliLabel K) :
    pauliCharacter K p q = pauliCharacter K q p := by
  unfold pauliCharacter
  rw [pauliSymplecticForm_symm]

/-- Three commutation signs multiply to the single character at the sum of
the three labels. -/
theorem pauliTripleCharacter_eq_character_sum (K : ℕ)
    (a p q r : PauliLabel K) :
    pauliTripleCharacter K a p q r =
      pauliCharacter K a (p + q + r) := by
  unfold pauliTripleCharacter
  rw [pauliCharacter_add_right, pauliCharacter_add_right]

/-- Webb Case 3 in scalar form: if the three Pauli labels do not multiply
to a scalar identity (equivalently, their binary sum is nonzero), their
triple commutation character has zero uniform sum. -/
theorem sum_pauliTripleCharacter_eq_zero (K : ℕ)
    (p q r : PauliLabel K) (hsum : p + q + r ≠ 0) :
    ∑ a : PauliLabel K, pauliTripleCharacter K a p q r = 0 := by
  simp_rw [pauliTripleCharacter_eq_character_sum,
    pauliCharacter_comm K _ (p + q + r)]
  exact sum_pauliCharacter_eq_zero K hsum

/-- A concrete Pauli translation whose three commutation signs multiply to
minus one whenever the label sum is nonzero. -/
theorem exists_pauliTripleCharacter_eq_neg_one (K : ℕ)
    (p q r : PauliLabel K) (hsum : p + q + r ≠ 0) :
    ∃ a : PauliLabel K, pauliTripleCharacter K a p q r = -1 := by
  obtain ⟨a, ha⟩ := exists_pauliSymplectic_pair_one K hsum
  refine ⟨a, ?_⟩
  calc
    pauliTripleCharacter K a p q r =
        pauliCharacter K a (p + q + r) :=
      pauliTripleCharacter_eq_character_sum K a p q r
    _ = pauliCharacter K (p + q + r) a :=
      pauliCharacter_comm K a (p + q + r)
    _ = -1 := by simp only [pauliCharacter, ha, binarySign_one]

/-- Complex-valued form of the triple commutation character. -/
noncomputable def complexPauliTripleCharacter (K : ℕ)
    (a p q r : PauliLabel K) : ℂ :=
  (pauliTripleCharacter K a p q r : ℂ)

/-- The complex triple character has the same zero-sum cancellation. -/
theorem sum_complexPauliTripleCharacter_eq_zero (K : ℕ)
    (p q r : PauliLabel K) (hsum : p + q + r ≠ 0) :
    ∑ a : PauliLabel K, complexPauliTripleCharacter K a p q r = 0 := by
  have hreal := sum_pauliTripleCharacter_eq_zero K p q r hsum
  have hcomplex := congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
  push_cast at hcomplex
  simpa [complexPauliTripleCharacter] using hcomplex

/-- The cancellation remains valid after attaching an arbitrary constant
module-valued orbit term. -/
theorem sum_complexPauliTripleCharacter_smul_eq_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (K : ℕ) (p q r : PauliLabel K) (hsum : p + q + r ≠ 0)
    (X : V) :
    ∑ a : PauliLabel K,
      complexPauliTripleCharacter K a p q r • X = 0 := by
  rw [← Finset.sum_smul]
  rw [sum_complexPauliTripleCharacter_eq_zero K p q r hsum, zero_smul]

/-- Literal product-of-three-characters spelling of the module-valued
cancellation, convenient for direct use after three tensor factors have
been expanded. -/
theorem sum_complexPauliCharacter_product_smul_eq_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (K : ℕ) (p q r : PauliLabel K) (hsum : p + q + r ≠ 0)
    (X : V) :
    ∑ a : PauliLabel K,
      ((pauliCharacter K a p : ℂ) *
        (pauliCharacter K a q : ℂ) *
        (pauliCharacter K a r : ℂ)) • X = 0 := by
  simpa [complexPauliTripleCharacter, pauliTripleCharacter] using
    sum_complexPauliTripleCharacter_smul_eq_zero K p q r hsum X

/-- A symplectic action preserves the nonzero three-label sum. -/
theorem binarySymplectic_three_sum_ne_zero
    (K : ℕ) (g : binarySymplecticGroup K)
    (p q r : PauliLabel K) (hsum : p + q + r ≠ 0) :
    g.1 p + g.1 q + g.1 r ≠ 0 := by
  intro hzero
  apply hsum
  apply g.1.injective
  simpa only [map_add, map_zero] using hzero

/-- Exact Pauli-coordinate cancellation after any generated symplectic
action, in the module-valued form used inside a three-fold twirl. -/
theorem sum_complexPauliTripleCharacter_smul_binaryTransvection_eq_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (K : ℕ) (g : binaryTransvectionGroup K)
    (p q r : PauliLabel K) (hsum : p + q + r ≠ 0)
    (X : V) :
    ∑ a : PauliLabel K,
      complexPauliTripleCharacter K a
        (g.1.1 p) (g.1.1 q) (g.1.1 r) • X = 0 := by
  exact sum_complexPauliTripleCharacter_smul_eq_zero K
    (g.1.1 p) (g.1.1 q) (g.1.1 r)
    (binarySymplectic_three_sum_ne_zero K g.1 p q r hsum) X

/-- Literal product-of-three-characters spelling after a generated
symplectic action. -/
theorem sum_complexPauliCharacter_product_smul_binaryTransvection_eq_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (K : ℕ) (g : binaryTransvectionGroup K)
    (p q r : PauliLabel K) (hsum : p + q + r ≠ 0)
    (X : V) :
    ∑ a : PauliLabel K,
      ((pauliCharacter K a (g.1.1 p) : ℂ) *
        (pauliCharacter K a (g.1.1 q) : ℂ) *
        (pauliCharacter K a (g.1.1 r) : ℂ)) • X = 0 := by
  simpa [complexPauliTripleCharacter, pauliTripleCharacter] using
    sum_complexPauliTripleCharacter_smul_binaryTransvection_eq_zero
      K g p q r hsum X

/-- Grouping the whole Pauli-coset ensemble by its symplectic coordinate
annihilates every three-fold orbit term whose Pauli coordinate enters only
through the three commutation signs.  The factor `X g` may be any vector,
matrix, or tensor-cube term depending on `g`. -/
theorem sum_pauliCosetClifford_tripleCharacter_smul_eq_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (K : ℕ) (p q r : PauliLabel K) (hsum : p + q + r ≠ 0)
    (X : binaryTransvectionGroup K → V) :
    ∑ e : PauliCosetCliffordEnsemble K,
      complexPauliTripleCharacter K e.1
        (e.2.1.1 p) (e.2.1.1 q) (e.2.1.1 r) • X e.2 = 0 := by
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_eq_zero
  intro g hg
  exact sum_complexPauliTripleCharacter_smul_binaryTransvection_eq_zero
    K g p q r hsum (X g)

end TomographyOracleCore
