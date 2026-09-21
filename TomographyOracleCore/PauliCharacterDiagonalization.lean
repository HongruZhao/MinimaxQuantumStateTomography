import TomographyOracleCore.BinarySymplecticPauli
import TomographyOracleCore.IndependentBlockPauliCounting
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace TomographyOracleCore

/-!
# Binary Pauli characters and abstract channel diagonalization

This module proves the elementary character orthogonality underlying
computational-basis Pauli dephasing, then packages the finite-group average
as a genuinely diagonal channel on Pauli coefficients.

No matrix representation of physical Clifford operators is assumed here.
The final theorems therefore isolate that representation theorem as the
remaining interface between the finite binary calculation and the physical
Born measurement channel.
-/

open scoped BigOperators

/-! ## The sign character of `ZMod 2` -/

/-- The real sign character of the additive group `ZMod 2`. -/
def binarySign (a : ZMod 2) : ℝ := if a = 0 then 1 else -1

@[simp] theorem binarySign_zero : binarySign 0 = 1 := by
  simp [binarySign]

@[simp] theorem binarySign_one : binarySign 1 = -1 := by
  norm_num [binarySign]

/-- The sign character turns binary addition into multiplication. -/
theorem binarySign_add (a b : ZMod 2) :
    binarySign (a + b) = binarySign a * binarySign b := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl
  · simp
  · rcases zmodTwo_eq_zero_or_one b with rfl | rfl
    · simp
    · rw [CharTwo.add_self_eq_zero]
      simp

theorem binarySign_ne_zero (a : ZMod 2) : binarySign a ≠ 0 := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;> norm_num

theorem binarySign_sq (a : ZMod 2) : binarySign a * binarySign a = 1 := by
  rcases zmodTwo_eq_zero_or_one a with rfl | rfl <;> norm_num

/-! ## Characters on binary words -/

/-- Binary dot product on `K`-bit words. -/
def binaryDotProduct (K : ℕ) (x y : PauliBinaryWord K) : ZMod 2 :=
  ∑ i, x i * y i

theorem binaryDotProduct_add_left (K : ℕ)
    (x y z : PauliBinaryWord K) :
    binaryDotProduct K (x + y) z =
      binaryDotProduct K x z + binaryDotProduct K y z := by
  simp only [binaryDotProduct, Pi.add_apply, add_mul]
  exact Finset.sum_add_distrib

theorem binaryDotProduct_add_right (K : ℕ)
    (x y z : PauliBinaryWord K) :
    binaryDotProduct K x (y + z) =
      binaryDotProduct K x y + binaryDotProduct K x z := by
  simp only [binaryDotProduct, Pi.add_apply, mul_add]
  exact Finset.sum_add_distrib

@[simp] theorem binaryDotProduct_zero_left (K : ℕ)
    (y : PauliBinaryWord K) : binaryDotProduct K 0 y = 0 := by
  simp [binaryDotProduct]

@[simp] theorem binaryDotProduct_zero_right (K : ℕ)
    (x : PauliBinaryWord K) : binaryDotProduct K x 0 = 0 := by
  simp [binaryDotProduct]

/-- Real character indexed by a binary word. -/
def binaryWordCharacter (K : ℕ)
    (x y : PauliBinaryWord K) : ℝ :=
  binarySign (binaryDotProduct K x y)

/-- Binary words add to zero with themselves. -/
theorem binaryWord_add_self (K : ℕ) (x : PauliBinaryWord K) : x + x = 0 := by
  funext i
  exact CharTwo.add_self_eq_zero (x i)

@[simp] theorem binaryWordCharacter_zero_left (K : ℕ)
    (y : PauliBinaryWord K) : binaryWordCharacter K 0 y = 1 := by
  simp [binaryWordCharacter]

@[simp] theorem binaryWordCharacter_zero_right (K : ℕ)
    (x : PauliBinaryWord K) : binaryWordCharacter K x 0 = 1 := by
  simp [binaryWordCharacter]

theorem binaryWordCharacter_add_left (K : ℕ)
    (x y z : PauliBinaryWord K) :
    binaryWordCharacter K (x + y) z =
      binaryWordCharacter K x z * binaryWordCharacter K y z := by
  rw [binaryWordCharacter, binaryDotProduct_add_left, binarySign_add]
  rfl

theorem binaryWordCharacter_add_right (K : ℕ)
    (x y z : PauliBinaryWord K) :
    binaryWordCharacter K x (y + z) =
      binaryWordCharacter K x y * binaryWordCharacter K x z := by
  rw [binaryWordCharacter, binaryDotProduct_add_right, binarySign_add]
  rfl

/-- A nonzero binary word has a coordinate word with dot product one. -/
theorem exists_binaryDotProduct_one (K : ℕ)
    {x : PauliBinaryWord K} (hx : x ≠ 0) :
    ∃ y : PauliBinaryWord K, binaryDotProduct K x y = 1 := by
  classical
  have hxi : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    apply hx
    funext i
    exact h i
  obtain ⟨i, hi⟩ := hxi
  have hi1 : x i = 1 := by
    rcases zmodTwo_eq_zero_or_one (x i) with h | h
    · exact (hi h).elim
    · exact h
  refine ⟨Pi.single i 1, ?_⟩
  simp only [binaryDotProduct]
  rw [Finset.sum_eq_single i]
  · simp [hi1]
  · intro j _ hji
    simp [hji]
  · simp

/-- Every nontrivial binary character has zero sum. -/
theorem sum_binaryWordCharacter_eq_zero (K : ℕ)
    {x : PauliBinaryWord K} (hx : x ≠ 0) :
    ∑ y : PauliBinaryWord K, binaryWordCharacter K x y = 0 := by
  classical
  obtain ⟨r, hr⟩ := exists_binaryDotProduct_one K hx
  have hshift := Equiv.sum_comp (Equiv.addRight r)
    (binaryWordCharacter K x)
  have hpoint : ∀ y : PauliBinaryWord K,
      binaryWordCharacter K x (y + r) =
        -binaryWordCharacter K x y := by
    intro y
    have hcr : binaryWordCharacter K x r = -1 := by
      simp [binaryWordCharacter, hr]
    rw [binaryWordCharacter_add_right, hcr]
    ring
  have hneg :
      (∑ y : PauliBinaryWord K, binaryWordCharacter K x (y + r)) =
        -(∑ y : PauliBinaryWord K, binaryWordCharacter K x y) := by
    simp_rw [hpoint]
    simp
  change (∑ i, binaryWordCharacter K x (i + r)) =
      ∑ i, binaryWordCharacter K x i at hshift
  rw [hneg] at hshift
  linarith

/-- Exact Walsh-character orthogonality on `K` bits. -/
theorem sum_binaryWordCharacter_mul (K : ℕ)
    (x z : PauliBinaryWord K) :
    (∑ y : PauliBinaryWord K,
      binaryWordCharacter K x y * binaryWordCharacter K z y) =
      if x = z then (2 : ℝ) ^ K else 0 := by
  classical
  have hadd : ∀ y : PauliBinaryWord K,
      binaryWordCharacter K x y * binaryWordCharacter K z y =
        binaryWordCharacter K (x + z) y := by
    intro y
    exact (binaryWordCharacter_add_left K x z y).symm
  simp_rw [hadd]
  by_cases hxz : x = z
  · subst z
    rw [if_pos rfl, binaryWord_add_self]
    simp [PauliBinaryWord]
  · rw [if_neg hxz]
    apply sum_binaryWordCharacter_eq_zero K
    intro hzero
    apply hxz
    calc
      x = x + 0 := by simp
      _ = x + (x + z) := by rw [hzero]
      _ = (x + x) + z := by abel
      _ = z := by
        rw [binaryWord_add_self, zero_add]

/-- Normalized Walsh-character orthogonality. -/
theorem average_binaryWordCharacter_mul
    {K : ℕ} (x z : PauliBinaryWord K) :
    (∑ y : PauliBinaryWord K,
      binaryWordCharacter K x y * binaryWordCharacter K z y) /
        (2 : ℝ) ^ K =
      if x = z then 1 else 0 := by
  rw [sum_binaryWordCharacter_mul]
  by_cases h : x = z <;> simp [h]

/-! ## Symplectic Pauli characters -/

/-- Real commutation character of two binary Pauli labels. -/
noncomputable def pauliCharacter (K : ℕ) (p q : PauliLabel K) : ℝ :=
  binarySign (pauliSymplecticForm K p q)

@[simp] theorem pauliCharacter_zero_left (K : ℕ) (q : PauliLabel K) :
    pauliCharacter K 0 q = 1 := by
  simp [pauliCharacter]

@[simp] theorem pauliCharacter_zero_right (K : ℕ) (p : PauliLabel K) :
    pauliCharacter K p 0 = 1 := by
  simp [pauliCharacter]

theorem pauliCharacter_add_left (K : ℕ)
    (p q r : PauliLabel K) :
    pauliCharacter K (p + q) r =
      pauliCharacter K p r * pauliCharacter K q r := by
  rw [pauliCharacter, LinearMap.map_add₂, binarySign_add]
  rfl

theorem pauliCharacter_add_right (K : ℕ)
    (p q r : PauliLabel K) :
    pauliCharacter K p (q + r) =
      pauliCharacter K p q * pauliCharacter K p r := by
  rw [pauliCharacter, map_add, binarySign_add]
  rfl

/-- Every nontrivial symplectic Pauli character has zero sum. -/
theorem sum_pauliCharacter_eq_zero (K : ℕ)
    {p : PauliLabel K} (hp : p ≠ 0) :
    ∑ q : PauliLabel K, pauliCharacter K p q = 0 := by
  classical
  obtain ⟨r, hr⟩ := exists_pauliSymplectic_pair_one K hp
  have hshift := Equiv.sum_comp (Equiv.addRight r) (pauliCharacter K p)
  have hpoint : ∀ q : PauliLabel K,
      pauliCharacter K p (q + r) = -pauliCharacter K p q := by
    intro q
    have hcr : pauliCharacter K p r = -1 := by
      simp [pauliCharacter, hr]
    rw [pauliCharacter_add_right, hcr]
    ring
  have hneg :
      (∑ q : PauliLabel K, pauliCharacter K p (q + r)) =
        -(∑ q : PauliLabel K, pauliCharacter K p q) := by
    simp_rw [hpoint]
    simp
  change (∑ i, pauliCharacter K p (i + r)) =
      ∑ i, pauliCharacter K p i at hshift
  rw [hneg] at hshift
  linarith

/-- Exact orthogonality of binary symplectic Pauli characters. -/
theorem sum_pauliCharacter_mul (K : ℕ) (p r : PauliLabel K) :
    (∑ q : PauliLabel K,
      pauliCharacter K p q * pauliCharacter K r q) =
      if p = r then (4 : ℝ) ^ K else 0 := by
  classical
  have hadd : ∀ q : PauliLabel K,
      pauliCharacter K p q * pauliCharacter K r q =
        pauliCharacter K (p + r) q := by
    intro q
    exact (pauliCharacter_add_left K p r q).symm
  simp_rw [hadd]
  by_cases hpr : p = r
  · subst r
    rw [if_pos rfl, pauliLabel_add_self]
    simp [PauliLabel, PauliBinaryWord, ← mul_pow]
  · rw [if_neg hpr]
    apply sum_pauliCharacter_eq_zero K
    intro hzero
    apply hpr
    calc
      p = p + 0 := by simp
      _ = p + (p + r) := by rw [hzero]
      _ = (p + p) + r := by abel
      _ = r := by rw [pauliLabel_add_self, zero_add]

/-! ## Computational dephasing and a finite group average -/

/-- A Pauli label is diagonal in the computational basis exactly when its
`X` word vanishes. -/
def IsComputationalPauli {K : ℕ} (p : PauliLabel K) : Prop := p.1 = 0

instance instDecidableIsComputationalPauli {K : ℕ} (p : PauliLabel K) :
    Decidable (IsComputationalPauli p) := by
  exact inferInstanceAs (Decidable (p.1 = 0))

/-- Coefficient-space computational dephasing: retain precisely the
computational-basis (`Z`-type) Pauli coordinates. -/
def computationalPauliDephasing (K : ℕ)
    (f : PauliLabel K → ℝ) : PauliLabel K → ℝ :=
  fun p ↦ if IsComputationalPauli p then f p else 0

@[simp] theorem computationalPauliDephasing_apply (K : ℕ)
    (f : PauliLabel K → ℝ) (p : PauliLabel K) :
    computationalPauliDephasing K f p =
      if IsComputationalPauli p then f p else 0 := rfl

/-- Permutation of Pauli coefficients induced by a group action on labels. -/
def actOnPauliCoefficients
    {K : ℕ} {C : Type*} [Group C] [MulAction C (PauliLabel K)]
    (c : C) (f : PauliLabel K → ℝ) : PauliLabel K → ℝ :=
  fun p ↦ f (c⁻¹ • p)

/-- Conjugate computational dephasing by one abstract Pauli-label action. -/
def conjugatedComputationalPauliDephasing
    {K : ℕ} {C : Type*} [Group C] [MulAction C (PauliLabel K)]
    (c : C) (f : PauliLabel K → ℝ) : PauliLabel K → ℝ :=
  actOnPauliCoefficients c⁻¹
    (computationalPauliDephasing K (actOnPauliCoefficients c f))

/-- Conjugation signs cancel: conjugated dephasing is diagonal and retains
the coordinate `p` precisely when `c • p` is computational-basis diagonal. -/
theorem conjugatedComputationalPauliDephasing_apply
    {K : ℕ} {C : Type*} [Group C] [MulAction C (PauliLabel K)]
    (c : C) (f : PauliLabel K → ℝ) (p : PauliLabel K) :
    conjugatedComputationalPauliDephasing c f p =
      if IsComputationalPauli (c • p) then f p else 0 := by
  simp [conjugatedComputationalPauliDephasing, actOnPauliCoefficients,
    computationalPauliDephasing]

/-- Uniform average of conjugated computational dephasing channels. -/
noncomputable def finitePauliMeasurementChannel
    {K : ℕ} (C : Type*) [Group C] [Fintype C]
    [MulAction C (PauliLabel K)]
    (f : PauliLabel K → ℝ) : PauliLabel K → ℝ :=
  fun p ↦ (∑ c : C, conjugatedComputationalPauliDephasing c f p) /
    Fintype.card C

/-- Fraction of group elements sending a label into the computational Pauli
subspace. -/
noncomputable def finitePauliHitEigenvalue
    {K : ℕ} (C : Type*) [Group C] [Fintype C]
    [MulAction C (PauliLabel K)] (p : PauliLabel K) : ℝ :=
  ((Fintype.card {c : C // IsComputationalPauli (c • p)} : ℕ) : ℝ) /
    Fintype.card C

/-- Exact abstract Pauli-channel diagonalization.  This is the finite-sum
calculation behind `M(P)=m_P P`; the only remaining physical premise is that
the implemented conjugation really induces the supplied label action. -/
theorem finitePauliMeasurementChannel_apply
    {K : ℕ} (C : Type*) [Group C] [Fintype C]
    [MulAction C (PauliLabel K)]
    (f : PauliLabel K → ℝ) (p : PauliLabel K) :
    finitePauliMeasurementChannel C f p =
      finitePauliHitEigenvalue C p * f p := by
  classical
  rw [finitePauliMeasurementChannel, finitePauliHitEigenvalue]
  simp_rw [conjugatedComputationalPauliDephasing_apply]
  have hcount :
      (∑ c : C, if IsComputationalPauli (c • p) then (1 : ℝ) else 0) =
        (Fintype.card {c : C // IsComputationalPauli (c • p)} : ℕ) := by
    rw [Finset.sum_boole, ← Fintype.card_subtype]
  have hfactor :
      (∑ c : C, if IsComputationalPauli (c • p) then f p else 0) =
        (∑ c : C,
          if IsComputationalPauli (c • p) then (1 : ℝ) else 0) * f p := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c _
    split_ifs <;> simp
  calc
    (∑ c : C, if IsComputationalPauli (c • p) then f p else 0) /
          (Fintype.card C : ℝ) =
        ((∑ c : C,
            if IsComputationalPauli (c • p) then (1 : ℝ) else 0) /
          (Fintype.card C : ℝ)) * f p := by
            rw [hfactor]
            ring
    _ = ((Fintype.card {c : C // IsComputationalPauli (c • p)} : ℕ) : ℝ) /
          (Fintype.card C : ℝ) * f p := by rw [hcount]

/-- A basis coordinate is an eigenvector of the averaged channel. -/
theorem finitePauliMeasurementChannel_single
    {K : ℕ} (C : Type*) [Group C] [Fintype C]
    [MulAction C (PauliLabel K)]
    (p : PauliLabel K) :
    finitePauliMeasurementChannel C (Pi.single p 1) =
      finitePauliHitEigenvalue C p • (Pi.single p 1) := by
  classical
  funext q
  rw [finitePauliMeasurementChannel_apply]
  by_cases hqp : q = p
  · subst q
    simp
  · simp [Pi.single_apply, hqp]

/-- For the concrete binary symplectic action, every nonidentity Pauli
coordinate has exact eigenvalue `1 / (2^K + 1)`. -/
theorem finitePauliHitEigenvalue_binarySymplectic
    {K : ℕ} (hK : 0 < K) {p : PauliLabel K} (hp : p ≠ 0) :
    finitePauliHitEigenvalue (binarySymplecticGroup K) p =
      1 / ((2 : ℝ) ^ K + 1) := by
  rw [finitePauliHitEigenvalue]
  change
    ((Fintype.card
        {c : binarySymplecticGroup K // (c.1 p).1 = 0} : ℕ) : ℝ) /
        Fintype.card (binarySymplecticGroup K) =
      1 / ((2 : ℝ) ^ K + 1)
  simpa using
    (uniform_binarySymplectic_z_probability hK
      (⟨p, hp⟩ : NonidentityPauliLabel K))

/-- Fully concrete global-block channel eigenvector identity. -/
theorem binarySymplecticPauliMeasurementChannel_single
    {K : ℕ} (hK : 0 < K) {p : PauliLabel K} (hp : p ≠ 0) :
    finitePauliMeasurementChannel (binarySymplecticGroup K) (Pi.single p 1) =
      (1 / ((2 : ℝ) ^ K + 1)) • (Pi.single p 1) := by
  rw [finitePauliMeasurementChannel_single,
    finitePauliHitEigenvalue_binarySymplectic hK hp]

end TomographyOracleCore
