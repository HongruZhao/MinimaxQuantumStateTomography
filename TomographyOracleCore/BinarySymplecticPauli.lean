import TomographyOracleCore.CliffordPauliCounting
import Mathlib.LinearAlgebra.BilinearForm.IsometryEquiv
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.Algebra.CharP.Two

namespace TomographyOracleCore

/-!
# Binary symplectic action on unphased Pauli labels

This module realizes the standard Clifford quotient as the finite group of
linear automorphisms of binary Pauli labels preserving the canonical
symplectic form.  Characteristic-two transvections give an explicit proof
that this group acts transitively on all nonidentity Pauli labels.

Combined with `CliffordPauliCounting`, transitivity proves the exact local
hit probability `1 / (2^K + 1)` without an external counting assumption.
The separate representation theorem identifying physical Clifford
conjugation modulo phases with this binary symplectic action is not asserted
here.
-/

/-- Canonical binary symplectic form
`<(x,z),(x',z')> = sum_i (x_i z'_i + z_i x'_i)`. -/
noncomputable def pauliSymplecticForm (K : ℕ) :
    LinearMap.BilinForm (ZMod 2) (PauliLabel K) :=
  LinearMap.mk₂ (ZMod 2)
    (fun p q ↦ ∑ i, (p.1 i * q.2 i + p.2 i * q.1 i))
    (by
      intros
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intros
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intros
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring)
    (by
      intros
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring)

@[simp] theorem pauliSymplecticForm_apply (K : ℕ)
    (p q : PauliLabel K) :
    pauliSymplecticForm K p q =
      ∑ i, (p.1 i * q.2 i + p.2 i * q.1 i) := rfl

/-- Every element of the binary field is zero or one. -/
theorem zmodTwo_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  have hval := ZMod.val_lt a
  have hv : a.val = 0 ∨ a.val = 1 := by omega
  rcases hv with h | h
  · left
    rw [← ZMod.natCast_zmod_val a, h]
    rfl
  · right
    rw [← ZMod.natCast_zmod_val a, h]
    rfl

/-- Addition of a binary Pauli label to itself is zero. -/
theorem pauliLabel_add_self (K : ℕ) (p : PauliLabel K) : p + p = 0 := by
  apply Prod.ext <;> funext i
  · exact CharTwo.add_self_eq_zero _
  · exact CharTwo.add_self_eq_zero _

/-- The canonical binary symplectic form is alternating. -/
theorem pauliSymplecticForm_self (K : ℕ) (p : PauliLabel K) :
    pauliSymplecticForm K p p = 0 := by
  simp only [pauliSymplecticForm_apply]
  apply Finset.sum_eq_zero
  intro i _
  simpa [mul_comm] using
    CharTwo.add_self_eq_zero (p.1 i * p.2 i)

/-- In characteristic two the canonical symplectic form is symmetric. -/
theorem pauliSymplecticForm_symm (K : ℕ) (p q : PauliLabel K) :
    pauliSymplecticForm K p q = pauliSymplecticForm K q p := by
  simp only [pauliSymplecticForm_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Concrete nondegeneracy: every nonzero Pauli label pairs to one with a
single-coordinate label. -/
theorem exists_pauliSymplectic_pair_one (K : ℕ)
    {p : PauliLabel K} (hp : p ≠ 0) :
    ∃ q : PauliLabel K, pauliSymplecticForm K p q = 1 := by
  classical
  have hcomponent : p.1 ≠ 0 ∨ p.2 ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    exact Prod.ext h.1 h.2
  rcases hcomponent with hx | hz
  · have hxi : ∃ i, p.1 i ≠ 0 := by
      by_contra h
      push Not at h
      apply hx
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hxi
    have hi1 : p.1 i = 1 := by
      rcases zmodTwo_eq_zero_or_one (p.1 i) with h | h
      · exact (hi h).elim
      · exact h
    refine ⟨(0, Pi.single i 1), ?_⟩
    rw [pauliSymplecticForm_apply]
    simp only [Pi.zero_apply]
    rw [Finset.sum_eq_single i]
    · simp [hi1]
    · intro j _ hji
      simp [hji]
    · simp
  · have hzi : ∃ i, p.2 i ≠ 0 := by
      by_contra h
      push Not at h
      apply hz
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hzi
    have hi1 : p.2 i = 1 := by
      rcases zmodTwo_eq_zero_or_one (p.2 i) with h | h
      · exact (hi h).elim
      · exact h
    refine ⟨(Pi.single i 1, 0), ?_⟩
    rw [pauliSymplecticForm_apply]
    simp only [Pi.zero_apply, mul_zero, zero_add]
    rw [Finset.sum_eq_single i]
    · simp [hi1]
    · intro j _ hji
      simp [hji]
    · simp

/-- Any two nonzero Pauli labels have a common vector pairing to one with
both of them. -/
theorem exists_common_pauliSymplectic_pair_one (K : ℕ)
    {p q : PauliLabel K} (hp : p ≠ 0) (hq : q ≠ 0) :
    ∃ a : PauliLabel K,
      pauliSymplecticForm K p a = 1 ∧
      pauliSymplecticForm K q a = 1 := by
  obtain ⟨r, hpr⟩ := exists_pauliSymplectic_pair_one K hp
  by_cases hqr : pauliSymplecticForm K q r = 1
  · exact ⟨r, hpr, hqr⟩
  · have hqr0 : pauliSymplecticForm K q r = 0 := by
      rcases zmodTwo_eq_zero_or_one (pauliSymplecticForm K q r) with h | h
      · exact h
      · exact (hqr h).elim
    obtain ⟨s, hqs⟩ := exists_pauliSymplectic_pair_one K hq
    by_cases hps : pauliSymplecticForm K p s = 1
    · exact ⟨s, hps, hqs⟩
    · have hps0 : pauliSymplecticForm K p s = 0 := by
        rcases zmodTwo_eq_zero_or_one (pauliSymplecticForm K p s) with h | h
        · exact h
        · exact (hps h).elim
      refine ⟨r + s, ?_, ?_⟩
      · rw [map_add, hpr, hps0, add_zero]
      · rw [map_add, hqr0, hqs, zero_add]

/-- Symplectic transvection along `a`. -/
noncomputable def pauliTransvectionLinear (K : ℕ) (a : PauliLabel K) :
    PauliLabel K →ₗ[ZMod 2] PauliLabel K where
  toFun x := x + pauliSymplecticForm K x a • a
  map_add' x y := by
    simp only [map_add, LinearMap.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [map_smul, smul_add, smul_smul]
    rfl

@[simp] theorem pauliTransvectionLinear_apply (K : ℕ)
    (a x : PauliLabel K) :
    pauliTransvectionLinear K a x =
      x + pauliSymplecticForm K x a • a := rfl

/-- A binary symplectic transvection is an involution. -/
theorem pauliTransvectionLinear_involutive (K : ℕ) (a : PauliLabel K) :
    Function.Involutive (pauliTransvectionLinear K a) := by
  intro x
  simp only [pauliTransvectionLinear_apply, map_add, map_smul,
    pauliSymplecticForm_self, zero_smul, add_zero]
  rw [add_assoc, pauliLabel_add_self, add_zero]

/-- Symplectic transvection as a linear equivalence. -/
noncomputable def pauliTransvection (K : ℕ) (a : PauliLabel K) :
    PauliLabel K ≃ₗ[ZMod 2] PauliLabel K :=
  LinearEquiv.ofInvolutive (pauliTransvectionLinear K a)
    (pauliTransvectionLinear_involutive K a)

@[simp] theorem pauliTransvection_apply (K : ℕ)
    (a x : PauliLabel K) :
    pauliTransvection K a x =
      x + pauliSymplecticForm K x a • a := rfl

/-- Transvections preserve the canonical binary symplectic form. -/
theorem pauliTransvection_preserves_form (K : ℕ)
    (a x y : PauliLabel K) :
    pauliSymplecticForm K (pauliTransvection K a x)
        (pauliTransvection K a y) =
      pauliSymplecticForm K x y := by
  simp only [pauliTransvection_apply, map_add, map_smul,
    LinearMap.add_apply, LinearMap.smul_apply,
    pauliSymplecticForm_self, smul_eq_mul, mul_zero, add_zero]
  rw [pauliSymplecticForm_symm K a y]
  let c := pauliSymplecticForm K x a
  let d := pauliSymplecticForm K y a
  change pauliSymplecticForm K x y + c * d + d * c =
    pauliSymplecticForm K x y
  rw [mul_comm c d, add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- If two vectors pair to one, the transvection along their sum sends the
first vector to the second. -/
theorem pauliTransvection_add_map_of_pair_one (K : ℕ)
    {p q : PauliLabel K} (hpq : pauliSymplecticForm K p q = 1) :
    pauliTransvection K (p + q) p = q := by
  rw [pauliTransvection_apply]
  have hcoefficient : pauliSymplecticForm K p (p + q) = 1 := by
    rw [map_add, pauliSymplecticForm_self, hpq, zero_add]
  rw [hcoefficient, one_smul]
  calc
    p + (p + q) = (p + p) + q := by abel
    _ = q := by rw [pauliLabel_add_self, zero_add]

/-- The finite binary symplectic group on unphased `K`-qubit Pauli labels. -/
def binarySymplecticGroup (K : ℕ) :
    Subgroup (PauliLabel K ≃ₗ[ZMod 2] PauliLabel K) where
  carrier := {g | ∀ x y,
    pauliSymplecticForm K (g x) (g y) = pauliSymplecticForm K x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by
    intro f g hf hg x y
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hf, hg]
  inv_mem' := by
    intro g hg x y
    have h := hg (g⁻¹ x) (g⁻¹ y)
    simpa using h.symm

/-- Every binary symplectic transvection belongs to the binary symplectic
group. -/
noncomputable def binarySymplecticTransvection (K : ℕ)
    (a : PauliLabel K) : binarySymplecticGroup K :=
  ⟨pauliTransvection K a, pauliTransvection_preserves_form K a⟩

noncomputable instance binarySymplecticGroupFintype (K : ℕ) :
    Fintype (binarySymplecticGroup K) :=
  Fintype.ofInjective
    (fun g : binarySymplecticGroup K ↦
      fun p : PauliLabel K ↦ g.1 p)
    (by
      intro g h hfun
      apply Subtype.ext
      apply LinearEquiv.ext
      intro p
      exact congrFun hfun p)

/-- Natural action of the binary symplectic group on all Pauli labels. -/
instance binarySymplecticGroupMulAction (K : ℕ) :
    MulAction (binarySymplecticGroup K) (PauliLabel K) :=
  MulAction.compHom (PauliLabel K) (binarySymplecticGroup K).subtype

@[simp] theorem binarySymplecticGroup_smul_apply (K : ℕ)
    (g : binarySymplecticGroup K) (p : PauliLabel K) :
    g • p = g.1 p := rfl

/-- The nonzero labels are invariant under the binary symplectic action. -/
instance binarySymplecticGroupNonidentityMulAction (K : ℕ) :
    MulAction (binarySymplecticGroup K) (NonidentityPauliLabel K) where
  smul g p := ⟨g.1 p.1, by
    intro h
    apply p.2
    apply g.1.injective
    simpa using h⟩
  one_smul p := by apply Subtype.ext; rfl
  mul_smul g h p := by apply Subtype.ext; rfl

@[simp] theorem binarySymplecticGroup_nonidentity_smul_val (K : ℕ)
    (g : binarySymplecticGroup K) (p : NonidentityPauliLabel K) :
    (g • p).1 = g.1 p.1 := rfl

/-- Two explicit symplectic transvections send any nonzero Pauli label to
any other one. -/
theorem binarySymplecticGroup_exists_smul_eq (K : ℕ)
    (p q : NonidentityPauliLabel K) :
    ∃ g : binarySymplecticGroup K, g • p = q := by
  obtain ⟨a, hpa, hqa⟩ :=
    exists_common_pauliSymplectic_pair_one K p.2 q.2
  have haq : pauliSymplecticForm K a q.1 = 1 := by
    rw [pauliSymplecticForm_symm]
    exact hqa
  let g₁ := binarySymplecticTransvection K (p.1 + a)
  let g₂ := binarySymplecticTransvection K (a + q.1)
  refine ⟨g₂ * g₁, ?_⟩
  apply Subtype.ext
  change pauliTransvection K (a + q.1)
      (pauliTransvection K (p.1 + a) p.1) = q.1
  rw [pauliTransvection_add_map_of_pair_one K hpa,
    pauliTransvection_add_map_of_pair_one K haq]

/-- The binary symplectic (Clifford quotient) action is transitive on all
nonidentity Pauli labels. -/
instance binarySymplecticGroup_isPretransitive (K : ℕ) :
    MulAction.IsPretransitive (binarySymplecticGroup K)
      (NonidentityPauliLabel K) where
  exists_smul_eq p q := binarySymplecticGroup_exists_smul_eq K p q

/-- Fully concrete version of the local Clifford Pauli counting result for
the binary symplectic quotient. -/
theorem uniform_binarySymplectic_z_probability
    {K : ℕ} (hK : 0 < K) (Q : NonidentityPauliLabel K) :
    ((Fintype.card
        {c : binarySymplecticGroup K // (c • Q).1.1 = 0} : ℕ) : ℝ) /
        Fintype.card (binarySymplecticGroup K) =
      1 / ((2 : ℝ) ^ K + 1) :=
  uniform_transitive_pauli_action_z_probability hK Q

end TomographyOracleCore
