import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace TomographyOracleCore

/-!
# Finite counting behind the local-Clifford Pauli probability

An unphased `K`-qubit Pauli label is a pair of binary words `(x,z)`.  The
nonidentity labels therefore number `4^K - 1`, while the nonidentity labels
diagonal in the computational basis, `(0,z)` with `z ≠ 0`, number `2^K - 1`.

This module also proves that a uniform element of any finite group acting
transitively on the nonidentity labels sends a fixed label into the diagonal
subset with probability exactly `1 / (2^K + 1)`.  Consequently, after a
concrete Clifford implementation proves that its conjugation action is
transitive, no further probability or cardinality argument is needed.

No representation of Clifford operators by matrices is asserted here.
-/

/-- A binary word indexing one half of an unphased Pauli label. -/
abbrev PauliBinaryWord (K : ℕ) := Fin K → ZMod 2

/-- An unphased `K`-qubit Pauli label `(x,z)`. -/
abbrev PauliLabel (K : ℕ) := PauliBinaryWord K × PauliBinaryWord K

/-- The finite type of nonidentity unphased `K`-qubit Pauli labels. -/
abbrev NonidentityPauliLabel (K : ℕ) := {p : PauliLabel K // p ≠ 0}

/-- The nonidentity Pauli labels diagonal in the computational basis. -/
abbrev NonidentityZPauliLabel (K : ℕ) :=
  {p : NonidentityPauliLabel K // p.1.1 = 0}

/-- A nonzero `z` word is the same datum as a nonidentity diagonal Pauli
label `(0,z)`. -/
noncomputable def nonidentityZPauliLabelEquiv (K : ℕ) :
    {z : PauliBinaryWord K // z ≠ 0} ≃ NonidentityZPauliLabel K where
  toFun z := ⟨⟨(0, z.1), by
    intro h
    exact z.2 (congrArg Prod.snd h)⟩, rfl⟩
  invFun p := ⟨p.1.1.2, by
    intro hz
    apply p.1.2
    apply Prod.ext
    · exact p.2
    · exact hz⟩
  left_inv z := by ext i; rfl
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.symm
    · rfl

/-- There are exactly `4^K - 1` nonidentity unphased Pauli labels. -/
theorem card_nonidentityPauliLabel (K : ℕ) :
    Fintype.card (NonidentityPauliLabel K) = 4 ^ K - 1 := by
  simpa [NonidentityPauliLabel, PauliLabel, PauliBinaryWord, ← mul_pow] using
    (show Fintype.card {p : PauliLabel K // p ≠ 0} =
        Fintype.card (PauliLabel K) - 1 from
      Set.card_ne_eq (0 : PauliLabel K))

/-- There are exactly `2^K - 1` nonidentity computational-basis diagonal
Pauli labels. -/
theorem card_nonidentityZPauliLabel (K : ℕ) :
    Fintype.card (NonidentityZPauliLabel K) = 2 ^ K - 1 := by
  rw [Fintype.card_congr (nonidentityZPauliLabelEquiv K).symm]
  simpa [PauliBinaryWord] using
    (Set.card_ne_eq (0 : PauliBinaryWord K))

/-- The quotient of the two Pauli-label counts is the local shadow-channel
factor `1 / (2^K + 1)`. -/
theorem nonidentityZPauli_ratio
    {K : ℕ} (hK : 0 < K) :
    ((2 : ℝ) ^ K - 1) / ((4 : ℝ) ^ K - 1) =
      1 / ((2 : ℝ) ^ K + 1) := by
  have hpow : (1 : ℝ) < (2 : ℝ) ^ K :=
    one_lt_pow₀ (by norm_num) hK.ne'
  have hne : (2 : ℝ) ^ K - 1 ≠ 0 := sub_ne_zero.mpr hpow.ne'
  rw [show (4 : ℝ) ^ K - 1 =
      ((2 : ℝ) ^ K - 1) * ((2 : ℝ) ^ K + 1) by
    rw [show (4 : ℝ) ^ K = ((2 : ℝ) ^ K) ^ 2 by
      rw [pow_two, ← mul_pow]
      norm_num]
    ring]
  field_simp

section UniformOrbit

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω]
  [DecidableEq Ω] [MulAction G Ω]

/-- The fiber over `y` of the orbit map `g ↦ g • x`. -/
abbrev ActionFiber (x y : Ω) := {g : G // g • x = y}

/-- Left multiplication transports an orbit-map fiber to any other fiber
whose target is obtained by the same group element. -/
def actionFiberEquivOfSends (x : Ω) {y z : Ω}
    (h : G) (hh : h • y = z) :
    ActionFiber (G := G) x y ≃ ActionFiber (G := G) x z where
  toFun g := ⟨h * g.1, by rw [mul_smul, g.2, hh]⟩
  invFun g := ⟨h⁻¹ * g.1, by rw [mul_smul, g.2, ← hh, inv_smul_smul]⟩
  left_inv g := by ext; simp
  right_inv g := by ext; simp

/-- Every fiber of a transitive finite group action has the same size. -/
theorem actionFiber_card_eq [MulAction.IsPretransitive G Ω]
    (x y z : Ω) :
    Fintype.card (ActionFiber (G := G) x y) =
      Fintype.card (ActionFiber (G := G) x z) := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G y z
  exact Fintype.card_congr (actionFiberEquivOfSends x h hh)

/-- Partition a group-action event by the value of the orbit map. -/
def actionEventEquivSigma (x : Ω) (A : Finset Ω) :
    {g : G // g • x ∈ A} ≃
      Σ y : {y : Ω // y ∈ A}, ActionFiber (G := G) x y.1 where
  toFun g := ⟨⟨g.1 • x, g.2⟩, ⟨g.1, rfl⟩⟩
  invFun gy := ⟨gy.2.1, by rw [gy.2.2]; exact gy.1.2⟩
  left_inv g := by ext; rfl
  right_inv gy := by
    rcases gy with ⟨⟨y, hy⟩, ⟨g, hg⟩⟩
    cases hg
    rfl

/-- Partition the whole acting group by all values of the orbit map. -/
def actionEquivSigmaFibers (x : Ω) :
    G ≃ Σ y : Ω, ActionFiber (G := G) x y where
  toFun g := ⟨g • x, ⟨g, rfl⟩⟩
  invFun gy := gy.2.1
  left_inv g := rfl
  right_inv gy := by
    rcases gy with ⟨y, ⟨g, hg⟩⟩
    subst y
    rfl

/-- A transitive action hits a finite target set `A` in exactly
`|A| * |stabilizer fiber|` group elements. -/
theorem actionEvent_card [MulAction.IsPretransitive G Ω]
    (x : Ω) (A : Finset Ω) :
    Fintype.card {g : G // g • x ∈ A} =
      A.card * Fintype.card (ActionFiber (G := G) x x) := by
  rw [Fintype.card_congr (actionEventEquivSigma x A), Fintype.card_sigma]
  simp_rw [actionFiber_card_eq x _ x]
  simp

/-- Orbit-stabilizer, in the exact fiber form used for uniform counting. -/
theorem action_card [MulAction.IsPretransitive G Ω] (x : Ω) :
    Fintype.card G =
      Fintype.card Ω * Fintype.card (ActionFiber (G := G) x x) := by
  rw [Fintype.card_congr (actionEquivSigmaFibers x), Fintype.card_sigma]
  simp_rw [actionFiber_card_eq x _ x]
  simp

/-- Under the uniform distribution on a finite group, a transitive action
sends a fixed point into `A` with probability `|A| / |Ω|`. -/
theorem uniform_action_event_ratio [MulAction.IsPretransitive G Ω]
    (x : Ω) (A : Finset Ω) :
    ((Fintype.card {g : G // g • x ∈ A} : ℕ) : ℝ) /
        Fintype.card G =
      (A.card : ℝ) / Fintype.card Ω := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := by positivity
  have hΩnat : 0 < Fintype.card Ω := Fintype.card_pos_iff.mpr ⟨x⟩
  have hΩ : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast hΩnat.ne'
  have hSnat : 0 < Fintype.card (ActionFiber (G := G) x x) :=
    Fintype.card_pos_iff.mpr ⟨⟨1, one_smul G x⟩⟩
  have hS : (Fintype.card (ActionFiber (G := G) x x) : ℝ) ≠ 0 := by
    exact_mod_cast hSnat.ne'
  rw [actionEvent_card (G := G) (x := x) A,
    action_card (G := G) (Ω := Ω) x]
  push_cast
  field_simp [hS]

end UniformOrbit

/-- The finite set of nonidentity computational-basis diagonal Pauli
labels. -/
noncomputable def nonidentityZPauliFinset (K : ℕ) :
    Finset (NonidentityPauliLabel K) :=
  Finset.univ.filter fun p ↦ p.1.1 = 0

theorem card_nonidentityZPauliFinset (K : ℕ) :
    (nonidentityZPauliFinset K).card = 2 ^ K - 1 := by
  rw [← Fintype.card_coe]
  simpa [nonidentityZPauliFinset, NonidentityZPauliLabel] using
    card_nonidentityZPauliLabel K

/-- Exact local-Clifford counting interface.  Any concrete finite group
whose action on nonidentity Pauli labels is transitive has the desired
computational-basis hit probability `1 / (2^K + 1)`.

For the Clifford application, the sole remaining local premise is the
instance `MulAction.IsPretransitive C (NonidentityPauliLabel K)`. -/
theorem uniform_transitive_pauli_action_z_probability
    {K : ℕ} (hK : 0 < K)
    {C : Type*} [Group C] [Fintype C]
    [MulAction C (NonidentityPauliLabel K)]
    [MulAction.IsPretransitive C (NonidentityPauliLabel K)]
    (Q : NonidentityPauliLabel K) :
    ((Fintype.card {c : C // (c • Q).1.1 = 0} : ℕ) : ℝ) /
        Fintype.card C =
      1 / ((2 : ℝ) ^ K + 1) := by
  let A := nonidentityZPauliFinset K
  have huniform := uniform_action_event_ratio (G := C) (x := Q) A
  have hA : (A.card : ℝ) = (2 : ℝ) ^ K - 1 := by
    rw [show A.card = 2 ^ K - 1 by
      simpa [A] using card_nonidentityZPauliFinset K]
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_num
  have htotal : (Fintype.card (NonidentityPauliLabel K) : ℝ) =
      (4 : ℝ) ^ K - 1 := by
    rw [card_nonidentityPauliLabel]
    rw [Nat.cast_sub (Nat.one_le_pow K 4 (by norm_num))]
    norm_num
  rw [show Fintype.card {c : C // (c • Q).1.1 = 0} =
      Fintype.card {c : C // c • Q ∈ A} by
        apply Fintype.card_congr
        apply Equiv.subtypeEquivProp
        funext c
        simp [A, nonidentityZPauliFinset]]
  rw [huniform, hA, htotal]
  exact nonidentityZPauli_ratio hK

/-- The local Clifford hit factor lies in the unit interval. -/
theorem localCliffordHitFactor_mem_Icc (K : ℕ) :
    0 ≤ (((2 : ℝ) ^ K + 1)⁻¹) ∧
      (((2 : ℝ) ^ K + 1)⁻¹) ≤ 1 := by
  constructor
  · positivity
  · apply inv_le_one_of_one_le₀
    have hpow : 0 ≤ (2 : ℝ) ^ K := by positivity
    linarith

/-- Since the local hit factor is at most one, replacing the actual number
of nontrivial second-layer blocks by the total block count only decreases
the conditional hit probability. -/
theorem localCliffordHitFactor_pow_floor
    {K w m : ℕ} (hw : w ≤ m) :
    ((((2 : ℝ) ^ K + 1)⁻¹) ^ m) ≤
      ((((2 : ℝ) ^ K + 1)⁻¹) ^ w) := by
  exact pow_le_pow_of_le_one
    (localCliffordHitFactor_mem_Icc K).1
    (localCliffordHitFactor_mem_Icc K).2 hw

/-- A finite average preserves a pointwise lower bound. -/
theorem finite_average_ge_of_forall
    {U : Type*} [Fintype U] [Nonempty U]
    {a : ℝ} {f : U → ℝ} (h : ∀ u, a ≤ f u) :
    a ≤ (∑ u, f u) / Fintype.card U := by
  have hsum : (∑ _u : U, a) ≤ ∑ u : U, f u := by
    exact Finset.sum_le_sum fun u _ ↦ h u
  have hcard : 0 < (Fintype.card U : ℝ) := by positivity
  apply (le_div_iff₀ hcard).2
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

/-- Exact averaging step in Cho--Kim's two-layer lower bound.  If `w u` is
the number of nontrivial second-layer blocks after the first-layer choice
`u`, then `w u ≤ n/K` alone forces the averaged conditional probability
above `(2^K+1)^(-n/K)`. -/
theorem averaged_localCliffordHit_ge_floor
    {U : Type*} [Fintype U] [Nonempty U]
    {n K : ℕ} (w : U → ℕ) (hw : ∀ u, w u ≤ n / K) :
    ((((2 : ℝ) ^ K + 1)⁻¹) ^ (n / K)) ≤
      (∑ u, (((2 : ℝ) ^ K + 1)⁻¹) ^ w u) /
        Fintype.card U := by
  apply finite_average_ge_of_forall
  intro u
  exact localCliffordHitFactor_pow_floor (hw u)

end TomographyOracleCore
