import Mathlib.RepresentationTheory.Basic
import TomographyOracleCore.PeriodicCliffordFourthSectorAveragingCriterion

namespace TomographyOracleCore

noncomputable section

/-!
# Finite-group Hilbert--Schmidt twirls

This module isolates the group-theoretic part of the physical fourth-copy
Clifford average.  A finite-dimensional unitary conjugation representation
is used only through its exact inverse-adjoint pairing identity.  Under that
interface, its uniform group average is Hilbert--Schmidt self-adjoint, fixes
every invariant vector, and has range in the common fixed space.

The statements are generic in the finite group and matrix index.  The later
Clifford specialization only has to construct the representation and verify
the displayed inverse-adjoint identity.
-/

/-- Hilbert--Schmidt pairing is conjugate-linear in its first argument. -/
theorem qubitFourthComplexHilbertSchmidt_smul_left
    {ι : Type*} [Fintype ι]
    (c : ℂ) (A B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt (c • A) B =
      star c * qubitFourthComplexHilbertSchmidt A B := by
  simp [qubitFourthComplexHilbertSchmidt,
    Matrix.conjTranspose_smul]

/-- Finite sums can be pulled through the conjugate-linear first argument
of the Hilbert--Schmidt pairing. -/
theorem qubitFourthComplexHilbertSchmidt_sum_left
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : κ → Matrix ι ι ℂ) (B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt (∑ k, f k) B =
      ∑ k, qubitFourthComplexHilbertSchmidt (f k) B := by
  unfold qubitFourthComplexHilbertSchmidt
  rw [Matrix.conjTranspose_sum, Matrix.sum_mul, Matrix.trace_sum]

/-- Exact Hilbert--Schmidt adjoint identity for ordinary matrix
conjugation.  No invertibility premise is needed: the adjoint of
`X ↦ U X Uᴴ` is `X ↦ Uᴴ X U`. -/
theorem qubitFourthComplexHilbertSchmidt_conjugation_adjoint
    {ι : Type*} [Fintype ι]
    (U A B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A
        ((U * B) * U.conjTranspose) =
      qubitFourthComplexHilbertSchmidt
        ((U.conjTranspose * A) * U) B := by
  unfold qubitFourthComplexHilbertSchmidt
  calc
    (A.conjTranspose * ((U * B) * U.conjTranspose)).trace =
        (((U * B) * U.conjTranspose) * A.conjTranspose).trace :=
      Matrix.trace_mul_comm _ _
    _ = (U * (B * U.conjTranspose * A.conjTranspose)).trace := by
      simp only [mul_assoc]
    _ = ((B * U.conjTranspose * A.conjTranspose) * U).trace :=
      Matrix.trace_mul_comm _ _
    _ = (B * (U.conjTranspose * A.conjTranspose * U)).trace := by
      simp only [mul_assoc]
    _ = ((U.conjTranspose * A.conjTranspose * U) * B).trace :=
      Matrix.trace_mul_comm _ _
    _ = (((U.conjTranspose * A) * U).conjTranspose * B).trace := by
      simp [Matrix.conjTranspose_mul, mul_assoc]

/-- The normalized average of a representation of a finite group. -/
def finiteGroupHilbertSchmidtTwirl
    {G V : Type*} [Group G] [Fintype G]
    [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ G V) : V →ₗ[ℂ] V :=
  ((Fintype.card G : ℂ)⁻¹) • Representation.norm ρ

@[simp]
theorem finiteGroupHilbertSchmidtTwirl_apply
    {G V : Type*} [Group G] [Fintype G]
    [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ G V) (X : V) :
    finiteGroupHilbertSchmidtTwirl ρ X =
      ((Fintype.card G : ℂ)⁻¹) • ∑ g : G, ρ g X := by
  simp [finiteGroupHilbertSchmidtTwirl, Representation.norm,
    LinearMap.smul_apply, LinearMap.sum_apply]

/-- The group average fixes every vector already fixed by the whole
representation. -/
theorem finiteGroupHilbertSchmidtTwirl_eq_self_of_fixed
    {G V : Type*} [Group G] [Fintype G]
    [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ G V) (X : V)
    (hfixed : ∀ g : G, ρ g X = X) :
    finiteGroupHilbertSchmidtTwirl ρ X = X := by
  rw [finiteGroupHilbertSchmidtTwirl_apply]
  simp_rw [hfixed]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card G ≠ 0)
  simp [hcard]

/-- Every output of the group average is fixed by every group element. -/
theorem finiteGroupHilbertSchmidtTwirl_range_fixed
    {G V : Type*} [Group G] [Fintype G]
    [AddCommMonoid V] [Module ℂ V]
    (ρ : Representation ℂ G V) (g : G) (X : V) :
    ρ g (finiteGroupHilbertSchmidtTwirl ρ X) =
      finiteGroupHilbertSchmidtTwirl ρ X := by
  change ρ g (((Fintype.card G : ℂ)⁻¹) •
      Representation.norm ρ X) = _
  rw [map_smul, Representation.self_norm_apply]
  rfl

/-- If the representation action satisfies the inverse-adjoint identity
characteristic of unitary conjugation, then its uniform finite-group twirl
is self-adjoint for the Hilbert--Schmidt pairing. -/
theorem finiteGroupHilbertSchmidtTwirl_selfAdjoint
    {G ι : Type*} [Group G] [Fintype G]
    [Fintype ι]
    (ρ : Representation ℂ G (Matrix ι ι ℂ))
    (hinverseAdjoint : ∀ g : G, ∀ A B,
      qubitFourthComplexHilbertSchmidt A (ρ g B) =
        qubitFourthComplexHilbertSchmidt (ρ (g⁻¹) A) B)
    (A B : Matrix ι ι ℂ) :
    qubitFourthComplexHilbertSchmidt A
        (finiteGroupHilbertSchmidtTwirl ρ B) =
      qubitFourthComplexHilbertSchmidt
        (finiteGroupHilbertSchmidtTwirl ρ A) B := by
  let c : ℂ := (Fintype.card G : ℂ)⁻¹
  have hcstar : star c = c := by
    simp [c]
  have hinv :
      (∑ g : G,
        qubitFourthComplexHilbertSchmidt (ρ (g⁻¹) A) B) =
      ∑ g : G, qubitFourthComplexHilbertSchmidt (ρ g A) B := by
    simpa using Equiv.sum_comp (Equiv.inv G)
      (fun g : G ↦ qubitFourthComplexHilbertSchmidt (ρ g A) B)
  calc
    qubitFourthComplexHilbertSchmidt A
        (finiteGroupHilbertSchmidtTwirl ρ B) =
        c * ∑ g : G,
          qubitFourthComplexHilbertSchmidt A (ρ g B) := by
      rw [finiteGroupHilbertSchmidtTwirl_apply,
        qubitFourthComplexHilbertSchmidt_smul_right,
        qubitFourthComplexHilbertSchmidt_sum_right]
    _ = c * ∑ g : G,
        qubitFourthComplexHilbertSchmidt (ρ (g⁻¹) A) B := by
      congr 1
      apply Finset.sum_congr rfl
      intro g _hg
      exact hinverseAdjoint g A B
    _ = c * ∑ g : G,
        qubitFourthComplexHilbertSchmidt (ρ g A) B := by rw [hinv]
    _ = qubitFourthComplexHilbertSchmidt
        (finiteGroupHilbertSchmidtTwirl ρ A) B := by
      rw [finiteGroupHilbertSchmidtTwirl_apply,
        qubitFourthComplexHilbertSchmidt_smul_left,
        qubitFourthComplexHilbertSchmidt_sum_left, hcstar]

/-! ## Direct specialization to the thirty fourth-copy sectors -/

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-- Exact finite-group interface sufficient to identify a physical
fourth-copy twirl with the certified thirty-sector Weingarten projector. -/
theorem qubitFourthFiniteGroupTwirl_eq_sectorSynthesis
    {G : Type*} [Group G] [Fintype G]
    {r : ℕ} (hr : 3 ≤ r)
    (ρ : Representation ℂ G
      (Matrix (QubitFourthBlockReplicaIndex r)
        (QubitFourthBlockReplicaIndex r) ℂ))
    (hinverseAdjoint : ∀ g : G, ∀ A B,
      qubitFourthComplexHilbertSchmidt A (ρ g B) =
        qubitFourthComplexHilbertSchmidt (ρ (g⁻¹) A) B)
    (hsectorInvariant : ∀ g : G, ∀ l : Fin 30,
      ρ g (qubitFourthSectorR r l) = qubitFourthSectorR r l)
    (hrange : ∀ X, ∃ c : Fin 30 → ℂ,
      finiteGroupHilbertSchmidtTwirl ρ X =
        qubitFourthSectorCombination r c) :
    finiteGroupHilbertSchmidtTwirl ρ =
      qubitFourthSectorSynthesisCandidate r := by
  apply qubitFourthSectorAverage_eq_synthesis_of_selfAdjoint_fixed_range
    hr (finiteGroupHilbertSchmidtTwirl ρ)
  · exact finiteGroupHilbertSchmidtTwirl_selfAdjoint ρ
      hinverseAdjoint
  · intro l
    exact finiteGroupHilbertSchmidtTwirl_eq_self_of_fixed ρ
      (qubitFourthSectorR r l) (fun g ↦ hsectorInvariant g l)
  · exact hrange

end

end TomographyOracleCore
