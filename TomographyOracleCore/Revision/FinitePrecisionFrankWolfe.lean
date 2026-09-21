import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

/-!
# Feasible approximate projection by conditional gradient iteration

This constructs the inner iteration used to approximate a Frobenius
projection. Its only local algorithm input is an approximate linear
minimizer over the feasible set. For density matrices that minimizer is a
normalized rank-one projector returned by a Rayleigh routine. Feasibility
is preserved by rational convex-combination coefficients.

The error bound below is proved from the actual iterate definition; a
global projection or convergence guarantee is not supplied as a premise.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open scoped InnerProductSpace

/-- Rational step size. This operation is executable over the rationals. -/
def fwWeight (n : ℕ) : ℚ := 2 / (n + 2)

theorem fwWeight_cast (n : ℕ) : (fwWeight n : ℝ) = 2 / ((n : ℝ) + 2) := by
  simp [fwWeight]

theorem fwWeight_nonneg (n : ℕ) : (0 : ℝ) ≤ fwWeight n := by
  rw [fwWeight_cast]
  positivity

theorem fwWeight_le_one (n : ℕ) : (fwWeight n : ℝ) ≤ 1 := by
  rw [fwWeight_cast]
  apply (div_le_one₀ (by positivity : 0 < (n : ℝ) + 2)).2
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

/-- Executable version of the iterate for rational vector or matrix
arithmetic. In particular it applies to matrices of rational complex
numbers when the local oracle is executable. -/
def fwRationalIterate {V : Type*} [AddCommGroup V] [Module ℚ V]
    (oracle : V → V) (x0 : V) : ℕ → V
  | 0 => x0
  | n + 1 => (1 - fwWeight n) • fwRationalIterate oracle x0 n +
      fwWeight n • oracle (fwRationalIterate oracle x0 n)

section Module

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Conditional-gradient iterates with rational convex coefficients. -/
noncomputable def fwIterate (oracle : E → E) (x0 : E) : ℕ → E
  | 0 => x0
  | n + 1 => (1 - (fwWeight n : ℝ)) • fwIterate oracle x0 n +
      (fwWeight n : ℝ) • oracle (fwIterate oracle x0 n)

@[simp] theorem fwIterate_zero (oracle : E → E) (x0 : E) :
    fwIterate oracle x0 0 = x0 := rfl

@[simp] theorem fwIterate_succ (oracle : E → E) (x0 : E) (n : ℕ) :
    fwIterate oracle x0 (n + 1) =
      (1 - (fwWeight n : ℝ)) • fwIterate oracle x0 n +
        (fwWeight n : ℝ) • oracle (fwIterate oracle x0 n) := rfl

/-- Every iterate is feasible. In particular no unproved PSD repair is
required when this construction is used on density matrices. -/
theorem fwIterate_mem
    (C : Set E) (hC : Convex ℝ C) (oracle : E → E) (x0 : E)
    (h0 : x0 ∈ C) (horacle : ∀ x ∈ C, oracle x ∈ C) (n : ℕ) :
    fwIterate oracle x0 n ∈ C := by
  induction n with
  | zero => exact h0
  | succ n ih =>
      exact hC ih (horacle _ ih)
        (sub_nonneg.mpr (fwWeight_le_one n)) (fwWeight_nonneg n) (by ring)

end Module

section Hilbert

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact quadratic identity for a feasible convex-combination step. -/
theorem fw_quadratic_identity
    (x v y : E) {a : ℝ} (ha : 0 ≤ a) :
    ‖(1 - a) • x + a • v - y‖ ^ 2 =
      ‖x - y‖ ^ 2 + 2 * a * ⟪x - y, v - x⟫_ℝ +
        a ^ 2 * ‖v - x‖ ^ 2 := by
  have heq : (1 - a) • x + a • v - y = (x - y) + a • (v - x) := by
    simp only [sub_smul, one_smul, smul_sub]
    abel
  rw [heq, norm_add_sq_real, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ha]
  ring

/-- One conditional-gradient step for the squared-distance objective.
The local linear oracle has additive error `delta`, and the feasible set
has squared diameter at most `D2`. -/
theorem fw_quadratic_step
    (x v z y : E) {a delta D2 : ℝ}
    (ha : 0 ≤ a)
    (hlinear : ⟪x - y, v - z⟫_ℝ ≤ delta)
    (hdiam : ‖v - x‖ ^ 2 ≤ D2) :
    ‖(1 - a) • x + a • v - y‖ ^ 2 - ‖z - y‖ ^ 2 ≤
      (1 - a) * (‖x - y‖ ^ 2 - ‖z - y‖ ^ 2) +
        2 * a * delta + a ^ 2 * D2 := by
  have hquadratic := fw_quadratic_identity x v y ha
  have hcompare : ‖z - y‖ ^ 2 = ‖x - y‖ ^ 2 +
      2 * ⟪x - y, z - x⟫_ℝ + ‖z - x‖ ^ 2 := by
    have heq : z - y = (x - y) + (z - x) := by abel
    rw [heq, norm_add_sq_real]
  have hlin : ⟪x - y, v - x⟫_ℝ - ⟪x - y, z - x⟫_ℝ ≤ delta := by
    have heq : v - z = (v - x) - (z - x) := by abel
    simpa only [heq, inner_sub_right] using hlinear
  have hlinMul := mul_le_mul_of_nonneg_left hlin ha
  have hdiamMul := mul_le_mul_of_nonneg_left hdiam (sq_nonneg a)
  have hcomparison := mul_nonneg ha (sq_nonneg ‖z - x‖)
  nlinarith

/-- Conditional-gradient projection error after the first step. The bound
does not require a bound on the initial objective or on the target `y`.
Only the bounded diameter of the feasible set enters. -/
theorem fwIterate_gap_le
    (C : Set E) (hC : Convex ℝ C) (oracle : E → E) (x0 y z : E)
    {delta D2 : ℝ} (hD2 : 0 ≤ D2)
    (h0 : x0 ∈ C) (hz : z ∈ C)
    (horacle : ∀ x ∈ C, oracle x ∈ C)
    (hlinear : ∀ x ∈ C, ⟪x - y, oracle x - z⟫_ℝ ≤ delta)
    (hdiam : ∀ x ∈ C, ∀ v ∈ C, ‖v - x‖ ^ 2 ≤ D2)
    (n : ℕ) :
    ‖fwIterate oracle x0 (n + 1) - y‖ ^ 2 - ‖z - y‖ ^ 2 ≤
      4 * D2 / ((n : ℝ) + 3) + 2 * delta := by
  have hmem (j : ℕ) : fwIterate oracle x0 j ∈ C :=
    fwIterate_mem C hC oracle x0 h0 horacle j
  have hstep (j : ℕ) := fw_quadratic_step
    (fwIterate oracle x0 j) (oracle (fwIterate oracle x0 j)) z y
    (fwWeight_nonneg j) (hlinear _ (hmem j))
    (hdiam _ (hmem j) _ (horacle _ (hmem j)))
  induction n with
  | zero =>
      have hs := hstep 0
      simp only [fwWeight, Nat.cast_zero, zero_add, Nat.cast_ofNat,
        Rat.cast_div, Rat.cast_ofNat, div_self (by norm_num : (2 : ℝ) ≠ 0),
        sub_self, zero_smul, one_smul, zero_mul, one_pow, mul_one,
        fwIterate_zero, one_mul] at hs
      simp only [Nat.cast_zero, zero_add]
      change ‖fwIterate oracle x0 1 - y‖ ^ 2 - ‖z - y‖ ^ 2 ≤ _
      have hfirst : fwIterate oracle x0 1 = oracle x0 := by
        simp [fwIterate, fwWeight]
      rw [hfirst]
      nlinarith
  | succ n ih =>
      have hs := hstep (n + 1)
      have hnonneg : 0 ≤ 1 - (fwWeight (n + 1) : ℝ) :=
        sub_nonneg.mpr (fwWeight_le_one (n + 1))
      have hscaled := mul_le_mul_of_nonneg_left ih hnonneg
      have hscalar :
          (1 - (fwWeight (n + 1) : ℝ)) *
              (4 * D2 / ((n : ℝ) + 3) + 2 * delta) +
            2 * (fwWeight (n + 1) : ℝ) * delta +
            (fwWeight (n + 1) : ℝ) ^ 2 * D2 ≤
          4 * D2 / (((n + 1 : ℕ) : ℝ) + 3) + 2 * delta := by
        rw [fwWeight_cast]
        push_cast
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        field_simp
        nlinarith
      rw [fwIterate_succ]
      linarith

/-- The variational inequality for a convex projection converts objective
error into squared distance from the exact projection. -/
theorem projection_distance_sq_le_objective_gap
    (x p y : E) (hvariational : ⟪y - p, x - p⟫_ℝ ≤ 0) :
    ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖p - y‖ ^ 2 := by
  have heq : x - y = (x - p) - (y - p) := by abel
  have hid := norm_sub_sq_real (x - p) (y - p)
  rw [← heq] at hid
  have hs := real_inner_comm (x - p) (y - p)
  have hn := norm_sub_rev y p
  rw [← hs, hn] at hid
  linarith

/-- Explicit accuracy budget for the inner projection routine. With linear
oracle error at most `epsilon²/4`, `16/epsilon²` iterations suffice for
Frobenius distance `epsilon`, on a set of squared diameter at most two. -/
theorem fwIterate_distance_le
    (C : Set E) (hC : Convex ℝ C) (oracle : E → E) (x0 y p : E)
    {delta epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (h0 : x0 ∈ C) (hp : p ∈ C)
    (horacle : ∀ x ∈ C, oracle x ∈ C)
    (hlinear : ∀ x ∈ C, ⟪x - y, oracle x - p⟫_ℝ ≤ delta)
    (hdiam : ∀ x ∈ C, ∀ v ∈ C, ‖v - x‖ ^ 2 ≤ 2)
    (hvariational : ∀ x ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0)
    (n : ℕ) (hdelta : delta ≤ epsilon ^ 2 / 4)
    (hbudget : 16 ≤ ((n : ℝ) + 3) * epsilon ^ 2) :
    ‖fwIterate oracle x0 (n + 1) - p‖ ≤ epsilon := by
  have hg := fwIterate_gap_le C hC oracle x0 y p (by norm_num : (0 : ℝ) ≤ 2)
    h0 hp horacle hlinear hdiam n
  have hd := projection_distance_sq_le_objective_gap
    (fwIterate oracle x0 (n + 1)) p y
    (hvariational _ (fwIterate_mem C hC oracle x0 h0 horacle _))
  have hden : 0 < (n : ℝ) + 3 := by positivity
  have hfrac : 8 / ((n : ℝ) + 3) ≤ epsilon ^ 2 / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  have hsq : ‖fwIterate oracle x0 (n + 1) - p‖ ^ 2 ≤ epsilon ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg _) hepsilon).1 hsq

/-- The executable rational recursion commutes with any additive embedding
that respects rational scalar multiplication and the local oracle. This
allows the real-Hilbert proof above to certify rational matrix iterates. -/
theorem fwRationalIterate_map
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (embed : V →+ E) (oracleV : V → V) (oracleE : E → E)
    (horacle : ∀ v, embed (oracleV v) = oracleE (embed v))
    (x0 : V) (n : ℕ) :
    embed (fwRationalIterate oracleV x0 n) = fwIterate oracleE (embed x0) n := by
  have hmap (q : ℚ) (v : V) : embed (q • v) = (q : ℝ) • embed v := by
    simpa using map_ratCast_smul embed ℚ ℝ q v
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [fwRationalIterate, fwIterate_succ, map_add, hmap, hmap]
      simp only [Rat.cast_id, Rat.cast_sub, Rat.cast_one, ih, horacle]

end Hilbert

end TomographyOracleCore.Revision.FinitePrecision
