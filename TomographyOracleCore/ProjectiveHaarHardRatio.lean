import TomographyOracleCore.ProjectiveHaarBlockLaw
import TomographyOracleCore.HaarBornScoreMoments

namespace TomographyOracleCore

open MeasureTheory
open scoped BigOperators

noncomputable section

/-!
# Scalar ingredients for the hard-reference Haar ratio

This module records two unconditional pieces of the arbitrary-POVM
one-copy calculation.  The first is the exact centered quadratic moment of
a complex-projective Haar direction.  The second is the finite weighted
Cauchy inequality used to pass from rank-one effects to a general positive
effect by spectral decomposition.

The only analytic identity not proved here is the *coupled* block ratio
moment on `ℂ² ⊕ ℂᵏ`: the normalized tail direction must be independent of
the two-coordinate head mass.  Neither theorem below assumes that identity.
-/

/-- Exact projective second moment for a centered Hermitian quadratic form:
`E[(u* A u)²] = tr(A²)/(k(k+1))` for a Haar unit vector in `ℂᵏ`.

The matrix `P` is the rank-one projector `|u⟩⟨u|`; Hermiticity makes the
trace pairing real, and the trace-zero premise removes the scalar term in
the projective two-copy moment. -/
theorem integral_complexProjectiveHaar_centered_quadratic_sq
    (k : ℕ) (hk : 1 ≤ k)
    (A : Matrix (Fin k) (Fin k) ℂ)
    (hA : A.IsHermitian) (htrace : A.trace = 0) :
    (∫ P, ((A * P).trace.re) ^ 2
        ∂complexProjectiveHaarLaw (Fin k)) =
      (A * A).trace.re / ((k : ℝ) * ((k : ℝ) + 1)) := by
  letI : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp (by omega)
  rw [show (fun P : Matrix (Fin k) (Fin k) ℂ ↦
      ((A * P).trace.re) ^ 2) =
      (fun P ↦ (A * P).trace.re * (A * P).trace.re) by
    funext P
    ring]
  rw [integral_complexProjectiveHaar_trace_mul_two_re (Fin k) A A hA hA]
  have h := congrArg Complex.re
    (card_mul_integral_complexProjectiveHaar_trace_mul_two (Fin k) A A)
  rw [htrace] at h
  simp only [zero_mul, zero_add] at h
  have hk0 : (k : ℝ) ≠ 0 := by positivity
  have hk10 : (k : ℝ) + 1 ≠ 0 := by positivity
  rw [Complex.div_re] at h
  norm_num [Fintype.card_fin, Complex.normSq_apply] at h
  field_simp [hk0, hk10] at h ⊢
  nlinarith

/-- Weighted Cauchy (Engel form), in precisely the form used for a positive
effect's spectral decomposition.  Strictly positive weights are enough
because zero eigenvalues are omitted from the spectral support. -/
theorem weighted_sq_sum_div_le
    {I : Type*} [DecidableEq I] (s : Finset I)
    (w q δ : I → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) (hq : ∀ i ∈ s, 0 < q i) :
    ((∑ i ∈ s, w i * δ i) ^ 2) / (∑ i ∈ s, w i * q i) ≤
      ∑ i ∈ s, w i * (δ i) ^ 2 / q i := by
  have h := Finset.sq_sum_div_le_sum_sq_div s
    (fun i ↦ w i * δ i) (g := fun i ↦ w i * q i)
    (fun i hi ↦ mul_pos (hw i hi) (hq i hi))
  rw [show (∑ i ∈ s, w i * δ i) =
      ∑ i ∈ s, (fun i ↦ w i * δ i) i by rfl,
    show (∑ i ∈ s, w i * q i) =
      ∑ i ∈ s, (fun i ↦ w i * q i) i by rfl]
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i hi
  have hw0 : w i ≠ 0 := (hw i hi).ne'
  have hq0 : q i ≠ 0 := (hq i hi).ne'
  field_simp [hw0, hq0]

end

end TomographyOracleCore
