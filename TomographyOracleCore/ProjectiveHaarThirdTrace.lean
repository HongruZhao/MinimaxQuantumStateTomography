import TomographyOracleCore.ProjectiveHaarThirdMoments

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator Pointwise

noncomputable section

/-!
# The mixed trace contraction of the third projective Haar moment

This module contracts the coordinate formula proved in
`ProjectiveHaarThirdMoments` against three arbitrary complex matrices.  The
result is the usual six-term order-three trace polynomial.  No tensor-moment
formula is assumed here.
-/

section ThirdTraceContraction

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

private theorem sum_three_rotate {α : Type*} [Fintype α]
    (f : α → α → α → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  calc
    _ = ∑ b, ∑ a, ∑ c, f a b c := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      exact Finset.sum_comm

private theorem sum_three_reverse {α : Type*} [Fintype α]
    (f : α → α → α → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ b, ∑ a, f a b c := by
  calc
    _ = ∑ a, ∑ c, ∑ b, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ b, f a b c := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro c hc
      exact Finset.sum_comm

private theorem sum_three_rotateBack {α : Type*} [Fintype α]
    (f : α → α → α → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ c, ∑ a, ∑ b, f a b c := by
  calc
    _ = ∑ b, ∑ c, ∑ a, f a b c := sum_three_rotate f
    _ = _ := sum_three_rotate (fun b c a ↦ f a b c)

private theorem thirdTraceKernelTerm_identity (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        (if b = a ∧ d = c ∧ f = e then (1 : ℂ) else 0)) =
      C.trace * B.trace * A.trace := by
  simp_rw [← complex_truthIndicator_mul]
  simp
  simpa [Matrix.trace, Matrix.diag_apply, mul_assoc, mul_comm, mul_left_comm,
    Finset.sum_mul, Finset.mul_sum] using
      (sum_three_reverse
        (f := fun a b c ↦ A a a * (B b b * C c c)))

private theorem thirdTraceKernelTerm_swapLast (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        (if b = a ∧ d = e ∧ f = c then (1 : ℂ) else 0)) =
      (B * C).trace * A.trace := by
  simp_rw [← complex_truthIndicator_mul]
  simp
  simpa [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_assoc,
    mul_comm, mul_left_comm, Finset.sum_mul, Finset.mul_sum] using
      (sum_three_rotate
        (f := fun a c e ↦ A a a * (B c e * C e c)))

private theorem thirdTraceKernelTerm_swapFirst (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        (if b = c ∧ d = a ∧ f = e then (1 : ℂ) else 0)) =
      (A * B).trace * C.trace := by
  simp_rw [← complex_truthIndicator_mul]
  simp
  simpa [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_assoc,
    mul_comm, mul_left_comm, Finset.sum_mul, Finset.mul_sum] using
      (sum_three_rotateBack
        (f := fun a b c ↦ A a b * B b a * C c c))

private theorem thirdTraceKernelTerm_cycleForward (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        (if b = c ∧ d = e ∧ f = a then (1 : ℂ) else 0)) =
      (A * (B * C)).trace := by
  simp_rw [← complex_truthIndicator_mul]
  simp
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_assoc,
    mul_comm, mul_left_comm, Finset.sum_mul, Finset.mul_sum]

private theorem thirdTraceKernelTerm_cycleBackward (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        (if b = e ∧ d = a ∧ f = c then (1 : ℂ) else 0)) =
      (A * (C * B)).trace := by
  simp_rw [← complex_truthIndicator_mul]
  simp
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_assoc,
    mul_comm, mul_left_comm, Finset.sum_mul, Finset.mul_sum]

private theorem thirdTraceKernelTerm_swapOuter (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        (if b = e ∧ d = c ∧ f = a then (1 : ℂ) else 0)) =
      (A * C).trace * B.trace := by
  simp_rw [← complex_truthIndicator_mul]
  simp
  simpa [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mul_assoc,
    mul_comm, mul_left_comm, Finset.sum_mul, Finset.mul_sum] using
      (sum_three_rotateBack
        (f := fun a b c ↦ A a b * B c c * C b a))

/-- The six traces obtained by contracting the symmetric order-three tensor
against three matrices. -/
noncomputable def complexProjectiveThirdTraceNumerator
    (A B C : Matrix ι ι ℂ) : ℂ :=
  A.trace * B.trace * C.trace +
    A.trace * (B * C).trace +
    (A * B).trace * C.trace +
    (A * (B * C)).trace +
    (A * (C * B)).trace +
    (A * C).trace * B.trace

set_option maxHeartbeats 1200000 in
/-- Pure finite-dimensional algebra: the explicit six-index coordinate
kernel contracts to the six-term trace numerator. -/
theorem complexProjectiveThirdMomentKernel_trace_contract
    (A B C : Matrix ι ι ℂ) :
    (∑ a : ι, ∑ b : ι, ∑ c : ι, ∑ d : ι, ∑ e : ι, ∑ f : ι,
      A a b * B c d * C e f *
        complexProjectiveThirdMomentKernel ι b a d c f e) =
      complexProjectiveThirdTraceNumerator A B C := by
  simp only [complexProjectiveThirdMomentKernel, mul_add,
    Finset.sum_add_distrib]
  rw [thirdTraceKernelTerm_identity, thirdTraceKernelTerm_swapLast,
    thirdTraceKernelTerm_swapFirst, thirdTraceKernelTerm_cycleForward,
    thirdTraceKernelTerm_cycleBackward, thirdTraceKernelTerm_swapOuter]
  dsimp [complexProjectiveThirdTraceNumerator]
  ring

/-- A triple coordinate product is integrable under the concrete normalized
projective Haar law. -/
theorem integrable_complexProjectiveHaar_coordinateThirdMoment
    (i j k l p q : ι) :
    Integrable
      (fun B : Matrix ι ι ℂ ↦ B i j * B k l * B p q)
      (complexProjectiveHaarLaw ι) := by
  have hg : Continuous
      (fun B : Matrix ι ι ℂ ↦ B i j * B k l * B p q) := by
    fun_prop
  unfold complexProjectiveHaarLaw
  apply (integrable_map_measure hg.aestronglyMeasurable
    (measurable_complexSphereProjector (ι := ι)).aemeasurable).2
  change Integrable
    (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
      complexSphereProjector x i j * complexSphereProjector x k l *
        complexSphereProjector x p q)
    (complexUnitSphereHaarLaw ι)
  exact integrable_complexSphereProjectorThirdMoment ι i j k l p q

private noncomputable def tracePairTerm
    (A P : Matrix ι ι ℂ) (s : ι × ι) : ℂ :=
  A s.1 s.2 * P s.2 s.1

private theorem trace_eq_pairSum (A P : Matrix ι ι ℂ) :
    (A * P).trace = ∑ s : ι × ι, tracePairTerm A P s := by
  simp [tracePairTerm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fintype.sum_prod_type]

private noncomputable def thirdTraceCoordinateTerm
    (A B C P : Matrix ι ι ℂ)
    (s : (ι × ι) × ((ι × ι) × (ι × ι))) : ℂ :=
  tracePairTerm A P s.2.2 * tracePairTerm B P s.2.1 *
    tracePairTerm C P s.1

private noncomputable def thirdTraceKernelTerm
    (A B C : Matrix ι ι ℂ)
    (s : (ι × ι) × ((ι × ι) × (ι × ι))) : ℂ :=
  A s.2.2.1 s.2.2.2 * B s.2.1.1 s.2.1.2 * C s.1.1 s.1.2 *
    complexProjectiveThirdMomentKernel ι
      s.2.2.2 s.2.2.1 s.2.1.2 s.2.1.1 s.1.2 s.1.1

private theorem trace_mul_three_eq_productSum
    (A B C P : Matrix ι ι ℂ) :
    (A * P).trace * (B * P).trace * (C * P).trace =
      ∑ s : (ι × ι) × ((ι × ι) × (ι × ι)),
        thirdTraceCoordinateTerm A B C P s := by
  rw [trace_eq_pairSum, trace_eq_pairSum, trace_eq_pairSum]
  simp [thirdTraceCoordinateTerm, Fintype.sum_prod_type,
    tracePairTerm, Finset.mul_sum, Finset.sum_mul]

private theorem thirdTraceKernel_productSum
    (A B C : Matrix ι ι ℂ) :
    (∑ s : (ι × ι) × ((ι × ι) × (ι × ι)),
        thirdTraceKernelTerm A B C s) =
      complexProjectiveThirdTraceNumerator A B C := by
  have h := (sum_three_reverse
    (f := fun ab cd ef : ι × ι ↦
      A ab.1 ab.2 * B cd.1 cd.2 * C ef.1 ef.2 *
        complexProjectiveThirdMomentKernel ι
          ab.2 ab.1 cd.2 cd.1 ef.2 ef.1)).symm
  rw [← complexProjectiveThirdMomentKernel_trace_contract A B C]
  simpa only [thirdTraceKernelTerm, Fintype.sum_prod_type] using h

set_option maxHeartbeats 1200000 in
/-- Exact mixed trace contraction of the concrete order-three projective
Haar moment. -/
theorem integral_complexProjectiveHaar_trace_mul_three
    (A B C : Matrix ι ι ℂ) :
    (∫ P, (A * P).trace * (B * P).trace * (C * P).trace
        ∂complexProjectiveHaarLaw ι) =
      complexProjectiveThirdTraceNumerator A B C *
        (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
  calc
    _ = ∫ P, ∑ s : (ι × ι) × ((ι × ι) × (ι × ι)),
          thirdTraceCoordinateTerm A B C P s
          ∂complexProjectiveHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [] with P
      exact trace_mul_three_eq_productSum A B C P
    _ = ∑ s : (ι × ι) × ((ι × ι) × (ι × ι)),
          ∫ P, thirdTraceCoordinateTerm A B C P s
            ∂complexProjectiveHaarLaw ι := by
      rw [integral_finsetSum]
      intro s hs
      rcases s with ⟨⟨e, f⟩, ⟨⟨c, d⟩, ⟨a, b⟩⟩⟩
      change Integrable
        (fun P : Matrix ι ι ℂ ↦
          (A a b * P b a) * (B c d * P d c) * (C e f * P f e))
        (complexProjectiveHaarLaw ι)
      have hfun :
          (fun P : Matrix ι ι ℂ ↦
            (A a b * P b a) * (B c d * P d c) * (C e f * P f e)) =
          (fun P ↦ (A a b * B c d * C e f) *
            (P b a * P d c * P f e)) := by
        funext P
        ring
      rw [hfun]
      exact (integrable_complexProjectiveHaar_coordinateThirdMoment
        b a d c f e).const_mul (A a b * B c d * C e f)
    _ = ∑ s : (ι × ι) × ((ι × ι) × (ι × ι)),
          thirdTraceKernelTerm A B C s *
            (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
      apply Finset.sum_congr rfl
      intro s hs
      rcases s with ⟨⟨e, f⟩, ⟨⟨c, d⟩, ⟨a, b⟩⟩⟩
      dsimp [thirdTraceCoordinateTerm, tracePairTerm,
        thirdTraceKernelTerm]
      have hfun :
          (fun P : Matrix ι ι ℂ ↦
            (A a b * P b a) * (B c d * P d c) * (C e f * P f e)) =
          (fun P ↦ (A a b * B c d * C e f) *
            (P b a * P d c * P f e)) := by
        funext P
        ring
      rw [hfun, integral_const_mul,
        complexProjectiveHaar_coordinateThirdMoment_formula]
      ring
    _ = (∑ s : (ι × ι) × ((ι × ι) × (ι × ι)),
          thirdTraceKernelTerm A B C s) *
            (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
      rw [Finset.sum_mul]
    _ = _ := by
      rw [thirdTraceKernel_productSum]

/-- For trace-one matrices and an idempotent rank-one direction, the six
trace terms reduce to `2 + 4 tr(A O)`. -/
theorem complexProjectiveThirdTraceNumerator_rankOne
    (A O : Matrix ι ι ℂ)
    (hAtrace : A.trace = 1) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    complexProjectiveThirdTraceNumerator A O O =
      2 + 4 * (A * O).trace := by
  simp only [complexProjectiveThirdTraceNumerator, hAtrace, hOtrace,
    hOidempotent, one_mul, mul_one]
  ring

/-- Rank-one specialization of the mixed trace contraction. -/
theorem integral_complexProjectiveHaar_trace_mul_rankOne_sq
    (A O : Matrix ι ι ℂ)
    (hAtrace : A.trace = 1) (hOtrace : O.trace = 1)
    (hOidempotent : O * O = O) :
    (∫ P, (A * P).trace * (O * P).trace * (O * P).trace
        ∂complexProjectiveHaarLaw ι) =
      (2 + 4 * (A * O).trace) *
        (complexProjectiveThirdMomentDenominator ι)⁻¹ := by
  rw [integral_complexProjectiveHaar_trace_mul_three,
    complexProjectiveThirdTraceNumerator_rankOne A O hAtrace hOtrace
      hOidempotent]

end ThirdTraceContraction

end

end TomographyOracleCore
