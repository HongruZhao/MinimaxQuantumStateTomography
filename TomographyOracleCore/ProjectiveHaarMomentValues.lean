import TomographyOracleCore.ProjectiveHaarMoments

namespace TomographyOracleCore

open MeasureTheory Metric Set
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator Pointwise

noncomputable section

set_option maxHeartbeats 800000 in

/-- A concrete two-coordinate reflection forces the one-coordinate fourth
 moment to be twice every distinct two-coordinate diagonal moment. -/
theorem complexSphereProjectorSecondMoment_diagonal_eq_two_pair
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorSecondMoment ι i i i i =
      2 * complexSphereProjectorSecondMoment ι i i j j := by
  let q : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (9 / 25 : ℂ) * complexSphereProjector x i i +
    (16 / 25 : ℂ) * complexSphereProjector x j j +
    (12 / 25 : ℂ) *
      (complexSphereProjector x i j + complexSphereProjector x j i)
  let f : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    complexSphereProjector x i i * complexSphereProjector x i i
  have hf : Continuous f :=
    (continuous_complexSphereProjector_apply ι i i).mul
      (continuous_complexSphereProjector_apply ι i i)
  have hinv := integral_comp_complexUnitSphereHaarLaw_linearIsometry ι
    (complexLinearIsometryEquivToReal
      (complexTwoCoordinateMixIsometry ι i j)) f hf
  have hcomp :
      (fun x ↦ f (unitSphereLinearIsometryAction
        (complexLinearIsometryEquivToReal
          (complexTwoCoordinateMixIsometry ι i j)) x)) =
      (fun x ↦ q x * q x) := by
    funext x
    dsimp [f]
    rw [complexSphereProjector_mix_left_diagonal ι i j hij]
  have hinv' :
      (∫ x, q x * q x ∂complexUnitSphereHaarLaw ι) =
        complexSphereProjectorSecondMoment ι i i i i := by
    rw [hcomp] at hinv
    simpa [f, complexSphereProjectorSecondMoment] using hinv
  let g1 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (81 / 625 : ℂ) *
      (complexSphereProjector x i i * complexSphereProjector x i i)
  let g2 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (256 / 625 : ℂ) *
      (complexSphereProjector x j j * complexSphereProjector x j j)
  let g3 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (144 / 625 : ℂ) *
      (complexSphereProjector x i j * complexSphereProjector x i j)
  let g4 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (144 / 625 : ℂ) *
      (complexSphereProjector x j i * complexSphereProjector x j i)
  let g5 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (288 / 625 : ℂ) *
      (complexSphereProjector x i i * complexSphereProjector x j j)
  let g6 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (216 / 625 : ℂ) *
      (complexSphereProjector x i i * complexSphereProjector x i j)
  let g7 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (216 / 625 : ℂ) *
      (complexSphereProjector x i i * complexSphereProjector x j i)
  let g8 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (384 / 625 : ℂ) *
      (complexSphereProjector x j j * complexSphereProjector x i j)
  let g9 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (384 / 625 : ℂ) *
      (complexSphereProjector x j j * complexSphereProjector x j i)
  let g10 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦
    (288 / 625 : ℂ) *
      (complexSphereProjector x i j * complexSphereProjector x j i)
  let s2 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ g1 x + g2 x
  let s3 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s2 x + g3 x
  let s4 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s3 x + g4 x
  let s5 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s4 x + g5 x
  let s6 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s5 x + g6 x
  let s7 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s6 x + g7 x
  let s8 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s7 x + g8 x
  let s9 : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ := fun x ↦ s8 x + g9 x
  have hexpand :
      (fun x ↦ q x * q x) =
      (fun x ↦ s9 x + g10 x) := by
    funext x
    dsimp [q, s9, s8, s7, s6, s5, s4, s3, s2,
      g1, g2, g3, g4, g5, g6, g7, g8, g9, g10]
    ring
  rw [hexpand] at hinv'
  have h1 : Integrable g1 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι i i i i).const_mul _
  have h2 : Integrable g2 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι j j j j).const_mul _
  have h3 : Integrable g3 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι i j i j).const_mul _
  have h4 : Integrable g4 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι j i j i).const_mul _
  have h5 : Integrable g5 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι i i j j).const_mul _
  have h6 : Integrable g6 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι i i i j).const_mul _
  have h7 : Integrable g7 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι i i j i).const_mul _
  have h8 : Integrable g8 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι j j i j).const_mul _
  have h9 : Integrable g9 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι j j j i).const_mul _
  have h10 : Integrable g10 (complexUnitSphereHaarLaw ι) := by
    exact (integrable_complexSphereProjectorSecondMoment ι i j j i).const_mul _
  have c1 : Continuous g1 := by
    dsimp [g1]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι i i).mul
        (continuous_complexSphereProjector_apply ι i i))
  have c2 : Continuous g2 := by
    dsimp [g2]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι j j).mul
        (continuous_complexSphereProjector_apply ι j j))
  have c3 : Continuous g3 := by
    dsimp [g3]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι i j).mul
        (continuous_complexSphereProjector_apply ι i j))
  have c4 : Continuous g4 := by
    dsimp [g4]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι j i).mul
        (continuous_complexSphereProjector_apply ι j i))
  have c5 : Continuous g5 := by
    dsimp [g5]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι i i).mul
        (continuous_complexSphereProjector_apply ι j j))
  have c6 : Continuous g6 := by
    dsimp [g6]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι i i).mul
        (continuous_complexSphereProjector_apply ι i j))
  have c7 : Continuous g7 := by
    dsimp [g7]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι i i).mul
        (continuous_complexSphereProjector_apply ι j i))
  have c8 : Continuous g8 := by
    dsimp [g8]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι j j).mul
        (continuous_complexSphereProjector_apply ι i j))
  have c9 : Continuous g9 := by
    dsimp [g9]
    exact continuous_const.mul
      ((continuous_complexSphereProjector_apply ι j j).mul
        (continuous_complexSphereProjector_apply ι j i))
  have cs2 : Continuous s2 := by dsimp [s2]; fun_prop
  have cs3 : Continuous s3 := by dsimp [s3]; fun_prop
  have cs4 : Continuous s4 := by dsimp [s4]; fun_prop
  have cs5 : Continuous s5 := by dsimp [s5]; fun_prop
  have cs6 : Continuous s6 := by dsimp [s6]; fun_prop
  have cs7 : Continuous s7 := by dsimp [s7]; fun_prop
  have cs8 : Continuous s8 := by dsimp [s8]; fun_prop
  have cs9 : Continuous s9 := by dsimp [s9]; fun_prop
  have int_cont (g : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ)
      (hg : Continuous g) : Integrable g (complexUnitSphereHaarLaw ι) := by
    apply hg.integrable_of_hasCompactSupport
    exact isCompact_univ.of_isClosed_subset isClosed_closure (Set.subset_univ _)
  have hs2 := int_cont s2 cs2
  have hs3 := int_cont s3 cs3
  have hs4 := int_cont s4 cs4
  have hs5 := int_cont s5 cs5
  have hs6 := int_cont s6 cs6
  have hs7 := int_cont s7 cs7
  have hs8 := int_cont s8 cs8
  have hs9 := int_cont s9 cs9
  have int_add' (g h : sphere (0 : EuclideanSpace ℂ ι) 1 → ℂ)
      (hg : Integrable g (complexUnitSphereHaarLaw ι))
      (hh : Integrable h (complexUnitSphereHaarLaw ι)) :
      (∫ x, g x + h x ∂complexUnitSphereHaarLaw ι) =
        (∫ x, g x ∂complexUnitSphereHaarLaw ι) +
          ∫ x, h x ∂complexUnitSphereHaarLaw ι := by
    simpa only [Pi.add_apply] using integral_add hg hh
  rw [int_add' s9 g10 hs9 h10] at hinv'
  simp only [s9] at hinv'
  rw [int_add' s8 g9 hs8 h9] at hinv'
  simp only [s8] at hinv'
  rw [int_add' s7 g8 hs7 h8] at hinv'
  simp only [s7] at hinv'
  rw [int_add' s6 g7 hs6 h7] at hinv'
  simp only [s6] at hinv'
  rw [int_add' s5 g6 hs5 h6] at hinv'
  simp only [s5] at hinv'
  rw [int_add' s4 g5 hs4 h5] at hinv'
  simp only [s4] at hinv'
  rw [int_add' s3 g4 hs3 h4] at hinv'
  simp only [s3] at hinv'
  rw [int_add' s2 g3 hs2 h3] at hinv'
  simp only [s2] at hinv'
  rw [int_add' g1 g2 h1 h2] at hinv'
  repeat' rw [integral_const_mul] at hinv'
  change
    (81 / 625 : ℂ) * complexSphereProjectorSecondMoment ι i i i i +
      (256 / 625 : ℂ) * complexSphereProjectorSecondMoment ι j j j j +
      (144 / 625 : ℂ) * complexSphereProjectorSecondMoment ι i j i j +
      (144 / 625 : ℂ) * complexSphereProjectorSecondMoment ι j i j i +
      (288 / 625 : ℂ) * complexSphereProjectorSecondMoment ι i i j j +
      (216 / 625 : ℂ) * complexSphereProjectorSecondMoment ι i i i j +
      (216 / 625 : ℂ) * complexSphereProjectorSecondMoment ι i i j i +
      (384 / 625 : ℂ) * complexSphereProjectorSecondMoment ι j j i j +
      (384 / 625 : ℂ) * complexSphereProjectorSecondMoment ι j j j i +
      (288 / 625 : ℂ) * complexSphereProjectorSecondMoment ι i j j i =
        complexSphereProjectorSecondMoment ι i i i i at hinv'
  rw [complexSphereProjectorSecondMoment_diagonal_eq ι j i,
    complexSphereProjectorSecondMoment_offdiag_square_eq_zero ι i j hij,
    complexSphereProjectorSecondMoment_offdiag_square_eq_zero ι j i (Ne.symm hij),
    complexSphereProjectorSecondMoment_three_one_eq_zero ι i j hij,
    complexSphereProjectorSecondMoment_offdiag_swap_eq_diagonal ι i j] at hinv'
  have hz1 : complexSphereProjectorSecondMoment ι i i j i = 0 := by
    apply complexSphereProjectorSecondMoment_eq_zero_of_not_balanced
    simp [Ne.symm hij]
  have hz2 : complexSphereProjectorSecondMoment ι j j i j = 0 := by
    apply complexSphereProjectorSecondMoment_eq_zero_of_not_balanced
    simp [hij]
  have hz3 : complexSphereProjectorSecondMoment ι j j j i = 0 := by
    exact complexSphereProjectorSecondMoment_three_one_eq_zero ι j i (Ne.symm hij)
  rw [hz1, hz2, hz3] at hinv'
  ring_nf at hinv'
  linear_combination (-625 / 288 : ℂ) * hinv'

/-- Squaring the pointwise trace-one identity and integrating gives the
 global normalization of all diagonal-pair moments. -/
theorem complexSphereProjectorSecondMoment_diagonal_doubleSum_eq_one
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    (∑ a : ι, ∑ b : ι,
      complexSphereProjectorSecondMoment ι a a b b) = 1 := by
  have hint (a b : ι) :=
    integrable_complexSphereProjectorSecondMoment ι a a b b
  have hinner (a : ι) :
      (∫ x, ∑ b : ι,
          complexSphereProjector x a a * complexSphereProjector x b b
          ∂complexUnitSphereHaarLaw ι) =
        ∑ b : ι, complexSphereProjectorSecondMoment ι a a b b := by
    rw [integral_finsetSum]
    · rfl
    · intro b hb
      exact hint a b
  have houterInt (a : ι) :
      Integrable
        (fun x : sphere (0 : EuclideanSpace ℂ ι) 1 ↦
          ∑ b : ι,
            complexSphereProjector x a a * complexSphereProjector x b b)
        (complexUnitSphereHaarLaw ι) := by
    apply integrable_finsetSum Finset.univ
    intro b hb
    exact hint a b
  calc
    (∑ a : ι, ∑ b : ι,
        complexSphereProjectorSecondMoment ι a a b b) =
        ∑ a : ι, ∫ x, ∑ b : ι,
          complexSphereProjector x a a * complexSphereProjector x b b
          ∂complexUnitSphereHaarLaw ι := by
      apply Finset.sum_congr rfl
      intro a ha
      exact (hinner a).symm
    _ = ∫ x, ∑ a : ι, ∑ b : ι,
          complexSphereProjector x a a * complexSphereProjector x b b
          ∂complexUnitSphereHaarLaw ι := by
      symm
      exact integral_finsetSum Finset.univ
        (fun a ha ↦ houterInt a)
    _ = ∫ _x, (1 : ℂ) ∂complexUnitSphereHaarLaw ι := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← Finset.sum_mul_sum]
      change (complexSphereProjector x).trace *
        (complexSphereProjector x).trace = 1
      rw [complexSphereProjector_trace_eq_one]
      norm_num
    _ = 1 := by
      rw [integral_const]
      simp

/-- Exact one-coordinate fourth moment under normalized complex-sphere Haar. -/
theorem complexSphereProjectorSecondMoment_diagonal_value
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (i : ι) :
    complexSphereProjectorSecondMoment ι i i i i =
      2 * (complexProjectiveTwoMomentDenominator ι)⁻¹ := by
  let b : ℂ := complexSphereProjectorSecondMoment ι i i i i
  have hterm (a c : ι) :
      complexSphereProjectorSecondMoment ι a a c c =
        b / 2 + if a = c then b / 2 else 0 := by
    by_cases hac : a = c
    · subst c
      rw [complexSphereProjectorSecondMoment_diagonal_eq ι a i]
      simp [b]
    · have hr := complexSphereProjectorSecondMoment_diagonal_eq_two_pair a c hac
      have hd := complexSphereProjectorSecondMoment_diagonal_eq ι a i
      rw [hd] at hr
      simp [hac]
      dsimp [b] at hr ⊢
      linear_combination (-1 / 2 : ℂ) * hr
  have hnorm := complexSphereProjectorSecondMoment_diagonal_doubleSum_eq_one (ι := ι)
  simp_rw [hterm] at hnorm
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ] at hnorm
  have hdiagDouble :
      (∑ a : ι, ∑ c : ι, if a = c then
        complexSphereProjectorSecondMoment ι i i i i / 2 else 0) =
      Fintype.card ι •
        (complexSphereProjectorSecondMoment ι i i i i / 2) := by
    simp
  rw [hdiagDouble] at hnorm
  simp only [nsmul_eq_mul] at hnorm
  have hden := complexProjectiveTwoMomentDenominator_ne_zero (ι := ι)
  rw [complexProjectiveTwoMomentDenominator]
  rw [complexProjectiveTwoMomentDenominator] at hden
  field_simp
  push_cast
  dsimp [b] at hnorm
  linear_combination 2 * hnorm

/-- Exact balanced moment for two distinct coordinates. -/
theorem complexSphereProjectorSecondMoment_distinct_diagonal_pair_value
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (i j : ι) (hij : i ≠ j) :
    complexSphereProjectorSecondMoment ι i i j j =
      (complexProjectiveTwoMomentDenominator ι)⁻¹ := by
  have hr := complexSphereProjectorSecondMoment_diagonal_eq_two_pair i j hij
  rw [complexSphereProjectorSecondMoment_diagonal_value i] at hr
  linear_combination (-1 / 2 : ℂ) * hr

/-- The normalized complex-projective coordinate two-moment formula, proved
 unconditionally from sphere invariance, phase selection, a two-coordinate
 reflection, and trace normalization. -/
theorem complexProjectiveCoordinateTwoMomentFormula_proved
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    ComplexProjectiveCoordinateTwoMomentFormula ι := by
  intro i j k l
  by_cases hij : i = j
  · subst j
    by_cases hkl : k = l
    · subst l
      by_cases hik : i = k
      · subst k
        rw [complexSphereProjectorSecondMoment_diagonal_value (ι := ι) i]
        norm_num
      · simpa [hik, Ne.symm hik] using
          complexSphereProjectorSecondMoment_distinct_diagonal_pair_value (ι := ι) i k hik
    · have hz : complexSphereProjectorSecondMoment ι i i k l = 0 := by
        apply complexSphereProjectorSecondMoment_eq_zero_of_not_balanced
        intro hbal
        rcases hbal with hfirst | hsecond
        · exact hkl hfirst.2
        · exact hkl (hsecond.2.trans hsecond.1)
      rw [hz]
      by_cases hil : i = l
      · subst l
        simp [hkl]
      · simp [hkl, hil]
  · by_cases hil : i = l
    · subst l
      by_cases hkj : k = j
      · subst k
        rw [complexSphereProjectorSecondMoment_offdiag_swap_eq_diagonal]
        simpa [hij, Ne.symm hij] using
          complexSphereProjectorSecondMoment_distinct_diagonal_pair_value (ι := ι) i j hij
      · have hz : complexSphereProjectorSecondMoment ι i j k i = 0 := by
          apply complexSphereProjectorSecondMoment_eq_zero_of_not_balanced
          simp [hij, hkj]
        rw [hz]
        simp [hij, hkj]
    · have hz : complexSphereProjectorSecondMoment ι i j k l = 0 := by
        apply complexSphereProjectorSecondMoment_eq_zero_of_not_balanced
        simp [hij, hil]
      rw [hz]
      simp [hij, hil]

/-- The concrete normalized projective Haar law satisfies the exact matrix
second-moment contraction with no project-specific axioms. -/
theorem complexProjectiveTwoMomentTheorem_proved
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι] :
    ComplexProjectiveTwoMomentTheorem (ι := ι) :=
  complexProjectiveCoordinateTwoMomentFormula_implies_twoMomentTheorem
    ι (complexProjectiveCoordinateTwoMomentFormula_proved (ι := ι))

/-- The concrete projective Haar forward channel has the exact closed form,
with no moment premise remaining. -/
theorem complexProjectiveHaarForward_eq_closedForm_unconditional
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    projectiveBasisForward (complexProjectiveHaarLaw ι) A =
      haarBasisForwardClosedForm A :=
  complexProjectiveHaarForward_eq_closedForm
    ι (complexProjectiveTwoMomentTheorem_proved (ι := ι)) A

/-- Exact calibrated inversion identity for the concrete projective Haar
channel. -/
theorem calibrated_complexProjectiveHaarForward_eq_unconditional
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    haarDimensionPlusOne (ι := ι) •
          projectiveBasisForward (complexProjectiveHaarLaw ι) A -
        A.trace • (1 : Matrix ι ι ℂ) = A :=
  calibrated_complexProjectiveHaarForward_eq
    ι (complexProjectiveTwoMomentTheorem_proved (ι := ι)) A

end
end TomographyOracleCore
