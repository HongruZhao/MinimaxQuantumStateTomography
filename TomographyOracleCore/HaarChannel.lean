import TomographyOracleCore.ForwardGeometry

namespace TomographyOracleCore

open MeasureTheory
open ProbabilityTheory
open MatrixReduction
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator

/-!
# Exact-Haar closed-form channel algebra

This file separates the finite-dimensional algebra of the global-Haar
random-basis channel from the genuinely probabilistic Haar-moment theorem.
No Haar moment identity is postulated here.  The closed form below is the
right-hand side obtained after contracting the complex projective two-design
identity; `ProjectiveTwoMomentContraction` records, as an unasserted
proposition, the exact nonlocal bridge still needed to identify a concrete
projective measure with this closed form.
-/

section ClosedForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Dimension scalar `D + 1` used by the exact complex-projective channel. -/
def haarDimensionPlusOne : ℂ := ((Fintype.card ι + 1 : ℕ) : ℂ)

theorem haarDimensionPlusOne_ne_zero :
    (haarDimensionPlusOne (ι := ι)) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have hcard : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  simp [haarDimensionPlusOne] at hre
  linarith

/-- Algebraic closed form of the exact global-Haar random-basis forward
channel: `(A + tr(A) I) / (D + 1)`.

The definition itself is not a claim about a Haar measure; the moment bridge
which identifies the integral channel with this expression is isolated below.
-/
noncomputable def haarBasisForwardClosedForm (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  (haarDimensionPlusOne (ι := ι))⁻¹ •
    (A + A.trace • (1 : Matrix ι ι ℂ))

theorem haarBasisForwardClosedForm_add (A B : Matrix ι ι ℂ) :
    haarBasisForwardClosedForm (A + B) =
      haarBasisForwardClosedForm A + haarBasisForwardClosedForm B := by
  ext i j
  simp [haarBasisForwardClosedForm, Matrix.trace_add]
  ring

theorem haarBasisForwardClosedForm_smul (c : ℂ) (A : Matrix ι ι ℂ) :
    haarBasisForwardClosedForm (c • A) =
      c • haarBasisForwardClosedForm A := by
  ext i j
  simp [haarBasisForwardClosedForm, Matrix.trace_smul]
  ring

/-- The manuscript calibration `(D+1) M(A) - tr(A) I`, applied to the exact
closed form. -/
noncomputable def haarCalibratedForwardClosedForm (A : Matrix ι ι ℂ) :
    Matrix ι ι ℂ :=
  haarDimensionPlusOne (ι := ι) • haarBasisForwardClosedForm A -
    A.trace • (1 : Matrix ι ι ℂ)

/-- Calibration cancels the depolarizing part exactly. -/
@[simp] theorem haarCalibratedForwardClosedForm_eq (A : Matrix ι ι ℂ) :
    haarCalibratedForwardClosedForm A = A := by
  rw [haarCalibratedForwardClosedForm, haarBasisForwardClosedForm,
    smul_smul]
  rw [mul_inv_cancel₀ (haarDimensionPlusOne_ne_zero (ι := ι)), one_smul]
  abel

theorem haarCalibratedForwardClosedForm_add (A B : Matrix ι ι ℂ) :
    haarCalibratedForwardClosedForm (A + B) =
      haarCalibratedForwardClosedForm A +
        haarCalibratedForwardClosedForm B := by
  simp

theorem haarCalibratedForwardClosedForm_smul (c : ℂ)
    (A : Matrix ι ι ℂ) :
    haarCalibratedForwardClosedForm (c • A) =
      c • haarCalibratedForwardClosedForm A := by
  simp

theorem haarCalibratedForwardClosedForm_isHermitian
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (haarCalibratedForwardClosedForm A).IsHermitian := by
  simpa using hA

end ClosedForm

section MomentBridge

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Matrix ι ι ℂ)]

/-- Forward channel induced by a probability law on rank-one projectors,
including the factor `D` coming from the `D` exchangeable columns of a random
basis.  This definition makes sense for any finite measure; the predicate
below says when its contracted second moment is the exact projective one. -/
noncomputable def projectiveBasisForward
    (ν : Measure (Matrix ι ι ℂ)) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (Fintype.card ι : ℂ) •
    ∫ B, (A * B).trace • B ∂ν

/-- Exact contracted complex-projective two-moment identity.  This is a
definition of the missing Haar-moment bridge, not an axiom and not an
inhabited structure. -/
def ProjectiveTwoMomentContraction
    (ν : Measure (Matrix ι ι ℂ)) : Prop :=
  ∀ A : Matrix ι ι ℂ,
    (Fintype.card ι : ℂ) •
        ∫ B, (A * B).trace • B ∂ν =
      haarBasisForwardClosedForm A

/-- Once the contracted two-moment theorem is supplied for a concrete
projective Haar law, the integral channel is definitionally identified with
the closed form. -/
theorem projectiveBasisForward_eq_closedForm
    (ν : Measure (Matrix ι ι ℂ))
    (hmoment : ProjectiveTwoMomentContraction ν)
    (A : Matrix ι ι ℂ) :
    projectiveBasisForward ν A = haarBasisForwardClosedForm A := by
  exact hmoment A

/-- The calibrated integral channel is the identity, conditional only on the
literal contracted two-moment bridge. -/
theorem calibrated_projectiveBasisForward_eq
    (ν : Measure (Matrix ι ι ℂ))
    (hmoment : ProjectiveTwoMomentContraction ν)
    (A : Matrix ι ι ℂ) :
    haarDimensionPlusOne (ι := ι) • projectiveBasisForward ν A -
        A.trace • (1 : Matrix ι ι ℂ) = A := by
  rw [projectiveBasisForward_eq_closedForm ν hmoment A]
  exact haarCalibratedForwardClosedForm_eq A

end MomentBridge

section DensityCurvature

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The calibrated exact-Haar density channel, expressed through the
closed-form matrix calculation. -/
noncomputable def haarCalibratedDensityChannel
    (ρ : DensityOperator ι) : Matrix ι ι ℂ :=
  haarCalibratedForwardClosedForm ρ.matrix

@[simp] theorem haarCalibratedDensityChannel_eq
    (ρ : DensityOperator ι) :
    haarCalibratedDensityChannel ρ = ρ.matrix := by
  simp [haarCalibratedDensityChannel]

theorem haarCalibratedDensityChannel_isHermitian
    (ρ : DensityOperator ι) :
    (haarCalibratedDensityChannel ρ).IsHermitian := by
  simpa using ρ.isHermitian

/-- The exact-Haar calibrated channel has curvature exactly one: its forward
energy is the squared Hermitian Frobenius norm. -/
theorem haarCalibratedDensityChannel_curvature_eq
    (σ ρ : DensityOperator ι) :
    hermitianForwardEnergy σ ρ
        (haarCalibratedDensityChannel σ -
          haarCalibratedDensityChannel ρ) =
      hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
        (σ.sub_isHermitian ρ) ^ 2 := by
  simp only [haarCalibratedDensityChannel_eq]
  have htrace := trace_sq_eq_hermitianFrobeniusSq
    (σ.matrix - ρ.matrix) (σ.sub_isHermitian ρ)
  have hre := congrArg Complex.re htrace
  simpa [hermitianForwardEnergy, hermitianFrobeniusNorm_sq] using hre

theorem haarCalibratedDensityChannel_curvature_one
    (σ ρ : DensityOperator ι) :
    (1 : ℝ) * hermitianFrobeniusNorm (σ.matrix - ρ.matrix)
        (σ.sub_isHermitian ρ) ^ 2 ≤
      hermitianForwardEnergy σ ρ
        (haarCalibratedDensityChannel σ -
          haarCalibratedDensityChannel ρ) := by
  rw [one_mul, haarCalibratedDensityChannel_curvature_eq]

end DensityCurvature

section ScoreAlgebra

/-! The following scalar functions are the exact closed forms obtained after
the second- and third-projective-moment contractions.  Their elementary
identities and sharp uniform bound are proved here without asserting those
probabilistic contractions. -/

/-- Exact first moment of `x = tr(O B)` under the Born-biased projective law. -/
noncomputable def haarOverlapFirstMoment (D : ℕ) (q : ℝ) : ℝ :=
  (1 + q) / (D + 1)

/-- Exact second moment of `x = tr(O B)` under the Born-biased projective law. -/
noncomputable def haarOverlapSecondMoment (D : ℕ) (q : ℝ) : ℝ :=
  (2 + 4 * q) / ((D + 1) * (D + 2))

/-- Closed-form mean of the calibrated rank-one score `Z = (D+1)x - 1`. -/
noncomputable def haarCalibratedScoreMean (D : ℕ) (q : ℝ) : ℝ :=
  (D + 1) * haarOverlapFirstMoment D q - 1

/-- Closed-form second moment of the calibrated rank-one score. -/
noncomputable def haarCalibratedScoreSecondMoment (D : ℕ) (q : ℝ) : ℝ :=
  (D + 1) ^ 2 * haarOverlapSecondMoment D q -
    2 * (D + 1) * haarOverlapFirstMoment D q + 1

/-- Exact variance polynomial from the contracted second and third moments. -/
noncomputable def haarCalibratedScoreVariance (D : ℕ) (q : ℝ) : ℝ :=
  D * (1 + 2 * q) / (D + 2) - q ^ 2

theorem haarCalibratedScoreMean_eq
    (D : ℕ) (q : ℝ) :
    haarCalibratedScoreMean D q = q := by
  simp [haarCalibratedScoreMean, haarOverlapFirstMoment]
  field_simp
  ring

theorem haarCalibratedScoreSecondMoment_eq
    (D : ℕ) (q : ℝ) :
    haarCalibratedScoreSecondMoment D q =
      D * (1 + 2 * q) / (D + 2) := by
  simp [haarCalibratedScoreSecondMoment, haarOverlapFirstMoment,
    haarOverlapSecondMoment]
  field_simp
  ring

/-- Completing the square gives the sharp maximum of the exact Haar variance
polynomial over all real overlaps, hence in particular over `[0,1]`. -/
theorem haarCalibratedScoreVariance_le_sharp
    (D : ℕ) (q : ℝ) :
    haarCalibratedScoreVariance D q ≤
      2 * D * (D + 1) / (D + 2) ^ 2 := by
  have hsq : 0 ≤ (q - (D : ℝ) / (D + 2)) ^ 2 := sq_nonneg _
  have hid :
      2 * (D : ℝ) * (D + 1) / (D + 2) ^ 2 -
          haarCalibratedScoreVariance D q =
        (q - (D : ℝ) / (D + 2)) ^ 2 := by
    simp [haarCalibratedScoreVariance]
    field_simp
    ring
  linarith

/-- Dimension-free variance gate used by the generic upper theorem. -/
theorem haarCalibratedScoreVariance_lt_two
    (D : ℕ) (q : ℝ) :
    haarCalibratedScoreVariance D q < 2 := by
  have hsharp := haarCalibratedScoreVariance_le_sharp D q
  have hden : 0 < ((D : ℝ) + 2) ^ 2 := sq_pos_of_pos (by positivity)
  have hstrict : 2 * (D : ℝ) * (D + 1) / (D + 2) ^ 2 < 2 := by
    apply (div_lt_iff₀ hden).2
    nlinarith [sq_nonneg ((D : ℝ) + 2)]
  exact hsharp.trans_lt hstrict

theorem haarCalibratedScoreVariance_le_two
    (D : ℕ) (q : ℝ) :
    haarCalibratedScoreVariance D q ≤ 2 :=
  (haarCalibratedScoreVariance_lt_two D q).le

end ScoreAlgebra

section ScoreMomentBridge

variable {ι : Type*} [Fintype ι]
  [MeasurableSpace (Matrix ι ι ℂ)]

/-- The real calibrated score in one rank-one direction, evaluated at an
observed rank-one projector.  Rank-one and positivity conditions belong to
the concrete Haar experiment and are intentionally not baked into this
purely algebraic function. -/
noncomputable def haarCalibratedRankOneScore
    (O B : Matrix ι ι ℂ) : ℝ :=
  ((Fintype.card ι + 1 : ℕ) : ℝ) * (O * B).trace.re - 1

/-- Exact second/third contracted projective-moment output for one calibrated
score under its *Born-biased observed law*.  This predicate is deliberately
unasserted.  A construction of the concrete global-Haar experiment must
prove it from normalized projective moments; merely naming a measure does not
produce a value of this proposition. -/
def HaarRankOneScoreMomentBridge
    (μ : Measure (Matrix ι ι ℂ)) (O : Matrix ι ι ℂ) (q : ℝ) : Prop :=
  MemLp (haarCalibratedRankOneScore O) 2 μ ∧
    (∫ B, haarCalibratedRankOneScore O B ∂μ) = q ∧
    (∫ B, (haarCalibratedRankOneScore O B) ^ 2 ∂μ) =
      (Fintype.card ι : ℝ) * (1 + 2 * q) /
        (Fintype.card ι + 2)

/-- The moment bridge gives the exact variance polynomial of the actual score
random variable. -/
theorem variance_haarCalibratedRankOneScore_eq
    (μ : Measure (Matrix ι ι ℂ)) [IsProbabilityMeasure μ]
    (O : Matrix ι ι ℂ) (q : ℝ)
    (hmoment : HaarRankOneScoreMomentBridge μ O q) :
    variance (haarCalibratedRankOneScore O) μ =
      haarCalibratedScoreVariance (Fintype.card ι) q := by
  rcases hmoment with ⟨hLp, hmean, hsecond⟩
  rw [variance_eq_sub hLp]
  change
    (∫ B, (haarCalibratedRankOneScore O B) ^ 2 ∂μ) -
        (∫ B, haarCalibratedRankOneScore O B ∂μ) ^ 2 = _
  rw [hsecond, hmean]
  rfl

/-- Dimension-free variance gate for the concrete score, conditional exactly
on the score-moment bridge and on no target upper-bound statement. -/
theorem variance_haarCalibratedRankOneScore_lt_two
    (μ : Measure (Matrix ι ι ℂ)) [IsProbabilityMeasure μ]
    (O : Matrix ι ι ℂ) (q : ℝ)
    (hmoment : HaarRankOneScoreMomentBridge μ O q) :
    variance (haarCalibratedRankOneScore O) μ < 2 := by
  rw [variance_haarCalibratedRankOneScore_eq μ O q hmoment]
  exact haarCalibratedScoreVariance_lt_two (Fintype.card ι) q

theorem variance_haarCalibratedRankOneScore_le_two
    (μ : Measure (Matrix ι ι ℂ)) [IsProbabilityMeasure μ]
    (O : Matrix ι ι ℂ) (q : ℝ)
    (hmoment : HaarRankOneScoreMomentBridge μ O q) :
    variance (haarCalibratedRankOneScore O) μ ≤ 2 :=
  (variance_haarCalibratedRankOneScore_lt_two μ O q hmoment).le

end ScoreMomentBridge

end TomographyOracleCore
