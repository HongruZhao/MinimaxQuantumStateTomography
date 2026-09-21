import TomographyOracleCore.Candidate2PhaseRandomizedL6L2
import TomographyOracleCore.Candidate2FixedNormCovariancePlumbing
import TomographyOracleCore.MatrixReduction
import TomographyOracleCore.PhysicalPOVM
import TomographyOracleCore.FiniteUnitaryProjectiveScore
import TomographyOracleCore.BinaryCliffordPeriodicFinEnsemble

/-!
# The finite Born vector law used by Candidate 2

The physical finite-unitary POVM records the projector
`U† |b><b| U`.  Candidate 2 applies covariance concentration to a vector
whose outer product is `(D + 1)` times that projector.  This file constructs
the corresponding atomic vector law with the literal Born weights, proves it
is a probability measure, and connects its quarter-phase lift to the generic
fixed-norm and L6--L2 plumbing.

No sample-covariance concentration theorem is stated or assumed here.
-/

open MeasureTheory ProbabilityTheory InnerProductSpace
open TomographyOracleCore.MatrixReduction TomographyOracleCore.PhysicalPOVM
open scoped BigOperators ENNReal RealInnerProductSpace

namespace TomographyOracleCore.Candidate2FiniteBornVectorLaw

noncomputable section

open Candidate2PhaseRandomizedLaw

variable {D : ℕ} {A : Type*} [Fintype A] [Nonempty A]

local instance : InnerProductSpace ℝ (EuclideanSpace ℂ (Fin D)) :=
  InnerProductSpace.complexToReal

/-- Literal Born weight of outcome `b` in the basis selected by `U`. -/
def finiteUnitaryBornWeight
    (rho : DensityOperator (Fin D))
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) : ℝ :=
  (rho.matrix * finiteUnitaryMeasurementProjector U b).trace.re

theorem finiteUnitaryBornWeight_nonneg
    (hD : 0 < D) (rho : DensityOperator (Fin D))
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    0 ≤ finiteUnitaryBornWeight rho U b := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  exact trace_mul_re_nonnegative_of_posSemidef rho.matrix
    (finiteUnitaryMeasurementProjector U b) rho.posSemidef
    (finiteUnitaryMeasurementProjector_posSemidef U b)

/-- Candidate 2's scaled measurement vector.  Its outer product is
`(D + 1)` times the measured rank-one projector. -/
def candidate2ScaledMeasurementVector
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    EuclideanSpace ℂ (Fin D) :=
  Real.sqrt ((D : ℝ) + 1) • finiteUnitaryMeasurementVector U b

@[simp]
theorem candidate2ScaledMeasurementVector_norm_sq
    (U : Matrix.unitaryGroup (Fin D) ℂ) (b : Fin D) :
    ‖candidate2ScaledMeasurementVector U b‖ ^ 2 = (D : ℝ) + 1 := by
  rw [candidate2ScaledMeasurementVector, norm_smul,
    finiteUnitaryMeasurementVector_norm, mul_one, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

/-- Atomic law of the scaled measurement vector with the physical Born
weights.  The ensemble element has uniform mass `1 / |A|`; conditional on
it, the basis outcome has its Born probability. -/
def finiteUnitaryBornVectorLaw
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    Measure (EuclideanSpace ℂ (Fin D)) :=
  ((Fintype.card A : ℕ) : ℝ≥0∞)⁻¹ •
    ∑ e : A, ∑ b : Fin D,
      ENNReal.ofReal (finiteUnitaryBornWeight rho (U e) b) •
        Measure.dirac (candidate2ScaledMeasurementVector (U e) b)

/-- The ENNReal Born masses of the atomic vector law sum to `|A|`. -/
theorem sum_finiteUnitaryBornWeight_ennreal
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    (∑ e : A, ∑ b : Fin D,
      ENNReal.ofReal (finiteUnitaryBornWeight rho (U e) b)) =
        (Fintype.card A : ℝ≥0∞) := by
  have hnonneg (e : A) (b : Fin D) :
      0 ≤ finiteUnitaryBornWeight rho (U e) b :=
    finiteUnitaryBornWeight_nonneg hD rho (U e) b
  calc
    (∑ e : A, ∑ b : Fin D,
        ENNReal.ofReal (finiteUnitaryBornWeight rho (U e) b)) =
        ∑ e : A, ENNReal.ofReal
          (∑ b : Fin D, finiteUnitaryBornWeight rho (U e) b) := by
      apply Finset.sum_congr rfl
      intro e _
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun b _ ↦ hnonneg e b)).symm
    _ = ENNReal.ofReal
        (∑ e : A, ∑ b : Fin D,
          finiteUnitaryBornWeight rho (U e) b) := by
      exact (ENNReal.ofReal_sum_of_nonneg
        (fun e _ ↦ Finset.sum_nonneg fun b _ ↦ hnonneg e b)).symm
    _ = (Fintype.card A : ℝ≥0∞) := by
      rw [show (∑ e : A, ∑ b : Fin D,
          finiteUnitaryBornWeight rho (U e) b) =
          (Fintype.card A : ℝ) by
        simpa only [finiteUnitaryBornWeight] using
          sum_finiteUnitaryMeasurementProjector_ensemble_bornWeight U rho]
      simp

theorem finiteUnitaryBornVectorLaw_apply_univ
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    finiteUnitaryBornVectorLaw U rho Set.univ = 1 := by
  simp [finiteUnitaryBornVectorLaw, Measure.smul_apply,
    sum_finiteUnitaryBornWeight_ennreal hD U rho,
    Fintype.card_ne_zero]
  apply ENNReal.inv_mul_cancel
  · exact_mod_cast (Fintype.card_ne_zero : Fintype.card A ≠ 0)
  · simp

theorem finiteUnitaryBornVectorLaw_isProbability
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) := by
  constructor
  exact finiteUnitaryBornVectorLaw_apply_univ hD U rho

/-- Exact real-valued expectation formula for the atomic Born vector law.
This is the vector-valued counterpart of
`integral_finiteUnitaryProjectivePOVM_bornMeasure_real_eq_sum`. -/
theorem integral_finiteUnitaryBornVectorLaw_real_eq_sum
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (g : EuclideanSpace ℂ (Fin D) → ℝ) :
    (∫ x, g x ∂finiteUnitaryBornVectorLaw U rho) =
      ((Fintype.card A : ℕ) : ℝ≥0∞)⁻¹.toReal •
        ∑ e : A, ∑ b : Fin D,
          finiteUnitaryBornWeight rho (U e) b *
            g (candidate2ScaledMeasurementVector (U e) b) := by
  have hb (e : A) : ∀ b ∈ (Finset.univ : Finset (Fin D)),
      Integrable g
        (ENNReal.ofReal (finiteUnitaryBornWeight rho (U e) b) •
          Measure.dirac (candidate2ScaledMeasurementVector (U e) b)) := by
    intro b _
    apply Integrable.smul_measure
    · exact integrable_dirac (f := g) (by simp)
    · simp
  have he : ∀ e ∈ (Finset.univ : Finset A),
      Integrable g
        (∑ b : Fin D,
          ENNReal.ofReal (finiteUnitaryBornWeight rho (U e) b) •
            Measure.dirac (candidate2ScaledMeasurementVector (U e) b)) := by
    intro e _
    exact (integrable_finsetSum_measure).2 (hb e)
  unfold finiteUnitaryBornVectorLaw
  rw [integral_smul_measure]
  congr 1
  rw [integral_finsetSum_measure he]
  apply Finset.sum_congr rfl
  intro e _
  rw [integral_finsetSum_measure (hb e)]
  apply Finset.sum_congr rfl
  intro b _
  rw [integral_smul_measure]
  simp [finiteUnitaryBornWeight_nonneg hD rho (U e) b]

/-- The scaled vector has fixed squared norm `D + 1` almost surely under the
literal finite Born law. -/
theorem ae_fixedNorm_finiteUnitaryBornVectorLaw
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    ∀ᵐ x ∂finiteUnitaryBornVectorLaw U rho,
      ‖x‖ ^ 2 = (D : ℝ) + 1 := by
  unfold finiteUnitaryBornVectorLaw
  apply Measure.ae_smul_measure
  simp only [ae_finsetSum_measure_iff, Finset.mem_univ, forall_const]
  intro e b
  apply Measure.ae_smul_measure
  have hset : MeasurableSet
      {x : EuclideanSpace ℂ (Fin D) | ‖x‖ ^ 2 = (D : ℝ) + 1} :=
    measurableSet_eq.preimage (measurable_norm.pow_const 2)
  exact (ae_dirac_iff hset).2
    (candidate2ScaledMeasurementVector_norm_sq (U e) b)

theorem memLp_id_finiteUnitaryBornVectorLaw
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) (p : ℝ≥0∞) :
    MemLp id p (finiteUnitaryBornVectorLaw U rho) := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  exact PeriodicForwardCovariance.fixedNorm_memLp
    (ae_fixedNorm_finiteUnitaryBornVectorLaw U rho) p

/-- The literal Born vector law after adjoining an independent uniform
quarter phase. -/
def finiteUnitaryPhaseRandomizedBornVectorLaw
    (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    Measure (EuclideanSpace ℂ (Fin D)) :=
  phaseRandomizedLaw (finiteUnitaryBornVectorLaw U rho)

theorem finiteUnitaryPhaseRandomizedBornVectorLaw_isProbability
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    IsProbabilityMeasure
      (finiteUnitaryPhaseRandomizedBornVectorLaw U rho) := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  unfold finiteUnitaryPhaseRandomizedBornVectorLaw
  infer_instance

theorem integral_id_finiteUnitaryPhaseRandomizedBornVectorLaw_eq_zero
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    ∫ x, x ∂finiteUnitaryPhaseRandomizedBornVectorLaw U rho = 0 := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  unfold finiteUnitaryPhaseRandomizedBornVectorLaw
  apply integral_id_phaseRandomizedLaw_eq_zero
  exact memLp_one_iff_integrable.mp
    (memLp_id_finiteUnitaryBornVectorLaw hD U rho 1)

theorem ae_fixedNorm_finiteUnitaryPhaseRandomizedBornVectorLaw
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    ∀ᵐ x ∂finiteUnitaryPhaseRandomizedBornVectorLaw U rho,
      ‖x‖ ^ 2 = (D : ℝ) + 1 := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  unfold finiteUnitaryPhaseRandomizedBornVectorLaw
  exact ae_fixedNorm_phaseRandomizedLaw
    (ae_fixedNorm_finiteUnitaryBornVectorLaw U rho)

/-- Feed a complex marginal estimate for the literal Born vector law into
the real Candidate 2 covariance interface.  The only remaining statistical
premise is the displayed complex L6--L2 estimate; no sample-covariance bound
is hidden here. -/
theorem hasL6L2Marginals_finiteUnitaryPhaseRandomizedBornVectorLaw
    (hD : 0 < D) (U : A → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    {kappaComplex kappaReal : ℝ}
    (hL6 : Candidate2PhaseRandomizedL6L2.HasComplexL6L2Marginals
      (finiteUnitaryBornVectorLaw U rho) kappaComplex)
    (hscale : 4 * kappaComplex ^ 6 ≤ kappaReal ^ 6) :
    PeriodicForwardCovariance.HasL6L2Marginals
      (finiteUnitaryPhaseRandomizedBornVectorLaw U rho) kappaReal := by
  letI : IsProbabilityMeasure (finiteUnitaryBornVectorLaw U rho) :=
    finiteUnitaryBornVectorLaw_isProbability hD U rho
  unfold finiteUnitaryPhaseRandomizedBornVectorLaw
  exact Candidate2PhaseRandomizedL6L2.hasL6L2Marginals_phaseRandomizedLaw
    (memLp_id_finiteUnitaryBornVectorLaw hD U rho 2)
    (memLp_id_finiteUnitaryBornVectorLaw hD U rho 6) hL6 hscale

/-! ## Literal periodic shallow specialization -/

/-- The unphased vector law of the concrete periodic two-layer Cho--Kim
measurement experiment. -/
def choKimPeriodicBornVectorLaw
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n))) :
    Measure (EuclideanSpace ℂ (Fin (2 ^ n))) :=
  finiteUnitaryBornVectorLaw
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho

/-- The centered realification law to which the real covariance theorem is
intended to be applied in the literal periodic shallow experiment. -/
def choKimPeriodicPhaseRandomizedBornVectorLaw
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n))) :
    Measure (EuclideanSpace ℂ (Fin (2 ^ n))) :=
  finiteUnitaryPhaseRandomizedBornVectorLaw
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho

theorem choKimPeriodicBornVectorLaw_isProbability
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n))) :
    IsProbabilityMeasure (choKimPeriodicBornVectorLaw hdiv rho) := by
  unfold choKimPeriodicBornVectorLaw
  exact finiteUnitaryBornVectorLaw_isProbability (by positivity)
    (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho

theorem choKimPeriodicPhaseRandomizedBornVectorLaw_isProbability
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n))) :
    IsProbabilityMeasure
      (choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho) := by
  unfold choKimPeriodicPhaseRandomizedBornVectorLaw
  exact finiteUnitaryPhaseRandomizedBornVectorLaw_isProbability
    (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho

theorem integral_id_choKimPeriodicPhaseRandomizedBornVectorLaw_eq_zero
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n))) :
    ∫ x, x ∂choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho = 0 := by
  unfold choKimPeriodicPhaseRandomizedBornVectorLaw
  exact integral_id_finiteUnitaryPhaseRandomizedBornVectorLaw_eq_zero
    (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho

theorem ae_fixedNorm_choKimPeriodicPhaseRandomizedBornVectorLaw
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n))) :
    ∀ᵐ x ∂choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho,
      ‖x‖ ^ 2 = ((2 ^ n : ℕ) : ℝ) + 1 := by
  unfold choKimPeriodicPhaseRandomizedBornVectorLaw
  exact ae_fixedNorm_finiteUnitaryPhaseRandomizedBornVectorLaw
    (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho

/-- Exact final moment-interface bridge for the literal periodic shallow
Born law.  The complex marginal hypothesis is the remaining fourth-moment to
sixth-Born-moment specialization; the missing Bai--Yin concentration theorem
is not present in this statement. -/
theorem hasL6L2Marginals_choKimPeriodicPhaseRandomizedBornVectorLaw
    {n K : ℕ} (hdiv : K ∣ n) (rho : DensityOperator (Fin (2 ^ n)))
    {kappaComplex kappaReal : ℝ}
    (hL6 : Candidate2PhaseRandomizedL6L2.HasComplexL6L2Marginals
      (choKimPeriodicBornVectorLaw hdiv rho) kappaComplex)
    (hscale : 4 * kappaComplex ^ 6 ≤ kappaReal ^ 6) :
    PeriodicForwardCovariance.HasL6L2Marginals
      (choKimPeriodicPhaseRandomizedBornVectorLaw hdiv rho) kappaReal := by
  unfold choKimPeriodicBornVectorLaw at hL6
  unfold choKimPeriodicPhaseRandomizedBornVectorLaw
  exact hasL6L2Marginals_finiteUnitaryPhaseRandomizedBornVectorLaw
    (by positivity) (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv) rho
      hL6 hscale

end

end TomographyOracleCore.Candidate2FiniteBornVectorLaw
