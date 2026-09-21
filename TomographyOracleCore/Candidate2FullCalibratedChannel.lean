import TomographyOracleCore.BinaryCliffordPeriodicPOVMCurvature

namespace TomographyOracleCore

open scoped BigOperators ENNReal ComplexOrder
open MatrixReduction
noncomputable section

/-!
# Full calibrated linear channel for Candidate 2

The calibrated density forward map subtracts the identity because density
matrices have trace one.  Its complex-linear extension to arbitrary matrices
must therefore subtract `trace(A) I`, not `I`.  This module records that full
linear channel and its exact Pauli eigenvalues, including eigenvalue one on
the identity Pauli.
-/

section GenericFiniteEnsemble

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- The complex-linear map `A ↦ trace(A) I`. -/
noncomputable def traceIdentityLinearChannel :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun A := A.trace • (1 : Matrix (Fin D) (Fin D) ℂ)
  map_add' A B := by
    rw [Matrix.trace_add, add_smul]
  map_smul' c A := by
    simp only [Matrix.trace_smul, smul_smul, RingHom.id_apply, smul_eq_mul]

@[simp] theorem traceIdentityLinearChannel_apply
    (A : Matrix (Fin D) (Fin D) ℂ) :
    traceIdentityLinearChannel A =
      A.trace • (1 : Matrix (Fin D) (Fin D) ℂ) := rfl

/-- The full linear extension of the calibrated finite measurement channel:
`L(A) = (D+1) M(A) - trace(A) I`. -/
noncomputable def finiteUnitaryFullCalibratedLinearChannel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  (((((D + 1 : ℕ) : ℝ) : ℂ) •
      finiteUnitaryProjectiveLinearChannel U) -
    traceIdentityLinearChannel)

@[simp] theorem finiteUnitaryFullCalibratedLinearChannel_apply
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A : Matrix (Fin D) (Fin D) ℂ) :
    finiteUnitaryFullCalibratedLinearChannel U A =
      (((D + 1 : ℕ) : ℝ) : ℂ) •
          finiteUnitaryProjectiveLinearChannel U A -
        A.trace • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  rfl

/-- The complex-linear projective channel agrees with the Born-weighted
forward map on density matrices. -/
theorem finiteUnitaryProjectiveLinearChannel_density
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    finiteUnitaryProjectiveLinearChannel U rho.matrix =
      finiteUnitaryProjectiveDensityForward U rho := by
  classical
  have hnorm :
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal =
        (Fintype.card E : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, Fintype.card_ne_zero]
  have hterm (e : E) (b : Fin D) :
      (rho.matrix * finiteUnitaryMeasurementProjector (U e) b).trace =
        (((rho.matrix *
          finiteUnitaryMeasurementProjector (U e) b).trace.re : ℝ) : ℂ) := by
    exact trace_mul_eq_re_of_isHermitian rho.matrix
      (finiteUnitaryMeasurementProjector (U e) b)
      rho.isHermitian
      (finiteUnitaryMeasurementProjector_posSemidef (U e) b).isHermitian
  unfold finiteUnitaryProjectiveDensityForward
  rw [finiteUnitaryProjectiveLinearChannel_apply, hnorm]
  push_cast
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro b hb
  rw [hterm]
  simp

/-- Every finite projective measurement channel fixes the identity matrix. -/
theorem finiteUnitaryProjectiveLinearChannel_one
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    finiteUnitaryProjectiveLinearChannel U
        (1 : Matrix (Fin D) (Fin D) ℂ) = 1 := by
  rw [finiteUnitaryProjectiveLinearChannel_apply]
  simp only [Matrix.one_mul, finiteUnitaryMeasurementProjector_trace,
    one_smul]
  rw [sum_finiteUnitaryMeasurementProjector_ensemble]
  simp [Fintype.card_ne_zero]

/-- On density matrices, the full linear channel is exactly the original
calibrated affine formula. -/
theorem finiteUnitaryFullCalibratedLinearChannel_density
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D)) :
    finiteUnitaryFullCalibratedLinearChannel U rho.matrix =
      finiteUnitaryCalibratedDensityChannel U rho := by
  rw [finiteUnitaryFullCalibratedLinearChannel_apply,
    finiteUnitaryProjectiveLinearChannel_density, rho.trace_eq_one]
  unfold finiteUnitaryCalibratedDensityChannel
  simp only [one_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- The full channel transports a difference of density matrices to the
difference of their calibrated forward images. -/
theorem finiteUnitaryFullCalibratedLinearChannel_density_sub
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (sigma rho : DensityOperator (Fin D)) :
    finiteUnitaryFullCalibratedLinearChannel U
        (sigma.matrix - rho.matrix) =
      finiteUnitaryCalibratedDensityChannel U sigma -
        finiteUnitaryCalibratedDensityChannel U rho := by
  rw [map_sub, finiteUnitaryFullCalibratedLinearChannel_density,
    finiteUnitaryFullCalibratedLinearChannel_density]

end GenericFiniteEnsemble

section BinaryPeriodic

/-- Exact trace of an unphased binary Pauli. -/
theorem binaryPauliMatrix_trace (K : ℕ) (p : PauliLabel K) :
    (binaryPauliMatrix K p).trace =
      if p = 0 then ((2 : ℂ) ^ K) else 0 := by
  classical
  by_cases hp : p = 0
  · subst p
    rw [if_pos rfl, binaryPauliMatrix_zero]
    simp [PauliBinaryWord]
  · rw [if_neg hp]
    unfold Matrix.trace Matrix.diag
    by_cases hx : p.1 = 0
    · have hz : p.2 ≠ 0 := by
        intro hz
        apply hp
        exact Prod.ext hx hz
      simp only [binaryPauliMatrix, hx, add_zero, if_true]
      exact_mod_cast sum_binaryWordCharacter_eq_zero K hz
    · apply Finset.sum_eq_zero
      intro b hb
      simp only [binaryPauliMatrix]
      rw [if_neg]
      exact fun h ↦ hx ((binaryWord_eq_add_iff_right_eq_zero K b p.1).mp h)

/-- Exact trace of a Hermitian binary Pauli. -/
theorem hermitianBinaryPauliMatrix_trace (K : ℕ) (p : PauliLabel K) :
    (hermitianBinaryPauliMatrix K p).trace =
      if p = 0 then ((2 : ℂ) ^ K) else 0 := by
  rw [hermitianBinaryPauliMatrix, Matrix.trace_smul,
    binaryPauliMatrix_trace]
  by_cases hp : p = 0
  · subst p
    simp [hermitianPauliPhase]
  · simp [hp]

/-- The concrete periodic projective channel is unital. -/
theorem choKimPeriodicBinaryMeasurementLinearChannel_one
    {n K : ℕ} (hdiv : K ∣ n) :
    choKimPeriodicBinaryMeasurementLinearChannel hdiv
        (1 : Matrix (PauliBinaryWord ((n / K) * K))
          (PauliBinaryWord ((n / K) * K)) ℂ) = 1 := by
  unfold choKimPeriodicBinaryMeasurementLinearChannel
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply, map_one]
  rw [finiteUnitaryProjectiveLinearChannel_one]
  simp

/-- Correct full Candidate-2 channel on the binary-word model:
`L(A) = (2^n+1) M(A) - trace(A) I`. -/
noncomputable def choKimPeriodicFullCalibratedBinaryLinearChannel
    {n K : ℕ} (hdiv : K ∣ n) :
    Matrix (PauliBinaryWord ((n / K) * K))
        (PauliBinaryWord ((n / K) * K)) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord ((n / K) * K))
        (PauliBinaryWord ((n / K) * K)) ℂ :=
  (((((2 : ℝ) ^ n + 1 : ℝ) : ℂ) •
      choKimPeriodicBinaryMeasurementLinearChannel hdiv) -
    { toFun := fun A ↦ A.trace •
          (1 : Matrix (PauliBinaryWord ((n / K) * K))
            (PauliBinaryWord ((n / K) * K)) ℂ)
      map_add' := by
        intro A B
        rw [Matrix.trace_add, add_smul]
      map_smul' := by
        intro c A
        simp only [Matrix.trace_smul, smul_smul, RingHom.id_apply,
          smul_eq_mul] })

@[simp] theorem choKimPeriodicFullCalibratedBinaryLinearChannel_apply
    {n K : ℕ} (hdiv : K ∣ n)
    (A : Matrix (PauliBinaryWord ((n / K) * K))
      (PauliBinaryWord ((n / K) * K)) ℂ) :
    choKimPeriodicFullCalibratedBinaryLinearChannel hdiv A =
      (((2 : ℝ) ^ n + 1 : ℝ) : ℂ) •
          choKimPeriodicBinaryMeasurementLinearChannel hdiv A -
        A.trace •
          (1 : Matrix (PauliBinaryWord ((n / K) * K))
            (PauliBinaryWord ((n / K) * K)) ℂ) := by
  rfl

/-- Full eigenvalue: one on the identity and the calibrated hit probability
on every nonidentity Pauli. -/
noncomputable def choKimPeriodicFullCalibratedEigenvalue
    {n K : ℕ} (p : PauliLabel ((n / K) * K)) : ℝ :=
  if p = 0 then 1 else choKimPeriodicCalibratedEigenvalue p

/-- Exact diagonalization of the full periodic channel, including identity
eigenvalue one. -/
theorem choKimPeriodicFullCalibratedBinaryLinearChannel_hermitianPauli
    {n K : ℕ} (hdiv : K ∣ n)
    (p : PauliLabel ((n / K) * K)) :
    choKimPeriodicFullCalibratedBinaryLinearChannel hdiv
        (hermitianBinaryPauliMatrix ((n / K) * K) p) =
      (choKimPeriodicFullCalibratedEigenvalue p : ℂ) •
        hermitianBinaryPauliMatrix ((n / K) * K) p := by
  classical
  by_cases hp : p = 0
  · subst p
    rw [hermitianBinaryPauliMatrix_zero,
      choKimPeriodicFullCalibratedBinaryLinearChannel_apply,
      choKimPeriodicBinaryMeasurementLinearChannel_one]
    have hcard :
        Fintype.card (PauliBinaryWord ((n / K) * K)) = 2 ^ n := by
      simp [PauliBinaryWord, Nat.div_mul_cancel hdiv]
    rw [Matrix.trace_one, hcard]
    simp only [choKimPeriodicFullCalibratedEigenvalue, if_pos, one_smul]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  · rw [choKimPeriodicFullCalibratedBinaryLinearChannel_apply]
    change choKimPeriodicCalibratedBinaryLinearChannel hdiv
        (hermitianBinaryPauliMatrix ((n / K) * K) p) -
          (hermitianBinaryPauliMatrix ((n / K) * K) p).trace •
            (1 : Matrix (PauliBinaryWord ((n / K) * K))
              (PauliBinaryWord ((n / K) * K)) ℂ) = _
    rw [choKimPeriodicCalibratedBinaryLinearChannel_hermitianPauli,
      hermitianBinaryPauliMatrix_trace]
    simp [hp, choKimPeriodicFullCalibratedEigenvalue]

end BinaryPeriodic

end
end TomographyOracleCore
