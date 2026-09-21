import TomographyOracleCore.BinaryCliffordPeriodicFinEnsemble
import TomographyOracleCore.BinaryPauliOneCopyCurvature

namespace TomographyOracleCore

open scoped BigOperators ENNReal ComplexOrder
open MatrixReduction
noncomputable section

section FiniteLinearChannel

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-- Complex-linear version of the uniform finite projective dephasing
channel.  On Hermitian inputs it agrees with the Born-weighted forward map. -/
noncomputable def finiteUnitaryProjectiveLinearChannel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ where
  toFun A := ((Fintype.card E : ℂ)⁻¹) •
    ∑ e : E, ∑ b : Fin D,
      ((A * finiteUnitaryMeasurementProjector (U e) b).trace) •
        finiteUnitaryMeasurementProjector (U e) b
  map_add' A B := by
    simp only [Matrix.add_mul, Matrix.trace_add, add_smul,
      Finset.sum_add_distrib]
    rw [smul_add]
  map_smul' c A := by
    ext i j
    simp only [Matrix.smul_mul, Matrix.trace_smul, Matrix.smul_apply,
      Matrix.sum_apply, smul_eq_mul, RingHom.id_apply]
    have hsum :
        (∑ e : E, ∑ b : Fin D,
          c * (A * finiteUnitaryMeasurementProjector (U e) b).trace *
            finiteUnitaryMeasurementProjector (U e) b i j) =
          c * (∑ e : E, ∑ b : Fin D,
            (A * finiteUnitaryMeasurementProjector (U e) b).trace *
              finiteUnitaryMeasurementProjector (U e) b i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      ring
    rw [hsum]
    ring

@[simp] theorem finiteUnitaryProjectiveLinearChannel_apply
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (A : Matrix (Fin D) (Fin D) ℂ) :
    finiteUnitaryProjectiveLinearChannel U A =
      ((Fintype.card E : ℂ)⁻¹) •
        ∑ e : E, ∑ b : Fin D,
          ((A * finiteUnitaryMeasurementProjector (U e) b).trace) •
            finiteUnitaryMeasurementProjector (U e) b := rfl

/-- On a difference of density matrices, the calibrated finite channel is
exactly `(D+1)` times its complex-linear dephasing channel. -/
theorem finiteUnitaryCalibratedDensityChannel_sub_eq_linearChannel
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (sigma rho : DensityOperator (Fin D)) :
    finiteUnitaryCalibratedDensityChannel U sigma -
        finiteUnitaryCalibratedDensityChannel U rho =
      (((D + 1 : ℕ) : ℝ) : ℂ) •
        finiteUnitaryProjectiveLinearChannel U
          (sigma.matrix - rho.matrix) := by
  classical
  have hnorm :
      ((Fintype.card E : ℕ) : ℝ≥0∞)⁻¹.toReal =
        (Fintype.card E : ℝ)⁻¹ := by
    simp [ENNReal.toReal_inv, Fintype.card_ne_zero]
  have hterm (e : E) (b : Fin D) :
      (((sigma.matrix * finiteUnitaryMeasurementProjector (U e) b).trace.re : ℝ) : ℂ) -
          (((rho.matrix * finiteUnitaryMeasurementProjector (U e) b).trace.re : ℝ) : ℂ) =
        ((sigma.matrix - rho.matrix) *
          finiteUnitaryMeasurementProjector (U e) b).trace := by
    have hs := trace_mul_eq_re_of_isHermitian sigma.matrix
      (finiteUnitaryMeasurementProjector (U e) b)
      sigma.isHermitian
      (finiteUnitaryMeasurementProjector_posSemidef (U e) b).isHermitian
    have hr := trace_mul_eq_re_of_isHermitian rho.matrix
      (finiteUnitaryMeasurementProjector (U e) b)
      rho.isHermitian
      (finiteUnitaryMeasurementProjector_posSemidef (U e) b).isHermitian
    rw [Matrix.sub_mul, Matrix.trace_sub, hs, hr]
    simp
  unfold finiteUnitaryCalibratedDensityChannel
    finiteUnitaryProjectiveDensityForward
  rw [finiteUnitaryProjectiveLinearChannel_apply]
  rw [sub_sub_sub_cancel_right]
  rw [← smul_sub]
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [hnorm]
  push_cast
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  push_cast
  rw [← smul_sub]
  congr 1
  rw [← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [← sub_smul]
  exact congrArg
    (fun c : ℂ ↦ c • finiteUnitaryMeasurementProjector (U e) b)
    (hterm e b)

/-- The selected-basis projector on a binary-word Hilbert space. -/
def binaryUnitaryMeasurementProjector
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (b : PauliBinaryWord N) :
    Matrix (PauliBinaryWord N) (PauliBinaryWord N) ℂ :=
  U.1.conjTranspose * computationalBasisProjector b * U.1

/-- Expand conjugated computational dephasing as the usual sum of Born
coefficients times the selected rank-one projectors. -/
theorem conjugatedComputationalBasisMeasurementChannel_eq_projector_sum
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (A : Matrix (PauliBinaryWord N) (PauliBinaryWord N) ℂ) :
    conjugatedComputationalBasisMeasurementChannel N U A =
      ∑ b : PauliBinaryWord N,
        (A * binaryUnitaryMeasurementProjector N U b).trace •
          binaryUnitaryMeasurementProjector N U b := by
  classical
  unfold conjugatedComputationalBasisMeasurementChannel
    computationalBasisMeasurementChannel binaryUnitaryMeasurementProjector
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Matrix.mul_smul, Matrix.smul_mul]
  apply congrArg (fun c : ℂ ↦ c •
    (U.1.conjTranspose * computationalBasisProjector b * U.1))
  calc
    ((U.1 * A * U.1.conjTranspose) *
        computationalBasisProjector b).trace =
        ((U.1 * A) *
          (U.1.conjTranspose * computationalBasisProjector b)).trace := by
          congr 1
          noncomm_ring
    _ = ((U.1.conjTranspose * computationalBasisProjector b) *
        (U.1 * A)).trace := Matrix.trace_mul_comm _ _
    _ = ((U.1.conjTranspose * computationalBasisProjector b * U.1) *
        A).trace := by
          congr 1
          noncomm_ring
    _ = (A * (U.1.conjTranspose * computationalBasisProjector b * U.1)).trace :=
      Matrix.trace_mul_comm _ _

@[simp] theorem trace_reindexAlgEquiv
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (A : Matrix α α ℂ) :
    (Matrix.reindexAlgEquiv ℂ ℂ e A).trace = A.trace := by
  unfold Matrix.trace
  simp only [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  exact Equiv.sum_comp e.symm (fun i ↦ A i i)

/-- Reindexing identifies the computational basis projectors literally. -/
theorem reindex_computationalBasisProjector
    {α : Type} {D : ℕ} [Fintype α]
    [DecidableEq α]
    (e : α ≃ Fin D) (b : α) :
    finiteComputationalBasisProjector (e b) =
      Matrix.reindexAlgEquiv ℂ ℂ e (Matrix.single b b 1) := by
  ext i j
  simp only [finiteComputationalBasisProjector, Matrix.single_apply,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]
  by_cases hi : e b = i <;> by_cases hj : e b = j <;>
    simp [hi, hj, Equiv.eq_symm_apply]

/-- Selected-basis projectors commute with a simultaneous basis reindex. -/
theorem finiteUnitaryMeasurementProjector_reindexUnitary
    {α : Type} {D : ℕ} [Fintype α]
    [DecidableEq α]
    (e : α ≃ Fin D) (U : Matrix.unitaryGroup α ℂ) (b : α) :
    finiteUnitaryMeasurementProjector (reindexUnitary e U) (e b) =
      Matrix.reindexAlgEquiv ℂ ℂ e
        (U.1.conjTranspose * Matrix.single b b 1 * U.1) := by
  unfold finiteUnitaryMeasurementProjector reindexUnitary
  rw [reindex_computationalBasisProjector]
  rw [← reindexAlgEquiv_conjTranspose]
  rw [map_mul, map_mul]

/-- The finite selected-basis channel of a reindexed binary-word ensemble is
exactly the reindexing of the literal conjugated-dephasing average. -/
theorem finiteUnitaryProjectiveLinearChannel_reindex_binary
    {N D : ℕ} {E : Type*} [Fintype E] [Nonempty E]
    (idx : PauliBinaryWord N ≃ Fin D)
    (U : E → Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (A : Matrix (PauliBinaryWord N) (PauliBinaryWord N) ℂ) :
    finiteUnitaryProjectiveLinearChannel
        (fun x ↦ reindexUnitary idx (U x))
        (Matrix.reindexAlgEquiv ℂ ℂ idx A) =
      Matrix.reindexAlgEquiv ℂ ℂ idx
        (((Fintype.card E : ℂ)⁻¹) •
          ∑ x : E,
            conjugatedComputationalBasisMeasurementChannel N (U x) A) := by
  classical
  rw [finiteUnitaryProjectiveLinearChannel_apply, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [conjugatedComputationalBasisMeasurementChannel_eq_projector_sum,
    map_sum]
  rw [← Equiv.sum_comp idx]
  apply Finset.sum_congr rfl
  intro b hb
  rw [finiteUnitaryMeasurementProjector_reindexUnitary]
  rw [← map_mul, trace_reindexAlgEquiv, map_smul]
  rfl

/-- Named form of the exact block-word reindexing used by the concrete
Cho--Kim unitary family. -/
noncomputable def choKimBlockWordEquivFin
    {n K : ℕ} (hdiv : K ∣ n) :
    PauliBinaryWord ((n / K) * K) ≃ Fin (2 ^ n) :=
  computableChoKimBlockIndex hdiv

/-- Exact channel transport for the concrete periodic Cho--Kim ensemble. -/
theorem finiteUnitaryProjectiveLinearChannel_choKim_reindex
    {n K : ℕ} (hdiv : K ∣ n)
    (A : Matrix (PauliBinaryWord ((n / K) * K))
      (PauliBinaryWord ((n / K) * K)) ℂ) :
    finiteUnitaryProjectiveLinearChannel
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)
        (Matrix.reindexAlgEquiv ℂ ℂ
          (choKimBlockWordEquivFin hdiv) A) =
      Matrix.reindexAlgEquiv ℂ ℂ
        (choKimBlockWordEquivFin hdiv)
        (averagedPeriodicTwoLayerMeasurementChannel (n / K) K
          (cyclicQubitShift ((n / K) * K) (K / 2)) A) := by
  simpa [choKimPeriodicTwoLayerCliffordUnitaryFin,
    choKimBlockWordEquivFin,
    choKimPeriodicTwoLayerCliffordUnitary,
    averagedPeriodicTwoLayerMeasurementChannel] using
    (finiteUnitaryProjectiveLinearChannel_reindex_binary
      (idx := choKimBlockWordEquivFin hdiv)
      (U := fun e : PeriodicTwoLayerCliffordEnsemble (n / K) K ↦
        choKimPeriodicTwoLayerCliffordUnitary (n / K) K e) A)

/-- Pull the concrete finite channel back to the binary-word basis where the
proved Pauli diagonalization and counting theorem apply. -/
noncomputable def choKimPeriodicBinaryMeasurementLinearChannel
    {n K : ℕ} (hdiv : K ∣ n) :
    Matrix (PauliBinaryWord ((n / K) * K))
        (PauliBinaryWord ((n / K) * K)) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord ((n / K) * K))
        (PauliBinaryWord ((n / K) * K)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ
      (choKimBlockWordEquivFin hdiv)).symm.toLinearMap.comp
    ((finiteUnitaryProjectiveLinearChannel
        (choKimPeriodicTwoLayerCliffordUnitaryFin hdiv)).comp
      (Matrix.reindexAlgEquiv ℂ ℂ
        (choKimBlockWordEquivFin hdiv)).toLinearMap)

@[simp] theorem choKimPeriodicBinaryMeasurementLinearChannel_apply
    {n K : ℕ} (hdiv : K ∣ n)
    (A : Matrix (PauliBinaryWord ((n / K) * K))
      (PauliBinaryWord ((n / K) * K)) ℂ) :
    choKimPeriodicBinaryMeasurementLinearChannel hdiv A =
      averagedPeriodicTwoLayerMeasurementChannel (n / K) K
        (cyclicQubitShift ((n / K) * K) (K / 2)) A := by
  unfold choKimPeriodicBinaryMeasurementLinearChannel
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
    AlgEquiv.toLinearMap_apply]
  rw [finiteUnitaryProjectiveLinearChannel_choKim_reindex]
  exact (Matrix.reindexAlgEquiv ℂ ℂ
    (choKimBlockWordEquivFin hdiv)).symm_apply_apply _

/-- Calibrated Pauli eigenvalue of the concrete periodic ensemble. -/
noncomputable def choKimPeriodicCalibratedEigenvalue
    {n K : ℕ} (p : PauliLabel ((n / K) * K)) : ℝ :=
  ((2 : ℝ) ^ n + 1) *
    periodicTwoLayerHitProbability (n / K) K
      (cyclicQubitShift ((n / K) * K) (K / 2)) p

/-- The calibrated pulled-back channel. -/
noncomputable def choKimPeriodicCalibratedBinaryLinearChannel
    {n K : ℕ} (hdiv : K ∣ n) :
    Matrix (PauliBinaryWord ((n / K) * K))
        (PauliBinaryWord ((n / K) * K)) ℂ →ₗ[ℂ]
      Matrix (PauliBinaryWord ((n / K) * K))
        (PauliBinaryWord ((n / K) * K)) ℂ :=
  (((2 : ℝ) ^ n + 1 : ℝ) : ℂ) •
    choKimPeriodicBinaryMeasurementLinearChannel hdiv

/-- Literal calibrated periodic channel diagonalization in the Hermitian
binary Pauli basis. -/
theorem choKimPeriodicCalibratedBinaryLinearChannel_hermitianPauli
    {n K : ℕ} (hdiv : K ∣ n)
    (p : PauliLabel ((n / K) * K)) :
    choKimPeriodicCalibratedBinaryLinearChannel hdiv
        (hermitianBinaryPauliMatrix ((n / K) * K) p) =
      (choKimPeriodicCalibratedEigenvalue p : ℂ) •
        hermitianBinaryPauliMatrix ((n / K) * K) p := by
  unfold choKimPeriodicCalibratedBinaryLinearChannel
    choKimPeriodicCalibratedEigenvalue
  rw [LinearMap.smul_apply, hermitianBinaryPauliMatrix,
    map_smul, choKimPeriodicBinaryMeasurementLinearChannel_apply,
    averagedPeriodicTwoLayerMeasurementChannel_binaryPauli_eq_hitProbability]
  simp only [smul_smul]
  apply congrArg (fun c : ℂ ↦ c • binaryPauliMatrix ((n / K) * K) p)
  push_cast
  ring

/-- Simultaneous reindexing preserves the squared Hermitian Frobenius norm. -/
theorem hermitianFrobeniusNorm_reindexAlgEquiv_sq
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (idx : α ≃ β) (A : Matrix α α ℂ) (hA : A.IsHermitian) :
    hermitianFrobeniusNorm
        (Matrix.reindexAlgEquiv ℂ ℂ idx A) (by
          simpa only [Matrix.reindexAlgEquiv_apply] using hA.reindex idx) ^ 2 =
      hermitianFrobeniusNorm A hA ^ 2 := by
  let hRA : (Matrix.reindexAlgEquiv ℂ ℂ idx A).IsHermitian := by
    simpa only [Matrix.reindexAlgEquiv_apply] using hA.reindex idx
  have htrace :
      ((Matrix.reindexAlgEquiv ℂ ℂ idx A) *
        Matrix.reindexAlgEquiv ℂ ℂ idx A).trace =
          (A * A).trace := by
    rw [← map_mul, trace_reindexAlgEquiv]
  have hsquare :
      hermitianFrobeniusSq
          (Matrix.reindexAlgEquiv ℂ ℂ idx A) hRA =
        hermitianFrobeniusSq A hA := by
    have hleft := trace_sq_eq_hermitianFrobeniusSq
      (Matrix.reindexAlgEquiv ℂ ℂ idx A) hRA
    have hright := trace_sq_eq_hermitianFrobeniusSq A hA
    have hc :
        ((hermitianFrobeniusSq
          (Matrix.reindexAlgEquiv ℂ ℂ idx A) hRA : ℝ) : ℂ) =
          ((hermitianFrobeniusSq A hA : ℝ) : ℂ) := by
      rw [← hleft, ← hright, htrace]
    exact_mod_cast hc
  rw [hermitianFrobeniusNorm_sq, hermitianFrobeniusNorm_sq]
  exact hsquare

/-- The concrete calibrated pulled-back binary channel has the requested
universal curvature floor. -/
theorem ChoKimBlockCondition.periodicCalibratedBinaryChannel_curvature
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (X : Matrix (PauliBinaryWord ((n / K) * K))
      (PauliBinaryWord ((n / K) * K)) ℂ)
    (hX : X.IsHermitian) (htrace : X.trace = 0) :
    (1 : ℝ) / 2 * hermitianFrobeniusNorm X hX ^ 2 ≤
      (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd X * X).trace.re := by
  apply complexLinearPauliChannel_curvature
    ((n / K) * K)
    (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd)
    choKimPeriodicCalibratedEigenvalue
    (choKimPeriodicCalibratedBinaryLinearChannel_hermitianPauli h.block_dvd)
    ((1 : ℝ) / 2)
  · intro p hp
    simpa [choKimPeriodicCalibratedEigenvalue] using
      h.half_le_calibrated_periodicTwoLayerHitProbability
        (cyclicQubitShift ((n / K) * K) (K / 2)) p
  · exact htrace

/-- Final literal curvature theorem for the genuine finite periodic unitary
projective POVM, on the paper's standard `Fin (2^n)` Hilbert space. -/
theorem ChoKimBlockCondition.finiteUnitaryCalibratedDensityChannel_curvature
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (sigma rho : DensityOperator (Fin (2 ^ n))) :
    (1 : ℝ) / 2 *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) ^ 2 ≤
      hermitianForwardEnergy sigma rho
        (finiteUnitaryCalibratedDensityChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) sigma -
          finiteUnitaryCalibratedDensityChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho) := by
  let idx := choKimBlockWordEquivFin h.block_dvd
  let delta := sigma.matrix - rho.matrix
  let X := Matrix.reindexAlgEquiv ℂ ℂ idx.symm delta
  have hdelta : delta.IsHermitian := by
    simpa [delta] using sigma.sub_isHermitian rho
  have hX : X.IsHermitian := by
    simpa only [X, Matrix.reindexAlgEquiv_apply] using hdelta.reindex idx.symm
  have htraceDelta : delta.trace = 0 := by
    simp [delta, Matrix.trace_sub, sigma.trace_eq_one, rho.trace_eq_one]
  have htraceX : X.trace = 0 := by
    change (Matrix.reindexAlgEquiv ℂ ℂ idx.symm delta).trace = 0
    rw [trace_reindexAlgEquiv]
    exact htraceDelta
  have hnorm :
      hermitianFrobeniusNorm X hX ^ 2 =
        hermitianFrobeniusNorm delta hdelta ^ 2 := by
    simpa [X] using
      (hermitianFrobeniusNorm_reindexAlgEquiv_sq idx.symm delta hdelta)
  have hdeltaReindex :
      Matrix.reindexAlgEquiv ℂ ℂ idx X = delta := by
    simp [X]
  have hlinear :
      finiteUnitaryProjectiveLinearChannel
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) delta =
        Matrix.reindexAlgEquiv ℂ ℂ idx
          (choKimPeriodicBinaryMeasurementLinearChannel h.block_dvd X) := by
    rw [← hdeltaReindex]
    rw [finiteUnitaryProjectiveLinearChannel_choKim_reindex]
    rw [choKimPeriodicBinaryMeasurementLinearChannel_apply]
  have hforward :
      finiteUnitaryCalibratedDensityChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) sigma -
          finiteUnitaryCalibratedDensityChannel
            (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho =
        Matrix.reindexAlgEquiv ℂ ℂ idx
          (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd X) := by
    rw [finiteUnitaryCalibratedDensityChannel_sub_eq_linearChannel, hlinear]
    unfold choKimPeriodicCalibratedBinaryLinearChannel
    rw [LinearMap.smul_apply, map_smul]
    congr 2 <;> norm_num
  have henergy :
      (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd X * X).trace.re =
        hermitianForwardEnergy sigma rho
          (finiteUnitaryCalibratedDensityChannel
              (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) sigma -
            finiteUnitaryCalibratedDensityChannel
              (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho) := by
    unfold hermitianForwardEnergy
    change _ =
      ((finiteUnitaryCalibratedDensityChannel
              (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) sigma -
            finiteUnitaryCalibratedDensityChannel
              (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho) *
        delta).trace.re
    rw [hforward, ← hdeltaReindex, ← map_mul, trace_reindexAlgEquiv]
  have hold := h.periodicCalibratedBinaryChannel_curvature X hX htraceX
  calc
    (1 : ℝ) / 2 *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) ^ 2 =
      (1 : ℝ) / 2 * hermitianFrobeniusNorm X hX ^ 2 := by
        rw [hnorm]
    _ ≤ (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd X * X).trace.re :=
      hold
    _ = _ := henergy

end FiniteLinearChannel

end
end TomographyOracleCore
