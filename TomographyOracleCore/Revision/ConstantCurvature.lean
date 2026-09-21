import TomographyOracleCore.BinaryCliffordPeriodicPOVMCurvature
import TomographyOracleCore.ChoKimBlockDimensionOptimization

namespace TomographyOracleCore

open MatrixReduction
noncomputable section

/-- Near-unit curvature available under the unchanged paper block condition. -/
def sharpPeriodicCurvature : ℝ := 32767 / 32768

theorem sharpPeriodicCurvature_pos : 0 < sharpPeriodicCurvature := by
  norm_num [sharpPeriodicCurvature]

theorem sharpPeriodicCurvature_le_one : sharpPeriodicCurvature ≤ 1 := by
  norm_num [sharpPeriodicCurvature]

/-- Retain the overlap dimension instead of replacing the exponent by log 2. -/
theorem ChoKimBlockCondition.curvatureExponent_le_one_div_32768
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    ((n / K : ℕ) : ℝ) * (((2 : ℝ) ^ K)⁻¹) ≤ 1 / 32768 := by
  by_cases hn : n = 0
  · simp [hn]
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let q : ℝ := choKimOverlapDimension K
  have hq0 : 0 < q := choKimOverlapDimension_pos K
  have hq128 : 128 < q := h.oneTwentyEight_lt_overlap hnpos
  have hhalf : 8 ≤ K / 2 := by
    by_contra hn8
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show K / 2 ≤ 7 by omega)
    norm_num [q, choKimOverlapDimension] at hq128 hp
    linarith
  have hq256 : 256 ≤ q := by
    have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hhalf
    norm_num [q, choKimOverlapDimension] at *
    exact hp
  have hqSq : q ^ 2 = (2 : ℝ) ^ K := by
    dsimp [q, choKimOverlapDimension]
    rw [← pow_mul, Nat.div_mul_cancel h.block_even.two_dvd]
  have hlog : 0 < Real.log 2 := log_two_pos
  have hKreal : 0 < (K : ℝ) := by exact_mod_cast h.block_pos
  have hdiv : K * (n / K) = n := Nat.mul_div_cancel' h.block_dvd
  have hcancel : (92 / Real.log 2) * ((n / K : ℕ) : ℝ) ≤ q := by
    apply (mul_le_mul_iff_of_pos_left hKreal).mp
    calc
      (K : ℝ) * ((92 / Real.log 2) * ((n / K : ℕ) : ℝ)) =
          (92 / Real.log 2) * (n : ℝ) := by
        rw [mul_left_comm, ← Nat.cast_mul, hdiv]
      _ ≤ (K : ℝ) * q := h.explicit_growth
  have hc : (128 : ℝ) ≤ 92 / Real.log 2 := by
    apply (le_div_iff₀ hlog).2
    nlinarith [Real.log_two_lt_d9]
  have hm : 128 * ((n / K : ℕ) : ℝ) ≤ q :=
    (mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg _)).trans hcancel
  rw [← hqSq]
  apply (mul_inv_le_iff₀ (sq_pos_of_pos hq0)).2
  have hqmul : 256 * q ≤ q ^ 2 := by nlinarith
  nlinarith

/-- Elementary Bernoulli-type lower bound without discarding the exponent. -/
theorem one_sub_mul_inv_le_inverse_one_add_inv_pow
    {z : ℝ} (hz : 0 < z) (m : ℕ) :
    1 - (m : ℝ) * z⁻¹ ≤ ((1 + z⁻¹)⁻¹) ^ m := by
  have hbase : Real.exp (-z⁻¹) ≤ (1 + z⁻¹)⁻¹ := by
    rw [Real.exp_neg]
    apply inv_anti₀ (by positivity : 0 < 1 + z⁻¹)
    simpa [add_comm] using Real.add_one_le_exp z⁻¹
  calc
    1 - (m : ℝ) * z⁻¹ ≤ Real.exp (-((m : ℝ) * z⁻¹)) := by
      simpa [sub_eq_add_neg, add_comm] using Real.add_one_le_exp (-((m : ℝ) * z⁻¹))
    _ = (Real.exp (-z⁻¹)) ^ m := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    _ ≤ ((1 + z⁻¹)⁻¹) ^ m :=
      pow_le_pow_left₀ (Real.exp_pos _).le hbase m

theorem ChoKimBlockCondition.sharp_le_curvatureFloor
    {n K : ℕ} (h : ChoKimBlockCondition n K) :
    sharpPeriodicCurvature ≤ choKimCurvatureFloor n K := by
  have hexp := h.curvatureExponent_le_one_div_32768
  have hbern := one_sub_mul_inv_le_inverse_one_add_inv_pow
    (pow_pos (by norm_num : (0 : ℝ) < 2) K) (n / K)
  change _ ≤ choKimCurvatureFloor n K at hbern
  norm_num [sharpPeriodicCurvature] at ⊢
  linarith

theorem ChoKimBlockCondition.sharp_le_calibrated_periodicTwoLayerHitProbability
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (sigma : Equiv.Perm (Fin ((n / K) * K)))
    (p : PauliLabel ((n / K) * K)) :
    sharpPeriodicCurvature ≤ ((2 : ℝ) ^ n + 1) *
      periodicTwoLayerHitProbability (n / K) K sigma p := by
  apply h.sharp_le_curvatureFloor.trans
  apply h.curvatureFloor_le_calibratedEigenvalueFloor.trans
  simpa [choKimCalibratedEigenvalueFloor, one_div] using
    mul_le_mul_of_nonneg_left (periodicTwoLayerHitProbability_floor h.block_pos sigma p)
      (show 0 ≤ (2 : ℝ) ^ n + 1 by positivity)

theorem ChoKimBlockCondition.periodicCalibratedBinaryChannel_curvature_sharp
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (X : Matrix (PauliBinaryWord ((n / K) * K))
      (PauliBinaryWord ((n / K) * K)) ℂ)
    (hX : X.IsHermitian) (htrace : X.trace = 0) :
    sharpPeriodicCurvature * hermitianFrobeniusNorm X hX ^ 2 ≤
      (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd X * X).trace.re := by
  apply complexLinearPauliChannel_curvature
    ((n / K) * K)
    (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd)
    choKimPeriodicCalibratedEigenvalue
    (choKimPeriodicCalibratedBinaryLinearChannel_hermitianPauli h.block_dvd)
    (sharpPeriodicCurvature)
  · intro p hp
    simpa [choKimPeriodicCalibratedEigenvalue] using
      h.sharp_le_calibrated_periodicTwoLayerHitProbability
        (cyclicQubitShift ((n / K) * K) (K / 2)) p
  · exact htrace

/-- Final literal curvature theorem for the genuine finite periodic unitary
projective POVM, on the paper's standard `Fin (2^n)` Hilbert space. -/
theorem ChoKimBlockCondition.finiteUnitaryCalibratedDensityChannel_curvature_sharp
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (sigma rho : DensityOperator (Fin (2 ^ n))) :
    sharpPeriodicCurvature *
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
  have hold := h.periodicCalibratedBinaryChannel_curvature_sharp X hX htraceX
  calc
    sharpPeriodicCurvature *
        hermitianFrobeniusNorm (sigma.matrix - rho.matrix)
          (sigma.sub_isHermitian rho) ^ 2 =
      sharpPeriodicCurvature * hermitianFrobeniusNorm X hX ^ 2 := by
        rw [hnorm]
    _ ≤ (choKimPeriodicCalibratedBinaryLinearChannel h.block_dvd X * X).trace.re :=
      hold
    _ = _ := henergy

end
end TomographyOracleCore
