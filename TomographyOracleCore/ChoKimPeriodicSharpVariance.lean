import TomographyOracleCore.ChoKimPeriodicVarianceOptimization

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators CStarAlgebra ComplexOrder ENNReal MatrixOrder
  Matrix.Norms.L2Operator

noncomputable section

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-!
# Sharp rational periodic Cho--Kim variance

The convenient error bound `2/3` gives variance `10`.  A direct rational
bound on the already-proved exact exponential improves the multiplicative
third-moment factor to `16081/10000`, hence the overlap and variance
coefficient to `48243/5000 = 9.6486`.
-/

/-- Rational envelope for the exact periodic exponential.  The proof uses
`40 x ≤ 19`, raises the desired inequality to the fortieth power, and uses
mathlib's certified decimal enclosure of `exp 1`. -/
theorem exp_sixtyThree_div_ninetyTwo_log_two_le_16081_div_10000 :
    Real.exp ((63 / 92 : ℝ) * Real.log 2) ≤ 16081 / 10000 := by
  let x : ℝ := (63 / 92 : ℝ) * Real.log 2
  have hx : 40 * x ≤ 19 := by
    dsimp [x]
    nlinarith [Real.log_two_lt_d9]
  have hpow : (Real.exp x) ^ 40 ≤ Real.exp 19 := by
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by norm_num at hx ⊢; linarith)
  have hepow : Real.exp 19 < (16081 / 10000 : ℝ) ^ 40 := by
    have he19 : Real.exp 19 = (Real.exp 1) ^ 19 := by
      simpa using Real.exp_nat_mul (1 : ℝ) 19
    rw [he19]
    calc
      (Real.exp 1) ^ 19 < (2.7182818286 : ℝ) ^ 19 :=
        pow_lt_pow_left₀ Real.exp_one_lt_d9 (by positivity) (by norm_num)
      _ < (16081 / 10000 : ℝ) ^ 40 := by norm_num
  apply le_of_pow_le_pow_left₀ (by norm_num : (40 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 16081 / 10000)
  exact hpow.trans hepow.le

/-- The exact periodic accumulated error plus one is at most `1.6081`. -/
theorem ChoKimBlockCondition.choKimPeriodicThirdDesignError_add_one_le_16081_div_10000
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    1 + choKimPeriodicThirdDesignError n K ≤ 16081 / 10000 := by
  exact (h.choKimPeriodicThirdDesignError_add_one_le_exp hn).trans
    exp_sixtyThree_div_ninetyTwo_log_two_le_16081_div_10000

/-- Any nonnegative overlap coefficient `kappa` transfers directly to the
same score-variance coefficient; the dimension ratio is at most one. -/
theorem variance_finiteUnitaryProjectiveScore_le_kappa_of_weightedOverlapSquare
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D))
    (kappa : ℝ) (hkappa : 0 ≤ kappa)
    (hoverlap : finiteUnitaryProjectiveWeightedOverlapSquare U rho u ≤
      kappa / (((D + 1 : ℕ) : ℝ) * ((D + 2 : ℕ) : ℝ))) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM D hD U).bornMeasure rho) ≤ kappa := by
  have hv :=
    variance_finiteUnitaryProjectiveScore_le_scaled_weightedOverlapSquare
      hD U rho u
  let d1 : ℝ := ((D + 1 : ℕ) : ℝ)
  let d2 : ℝ := ((D + 2 : ℕ) : ℝ)
  have hd1 : 0 < d1 := by positivity
  have hd2 : 0 < d2 := by positivity
  have hd12 : d1 ≤ d2 := by
    dsimp [d1, d2]
    exact_mod_cast (show D + 1 ≤ D + 2 by omega)
  have hs := mul_le_mul_of_nonneg_left
    (by simpa [d1, d2] using hoverlap) (sq_nonneg d1)
  have hratio : d1 ^ 2 * (kappa / (d1 * d2)) ≤ kappa := by
    have hquot : d1 / d2 ≤ 1 := (div_le_one hd2).2 hd12
    rw [show d1 ^ 2 * (kappa / (d1 * d2)) =
        kappa * (d1 / d2) by field_simp]
    nlinarith
  exact hv.trans (hs.trans (by simpa [d1, d2] using hratio))

/-- A C-star relative third-moment comparison whose multiplicative error is
at most `16081/10000` gives overlap coefficient `48243/5000`. -/
theorem finiteUnitaryProjectiveWeightedOverlapSquare_le_48243_div_5000_of_relativeCP_cstarMatrix
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hone : 1 + epsilon ≤ 16081 / 10000)
    (hrelative : RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin D))
        (TripleIndex (Fin D)) ℂ)
      epsilon
      (finiteUnitaryThirdTwirlLinearMap U)
      (unitaryHaarThirdTwirlLinearMap D)) :
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u ≤
      (48243 / 5000 : ℝ) /
        (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by
  letI : Nonempty (Fin D) := Fin.pos_iff_nonempty.mp hD
  have hhaar_nonnegative :=
    cpTracePairingOn_unitaryHaarThirdTwirl_nonnegative hD rho u hu
  have hhaar_le :=
    cpTracePairingOn_unitaryHaarThirdTwirl_le_six hD rho u hu
  calc
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u =
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (finiteUnitaryThirdTwirlLinearMap U)
          (densityDirectionTensor rho u) :=
      finiteUnitaryProjectiveWeightedOverlapSquare_eq_cpTracePairingOn
        U rho u
    _ ≤ (1 + epsilon) *
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      hrelative.cpTracePairingOn_le_upper_cstarMatrix
        (densityDirectionTensor_posSemidef rho u)
        (computationalDiagonalTensorCube_posSemidef D)
    _ ≤ (16081 / 10000 : ℝ) *
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      mul_le_mul_of_nonneg_right hone hhaar_nonnegative
    _ ≤ (16081 / 10000 : ℝ) *
        (6 / (((D : ℝ) + 1) * ((D : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hhaar_le (by norm_num)
    _ = (48243 / 5000 : ℝ) /
        (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by ring

/-- Sharp rational weighted-overlap bound for the literal periodic circuit. -/
theorem ChoKimBlockCondition.periodicWeightedOverlapSquare_le_48243_div_5000
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    finiteUnitaryProjectiveWeightedOverlapSquare
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u ≤
      (48243 / 5000 : ℝ) /
        ((((2 ^ n) + 1 : ℕ) : ℝ) *
          (((2 ^ n) + 2 : ℕ) : ℝ)) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    finiteUnitaryProjectiveWeightedOverlapSquare_le_48243_div_5000_of_relativeCP_cstarMatrix
      (by positivity : 0 < 2 ^ n)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      rho u hu
      (choKimPeriodicThirdDesignError n K)
      (h.choKimPeriodicThirdDesignError_add_one_le_16081_div_10000 hn)
      (h.relativeCPApproximation_periodicThirdDesign hn)

/-- Sharp rational one-copy variance bound for the literal periodic score. -/
theorem ChoKimBlockCondition.variance_periodicFiniteUnitaryProjectiveScore_le_48243_div_5000
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM (2 ^ n) (by positivity)
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)).bornMeasure
            rho) ≤ 48243 / 5000 := by
  apply variance_finiteUnitaryProjectiveScore_le_kappa_of_weightedOverlapSquare
    (kappa := 48243 / 5000) (by positivity : 0 < 2 ^ n)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u
    (by norm_num)
  exact h.periodicWeightedOverlapSquare_le_48243_div_5000 hn rho u hu

end

end TomographyOracleCore
