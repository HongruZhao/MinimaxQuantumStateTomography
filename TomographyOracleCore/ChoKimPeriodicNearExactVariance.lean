import TomographyOracleCore.ChoKimPeriodicSharpVariance

namespace TomographyOracleCore

open MeasureTheory ProbabilityTheory
open MatrixReduction PhysicalPOVM
open scoped BigOperators CStarAlgebra ComplexOrder ENNReal MatrixOrder
  Matrix.Norms.L2Operator

noncomputable section

variable {D : ℕ} {E : Type*} [Fintype E] [Nonempty E]

/-!
# Near-exact rational periodic Cho--Kim variance

The exact exponential factor satisfies a useful algebraic identity after
raising it to the `920`th power.  A fully checked integer comparison then
gives the tight rational envelope `1.60746`, only about `2.6e-7` above the
exact value.  The resulting overlap and variance coefficient is
`241119/25000 = 9.64476`.
-/

/-- Near-exact rational envelope obtained from
`(exp ((63/92) log 2))^920 = 2^630`. -/
theorem exp_sixtyThree_div_ninetyTwo_log_two_le_160746_div_100000 :
    Real.exp ((63 / 92 : ℝ) * Real.log 2) ≤ 160746 / 100000 := by
  let x : ℝ := (63 / 92 : ℝ) * Real.log 2
  have hpow : (Real.exp x) ^ 920 = (2 : ℝ) ^ 630 := by
    rw [← Real.exp_nat_mul]
    have hx : (920 : ℝ) * x = (630 : ℕ) * Real.log 2 := by
      dsimp [x]
      norm_num
      ring
    calc
      Real.exp ((920 : ℕ) * x) =
          Real.exp ((630 : ℕ) * Real.log 2) := congrArg Real.exp hx
      _ = (2 : ℝ) ^ 630 := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hrat : (2 : ℝ) ^ 630 ≤ (160746 / 100000 : ℝ) ^ 920 := by
    norm_num [div_pow]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 50000 ^ 920)).2
    have hn : (2 : ℕ) ^ 630 * 50000 ^ 920 ≤ 80373 ^ 920 := by
      set_option maxRecDepth 100000 in
        decide
    exact_mod_cast hn
  apply le_of_pow_le_pow_left₀ (by norm_num : (920 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 160746 / 100000)
  rw [hpow]
  exact hrat

/-- Near-exact multiplicative error bound for the literal periodic circuit. -/
theorem ChoKimBlockCondition.choKimPeriodicThirdDesignError_add_one_le_160746_div_100000
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n) :
    1 + choKimPeriodicThirdDesignError n K ≤ 160746 / 100000 := by
  exact (h.choKimPeriodicThirdDesignError_add_one_le_exp hn).trans
    exp_sixtyThree_div_ninetyTwo_log_two_le_160746_div_100000

/-- Near-exact C-star relative-design consumer. -/
theorem finiteUnitaryProjectiveWeightedOverlapSquare_le_241119_div_25000_of_relativeCP_cstarMatrix
    (hD : 0 < D)
    (U : E → Matrix.unitaryGroup (Fin D) ℂ)
    (rho : DensityOperator (Fin D))
    (u : EuclideanSpace ℂ (Fin D)) (hu : ‖u‖ = 1)
    (epsilon : ℝ) (hone : 1 + epsilon ≤ 160746 / 100000)
    (hrelative : RelativeCPApproximation
      (A := CStarMatrix (TripleIndex (Fin D))
        (TripleIndex (Fin D)) ℂ)
      epsilon
      (finiteUnitaryThirdTwirlLinearMap U)
      (unitaryHaarThirdTwirlLinearMap D)) :
    finiteUnitaryProjectiveWeightedOverlapSquare U rho u ≤
      (241119 / 25000 : ℝ) /
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
    _ ≤ (160746 / 100000 : ℝ) *
        cpTracePairingOn (computationalDiagonalTensorCube D)
          (unitaryHaarThirdTwirlLinearMap D)
          (densityDirectionTensor rho u) :=
      mul_le_mul_of_nonneg_right hone hhaar_nonnegative
    _ ≤ (160746 / 100000 : ℝ) *
        (6 / (((D : ℝ) + 1) * ((D : ℝ) + 2))) :=
      mul_le_mul_of_nonneg_left hhaar_le (by norm_num)
    _ = (241119 / 25000 : ℝ) /
        (((D : ℝ) + 1) * ((D : ℝ) + 2)) := by ring

/-- Near-exact weighted-overlap bound for the literal periodic circuit. -/
theorem ChoKimBlockCondition.periodicWeightedOverlapSquare_le_241119_div_25000
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    finiteUnitaryProjectiveWeightedOverlapSquare
        (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u ≤
      (241119 / 25000 : ℝ) /
        ((((2 ^ n) + 1 : ℕ) : ℝ) *
          (((2 ^ n) + 2 : ℕ) : ℝ)) := by
  simpa [Nat.cast_add, Nat.cast_one] using
    finiteUnitaryProjectiveWeightedOverlapSquare_le_241119_div_25000_of_relativeCP_cstarMatrix
      (by positivity : 0 < 2 ^ n)
      (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)
      rho u hu
      (choKimPeriodicThirdDesignError n K)
      (h.choKimPeriodicThirdDesignError_add_one_le_160746_div_100000 hn)
      (h.relativeCPApproximation_periodicThirdDesign hn)

/-- Near-exact one-copy variance bound for the literal periodic score. -/
theorem ChoKimBlockCondition.variance_periodicFiniteUnitaryProjectiveScore_le_241119_div_25000
    {n K : ℕ} (h : ChoKimBlockCondition n K) (hn : 0 < n)
    (rho : DensityOperator (Fin (2 ^ n)))
    (u : EuclideanSpace ℂ (Fin (2 ^ n))) (hu : ‖u‖ = 1) :
    variance (finiteUnitaryProjectiveScore u)
        ((finiteUnitaryProjectivePOVM (2 ^ n) (by positivity)
          (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd)).bornMeasure
            rho) ≤ 241119 / 25000 := by
  apply variance_finiteUnitaryProjectiveScore_le_kappa_of_weightedOverlapSquare
    (kappa := 241119 / 25000) (by positivity : 0 < 2 ^ n)
    (choKimPeriodicTwoLayerCliffordUnitaryFin h.block_dvd) rho u
    (by norm_num)
  exact h.periodicWeightedOverlapSquare_le_241119_div_25000 hn rho u hu

end

end TomographyOracleCore
