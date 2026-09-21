import TomographyOracleCore.PaperMatch.PureRandomizedTesting
import TomographyOracleCore.PhysicalNearestDecoder
import TomographyOracleCore.PaperMatch.SmallRankReduction

namespace TomographyOracleCore.PaperMatch.RankMinimax
open MeasureTheory ProbabilityTheory MatrixReduction PhysicalRisk
open scoped BigOperators ENNReal ComplexOrder InnerProductSpace
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {m T : ℕ}

theorem cubeBitError_bounds (θ : SignCube m) (σ : DensityOperator (Fin (m + 1))) (j : Fin m) :
    0 ≤ cubeBitError θ σ j ∧ cubeBitError θ σ j ≤ 1 := by
  unfold cubeBitError
  split <;> norm_num

theorem cubeBitError_measurable (θ : SignCube m) (j : Fin m) :
    Measurable (fun σ : DensityOperator (Fin (m + 1)) => cubeBitError θ σ j) := by
  unfold cubeBitError
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurable_decodedCubeSign j) (measurableSet_singleton (θ j))

theorem cubeBitError_flip_complement (θ : SignCube m)
    (σ : DensityOperator (Fin (m + 1))) (j : Fin m) :
    cubeBitError θ σ j + cubeBitError (cubeFlip j θ) σ j = 1 := by
  unfold cubeBitError
  rw [cubeFlip_self]
  cases θ j <;> cases decodedCubeSign σ j <;> norm_num

def cubeExpectedBitError (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T)
    (θ : SignCube m) (j : Fin m) : ℝ :=
  ∫ σ, cubeBitError θ σ j ∂estimateKernel design estimator (cubeState a ha θ)

theorem cubeExpectedBitError_pair (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T)
    (θ : SignCube m) (j : Fin m) :
    1 / 2 ≤ cubeExpectedBitError a ha design estimator θ j +
      cubeExpectedBitError a ha design estimator (cubeFlip j θ) j := by
  have hi (θ η : SignCube m) : Integrable (fun σ => cubeBitError θ σ j)
      (estimateKernel design estimator (cubeState a ha η)) :=
    integrable_unitTest _ _ (cubeBitError_measurable θ j)
      (fun σ => (cubeBitError_bounds θ σ j).1) (fun σ => (cubeBitError_bounds θ σ j).2)
  have hgap := cube_estimate_test_gap a ha ha1 hTa design estimator
    (fun σ => cubeBitError θ σ j) (cubeBitError_measurable θ j)
    (fun σ => (cubeBitError_bounds θ σ j).1) (fun σ => (cubeBitError_bounds θ σ j).2) θ j
  have hsum :
      (∫ σ, cubeBitError θ σ j ∂estimateKernel design estimator (cubeState a ha (cubeFlip j θ))) +
      cubeExpectedBitError a ha design estimator (cubeFlip j θ) j = 1 := by
    rw [cubeExpectedBitError, ← integral_add (hi θ _) (hi (cubeFlip j θ) _)]
    simp [cubeBitError_flip_complement]
  have h := (abs_le.mp hgap).1
  dsimp [cubeExpectedBitError] at *
  linarith

/-- Finite bit-flip pairing; the same hypercube is used for all seeds. -/
theorem cubeExpectedBitError_sum (a : ℝ)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T) (j : Fin m) :
    (Fintype.card (SignCube m) : ℝ) / 4 ≤ ∑ θ, cubeExpectedBitError a ha design estimator θ j := by
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (SignCube m)))
    (fun θ _ => cubeExpectedBitError_pair a ha ha1 hTa design estimator θ j)
  have hp : (∑ θ : SignCube m, cubeExpectedBitError a ha design estimator (cubeFlip j θ) j) =
      ∑ θ : SignCube m, cubeExpectedBitError a ha design estimator θ j :=
    (cubeFlipEquiv j).sum_comp (fun θ => cubeExpectedBitError a ha design estimator θ j)
  rw [Finset.sum_add_distrib, hp] at hs
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  linarith

/-- Integrability of the actual full trace loss under any probability law. -/
theorem integrable_realTraceLoss {D : ℕ} (ρ : DensityOperator (Fin D))
    (μ : Measure (DensityOperator (Fin D))) [IsProbabilityMeasure μ] :
    Integrable (realHermitianTraceLoss ρ) μ :=
  Integrable.of_bound (realHermitianTraceLoss_measurable ρ).aestronglyMeasurable 2
    (ae_of_all _ fun σ => by
      rw [Real.norm_eq_abs, realHermitianTraceLoss, abs_of_nonneg (hermitianTraceNorm_nonneg _ _)]
      exact density_hermitianTraceNorm_sub_le_two σ ρ)

def cubeExpectedLoss (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T)
    (θ : SignCube m) : ℝ :=
  ∫ σ, realHermitianTraceLoss (cubeState a ha θ) σ
    ∂estimateKernel design estimator (cubeState a ha θ)

theorem cubeExpectedLoss_hamming (a : ℝ) (ha0 : 0 ≤ a)
    (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T) (θ : SignCube m) :
    Real.sqrt (1 - (m : ℝ) * a ^ 2) * a *
      (∑ j, cubeExpectedBitError a ha design estimator θ j) ≤
      Real.sqrt m * cubeExpectedLoss a ha design estimator θ := by
  have hi (j : Fin m) : Integrable (fun σ => cubeBitError θ σ j)
      (estimateKernel design estimator (cubeState a ha θ)) :=
    integrable_unitTest _ _ (cubeBitError_measurable θ j)
      (fun σ => (cubeBitError_bounds θ σ j).1) (fun σ => (cubeBitError_bounds θ σ j).2)
  have hham := (integrable_finsetSum Finset.univ (fun j _ => hi j)).const_mul
    (Real.sqrt (1 - (m : ℝ) * a ^ 2) * a)
  have htrace := (integrable_realTraceLoss (cubeState a ha θ)
    (estimateKernel design estimator (cubeState a ha θ))).const_mul (Real.sqrt m)
  have h := integral_mono hham htrace (fun σ => cube_hamming_le_trace a ha0 ha θ σ)
  simpa only [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hi j),
    cubeExpectedBitError, cubeExpectedLoss] using h

/-- The finite average lower bound for actual expected full trace loss. -/
theorem cubeExpectedLoss_sum (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T) :
    (Fintype.card (SignCube m) : ℝ) *
      (Real.sqrt (1 - (m : ℝ) * a ^ 2) * a * Real.sqrt m / 4) ≤
      ∑ θ, cubeExpectedLoss a ha design estimator θ := by
  have hp : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (SignCube m)))
    (fun θ _ => cubeExpectedLoss_hamming a ha0 ha design estimator θ)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hs
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin m)))
    (fun j _ => cubeExpectedBitError_sum a ha ha1 hTa design estimator j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  have hcoef : 0 ≤ Real.sqrt (1 - (m : ℝ) * a ^ 2) * a := by positivity
  have h := (mul_le_mul_of_nonneg_left hb hcoef).trans hs
  apply (mul_le_mul_iff_right₀ hp).mp
  have hm_sq := Real.sq_sqrt (Nat.cast_nonneg m)
  calc
    _ = (Real.sqrt (1 - (m : ℝ) * a ^ 2) * a) *
        ((Real.sqrt (m : ℝ)) ^ 2 * ((Fintype.card (SignCube m) : ℝ) / 4)) := by ring
    _ = _ := by rw [hm_sq]
    _ ≤ _ := h

/-- At least one fixed pure state attains the finite-average lower bound. -/
theorem exists_cube_expected_loss_ge (hm : 1 ≤ m) (a : ℝ) (ha0 : 0 ≤ a)
    (ha : (m : ℝ) * a ^ 2 ≤ 1) (ha1 : a ^ 2 ≤ 1) (hTa : (T : ℝ) * a ^ 2 ≤ 1 / 64)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T) :
    ∃ θ : SignCube m, Real.sqrt (1 - (m : ℝ) * a ^ 2) * a * Real.sqrt m / 4 ≤
      cubeExpectedLoss a ha design estimator θ := by
  have hs := cubeExpectedLoss_sum hm a ha0 ha ha1 hTa design estimator
  by_contra h
  push_neg at h
  have hlt := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (SignCube m)))
    Finset.univ_nonempty (fun θ _ => h θ)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
  linarith

/-- Identification with the existing ENNReal physical risk, not a proxy loss. -/
theorem cubeExpectedLoss_ofReal (a : ℝ) (ha : (m : ℝ) * a ^ 2 ≤ 1)
    (design : Design (m + 1) T) (estimator : Estimator (m + 1) T) (θ : SignCube m) :
    ENNReal.ofReal (cubeExpectedLoss a ha design estimator θ) =
      statewiseExpectedTraceRisk design estimator (cubeState a ha θ) :=
  ofReal_integral_eq_lintegral_ofReal (integrable_realTraceLoss _ _)
    (ae_of_all _ fun σ => hermitianTraceNorm_nonneg _ _)

end
end TomographyOracleCore.PaperMatch.RankMinimax
