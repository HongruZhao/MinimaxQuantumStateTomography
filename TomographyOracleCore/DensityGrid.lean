import TomographyOracleCore.DensityCompact
import TomographyOracleCore.SemanticUpper

namespace TomographyOracleCore

open MatrixReduction
open DensityCompact
open scoped ComplexOrder Matrix.Norms.L2Operator InnerProductSpace

namespace DensityGrid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A computational-basis pure state, used only to witness that the density
state space is nonempty when the Hilbert-space index is nonempty. -/
noncomputable def basisDensityOperator (i₀ : ι) : DensityOperator ι where
  matrix := Matrix.diagonal (Pi.single i₀ 1)
  posSemidef := Matrix.PosSemidef.diagonal (by
    intro i
    by_cases h : i = i₀
    · subst i
      simp
    · simp [Pi.single_apply, h])
  trace_eq_one := by
    simp [Matrix.trace_diagonal]

theorem densityOperator_nonempty [Nonempty ι] :
    Nonempty (DensityOperator ι) := by
  exact ⟨basisDensityOperator (Classical.choice (inferInstance : Nonempty ι))⟩

/-- The compact density-state cover, reindexed by `Fin N`.  Hence the finite
minimum-distance estimator can use the canonical order on `Fin N`, with no
order imposed on density operators. -/
theorem exists_fin_density_operator_grid
    [Nonempty ι] (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ stateOf : Fin N → DensityOperator ι,
      0 < N ∧
      ∀ truth : DensityOperator ι, ∃ proxy : Fin N,
        dist truth (stateOf proxy) < epsilon := by
  letI : Nonempty (DensityOperator ι) := densityOperator_nonempty
  obtain ⟨N, stateOf, hN, _hstateOf, hcover⟩ :=
    exists_fin_metric_proxy_grid
      (Set.univ : Set (DensityOperator ι))
      isCompact_univ_densityOperator Set.univ_nonempty epsilon hepsilon
  exact ⟨N, stateOf, hN, fun truth => hcover truth (Set.mem_univ truth)⟩

/-- Linear forward prediction in the pure direction `u`. -/
noncomputable def quadraticPrediction
    (rho : DensityOperator ι) (u : EuclideanSpace ℂ ι) : ℝ :=
  (⟪u, rho.matrix.toEuclideanLin u⟫_ℂ).re

theorem dist_densityOperator_eq_operatorNorm
    (rho sigma : DensityOperator ι) :
    dist rho sigma = ‖rho.matrix - sigma.matrix‖ := by
  change dist rho.matrix sigma.matrix = ‖rho.matrix - sigma.matrix‖
  exact dist_eq_norm _ _

/-- Operator-norm Lipschitz control of a quadratic-form prediction. -/
theorem quadraticPrediction_sub_le
    (rho sigma : DensityOperator ι) (u : EuclideanSpace ℂ ι) :
    |quadraticPrediction rho u - quadraticPrediction sigma u| ≤
      ‖u‖ ^ 2 * dist rho sigma := by
  have hrewrite :
      quadraticPrediction rho u - quadraticPrediction sigma u =
        (⟪u, (rho.matrix - sigma.matrix).toEuclideanLin u⟫_ℂ).re := by
    simp [quadraticPrediction, sub_eq_add_neg, inner_add_right]
  rw [hrewrite]
  calc
    |(⟪u, (rho.matrix - sigma.matrix).toEuclideanLin u⟫_ℂ).re|
        ≤ ‖⟪u, (rho.matrix - sigma.matrix).toEuclideanLin u⟫_ℂ‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖u‖ * ‖(rho.matrix - sigma.matrix).toEuclideanLin u‖ :=
      norm_inner_le_norm _ _
    _ ≤ ‖u‖ * (‖rho.matrix - sigma.matrix‖ * ‖u‖) := by
      gcongr
      simpa [Matrix.l2_opNorm_def] using
        (rho.matrix - sigma.matrix).toEuclideanLin.toContinuousLinearMap.le_opNorm u
    _ = ‖u‖ ^ 2 * dist rho sigma := by
      rw [dist_densityOperator_eq_operatorNorm]
      ring

/-- Unit-vector quadratic predictions are one-Lipschitz in the chosen
operator-norm metric. -/
theorem quadraticPrediction_lipschitz_of_norm_le_one
    (rho sigma : DensityOperator ι) (u : EuclideanSpace ℂ ι)
    (hu : ‖u‖ ≤ 1) :
    |quadraticPrediction rho u - quadraticPrediction sigma u| ≤
      dist rho sigma := by
  have hu₀ : 0 ≤ ‖u‖ := norm_nonneg _
  have husq : ‖u‖ ^ 2 ≤ 1 := by nlinarith
  calc
    |quadraticPrediction rho u - quadraticPrediction sigma u|
        ≤ ‖u‖ ^ 2 * dist rho sigma :=
      quadraticPrediction_sub_le rho sigma u
    _ ≤ 1 * dist rho sigma :=
      mul_le_mul_of_nonneg_right husq (dist_nonneg)
    _ = dist rho sigma := one_mul _

/-- A concrete `Fin N` density grid whose predictions approximate all
unit-vector quadratic forms uniformly to the metric resolution. -/
theorem exists_fin_density_quadratic_prediction_grid
    [Nonempty ι] (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ stateOf : Fin N → DensityOperator ι,
      0 < N ∧
      ∀ truth : DensityOperator ι, ∃ proxy : Fin N,
        ∀ u : EuclideanSpace ℂ ι, ‖u‖ ≤ 1 →
          |quadraticPrediction (stateOf proxy) u -
            quadraticPrediction truth u| ≤ epsilon := by
  obtain ⟨N, stateOf, hN, hcover⟩ :=
    exists_fin_density_operator_grid (ι := ι) epsilon hepsilon
  refine ⟨N, stateOf, hN, ?_⟩
  intro truth
  obtain ⟨proxy, hdist⟩ := hcover truth
  refine ⟨proxy, ?_⟩
  intro u hu
  exact (quadraticPrediction_lipschitz_of_norm_le_one
    (stateOf proxy) truth u hu).trans (by simpa [dist_comm] using hdist.le)

end DensityGrid

end TomographyOracleCore
