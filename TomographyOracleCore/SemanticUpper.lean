import TomographyOracleCore.MatrixReduction
import TomographyOracleCore.ExpectedOracle

namespace TomographyOracleCore
open MeasureTheory MatrixReduction

/-! Deterministic forward-error oracle and compact-space coverings. -/

/-- Matrix cone/curvature/duality plus a forward-error bound imply the full
simultaneous oracle.  This assembles the typed matrix reduction, quadratic
absorption, and the exact `64 / a` noise constant. -/
theorem densityOracle_of_matrix_bounds_and_forward_error
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (sigma rho : DensityOperator ι)
    (D : ℕ) (a eta h energy : ℝ) (tail : ℕ → ℝ)
    (ha : 0 < a) (hh : 0 ≤ h)
    (hforward : h ≤ 4 * eta)
    (hcone : ∀ s, 1 ≤ s → s ≤ D →
      traceNorm (sigma.matrix - rho.matrix) ≤
        2 * tail s + 4 * Real.sqrt s *
          frobeniusNorm (sigma.matrix - rho.matrix))
    (hlower :
      a * frobeniusNorm (sigma.matrix - rho.matrix) ^ 2 ≤ energy)
    (hupper :
      energy ≤ traceNorm (sigma.matrix - rho.matrix) * h) :
    OracleBound (traceNorm (sigma.matrix - rho.matrix)) tail
      (64 * eta / a) D := by
  intro s hs1 hsD
  have hred := density_trace_reduction_of_matrix_bounds sigma rho s a
    (tail s) h energy ha hh (hcone s hs1 hsD) hlower hupper
  have hz : 0 ≤ (s : ℝ) * h / a :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg s) hh) ha.le
  have habsorb :
      traceNorm (sigma.matrix - rho.matrix) ≤
        4 * tail s + 16 * ((s : ℝ) * h / a) :=
    scalar_quadratic_absorption
      (traceNorm (sigma.matrix - rho.matrix)) (tail s)
      ((s : ℝ) * h / a) (traceNorm_nonneg _) hz hred
  have hnoise := noise_control_of_forward_bound a h eta ha hforward s
  linarith
section FiniteProxyGrid

/-- Every compact state class admits a finite metric proxy grid.  This is the
state-independent discretization needed by the finite minimax estimator: the
grid depends only on the class and the requested resolution, not on the
unknown truth. -/
theorem exists_finite_metric_proxy_grid
    {State : Type*} [PseudoMetricSpace State]
    (states : Set State) (hcompact : IsCompact states)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ candidates : Finset State,
      (∀ proxy ∈ candidates, proxy ∈ states) ∧
      ∀ truth ∈ states, ∃ proxy ∈ candidates,
        dist truth proxy < epsilon := by
  classical
  obtain ⟨grid, hgrid_subset, hgrid_finite, hcover⟩ :=
    hcompact.finite_cover_balls hepsilon
  refine ⟨hgrid_finite.toFinset, ?_, ?_⟩
  · intro proxy hproxy
    exact hgrid_subset (hgrid_finite.mem_toFinset.mp hproxy)
  · intro truth htruth
    have hmem : truth ∈ ⋃ proxy ∈ grid, Metric.ball proxy epsilon :=
      hcover htruth
    rw [Set.mem_iUnion₂] at hmem
    rcases hmem with ⟨proxy, hproxy, hball⟩
    exact ⟨proxy, hgrid_finite.mem_toFinset.mpr hproxy,
      Metric.mem_ball.mp hball⟩

/-- A Lipschitz prediction map turns the compact metric grid into a finite
prediction proxy grid with explicit bias `L * epsilon`. -/
theorem exists_finite_prediction_proxy_grid
    {State Direction : Type*} [PseudoMetricSpace State]
    (states : Set State) (hcompact : IsCompact states)
    (prediction : State → Direction → ℝ)
    (L epsilon : ℝ) (hL : 0 ≤ L) (hepsilon : 0 < epsilon)
    (hlipschitz : ∀ left ∈ states, ∀ right ∈ states, ∀ u,
      |prediction left u - prediction right u| ≤ L * dist left right) :
    ∃ candidates : Finset State,
      (∀ proxy ∈ candidates, proxy ∈ states) ∧
      ∀ truth ∈ states, ∃ proxy ∈ candidates,
        ∀ u, |prediction proxy u - prediction truth u| ≤ L * epsilon := by
  obtain ⟨candidates, hcandidates, hproxy⟩ :=
    exists_finite_metric_proxy_grid states hcompact epsilon hepsilon
  refine ⟨candidates, hcandidates, ?_⟩
  intro truth htruth
  obtain ⟨proxy, hproxy_mem, hdist⟩ := hproxy truth htruth
  refine ⟨proxy, hproxy_mem, ?_⟩
  intro u
  exact (hlipschitz proxy (hcandidates proxy hproxy_mem) truth htruth u).trans
    (mul_le_mul_of_nonneg_left (by simpa [dist_comm] using hdist.le) hL)

/-- Reindex a compact finite proxy grid by `Fin N`.  The estimator can thus
use the canonical linear order on `Fin N`; no arbitrary order on the
continuous state space is needed. -/
theorem exists_fin_metric_proxy_grid
    {State : Type*} [PseudoMetricSpace State]
    (states : Set State) (hcompact : IsCompact states)
    (hstates : states.Nonempty)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ stateOf : Fin N → State,
      0 < N ∧
      (∀ i, stateOf i ∈ states) ∧
      ∀ truth ∈ states, ∃ proxy : Fin N,
        dist truth (stateOf proxy) < epsilon := by
  classical
  obtain ⟨grid, hgrid, hcover⟩ :=
    exists_finite_metric_proxy_grid states hcompact epsilon hepsilon
  obtain ⟨truth₀, htruth₀⟩ := hstates
  obtain ⟨proxy₀, hproxy₀, _⟩ := hcover truth₀ htruth₀
  have hgrid_nonempty : grid.Nonempty := ⟨proxy₀, hproxy₀⟩
  let e : grid ≃ Fin grid.card := grid.equivFin
  let stateOf : Fin grid.card → State := fun i => (e.symm i).1
  refine ⟨grid.card, stateOf, Finset.card_pos.mpr hgrid_nonempty, ?_, ?_⟩
  · intro i
    exact hgrid (e.symm i).1 (e.symm i).2
  · intro truth htruth
    obtain ⟨proxy, hproxy, hdist⟩ := hcover truth htruth
    let proxyIndex : Fin grid.card := e ⟨proxy, hproxy⟩
    refine ⟨proxyIndex, ?_⟩
    simpa [stateOf, proxyIndex, e] using hdist

/-- Lipschitz prediction version of the `Fin N` proxy grid. -/
theorem exists_fin_prediction_proxy_grid
    {State Direction : Type*} [PseudoMetricSpace State]
    (states : Set State) (hcompact : IsCompact states)
    (hstates : states.Nonempty)
    (prediction : State → Direction → ℝ)
    (L epsilon : ℝ) (hL : 0 ≤ L) (hepsilon : 0 < epsilon)
    (hlipschitz : ∀ left ∈ states, ∀ right ∈ states, ∀ u,
      |prediction left u - prediction right u| ≤ L * dist left right) :
    ∃ N : ℕ, ∃ stateOf : Fin N → State,
      0 < N ∧
      (∀ i, stateOf i ∈ states) ∧
      ∀ truth ∈ states, ∃ proxy : Fin N,
        ∀ u, |prediction (stateOf proxy) u - prediction truth u| ≤
          L * epsilon := by
  obtain ⟨N, stateOf, hN, hstateOf, hcover⟩ :=
    exists_fin_metric_proxy_grid states hcompact hstates epsilon hepsilon
  refine ⟨N, stateOf, hN, hstateOf, ?_⟩
  intro truth htruth
  obtain ⟨proxy, hdist⟩ := hcover truth htruth
  refine ⟨proxy, ?_⟩
  intro u
  exact (hlipschitz (stateOf proxy) (hstateOf proxy) truth htruth u).trans
    (mul_le_mul_of_nonneg_left (by simpa [dist_comm] using hdist.le) hL)

end FiniteProxyGrid

end TomographyOracleCore
