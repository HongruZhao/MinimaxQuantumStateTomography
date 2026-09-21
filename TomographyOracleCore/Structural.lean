import TomographyOracleCore.MathlibImports
import TomographyOracleCore.Assumptions

namespace TomographyOracleCore

/-!
Structural lemmas that remove two pieces of misleading bookkeeping from the
scientific trust boundary.

The first theorem proves the scalar curvature-to-reduction step once the
matrix block/cone inequality and the energy inequality have been established.
The second group defines unrestricted and fixed-design risks as genuine
infima and proves their ordering.  Thus experiment inclusion is not a
scientific hypothesis.
-/

/-- If a nonnegative scaled Frobenius error satisfies the cone inequality and
its square is controlled by `z * err`, then the square-root reduction used by
the oracle theorem follows.  In the tomography proof one takes
`scaledF = sqrt s * ‖Δ‖_F` and `z = s * h / a`. -/
theorem reduction_of_cone_and_energy
    (err tail scaledF z : ℝ)
    (herr : 0 ≤ err) (hz : 0 ≤ z)
    (hcone : err ≤ 2 * tail + 4 * scaledF)
    (henergy : scaledF ^ 2 ≤ z * err) :
    err ≤ 2 * tail + 4 * Real.sqrt z * Real.sqrt err := by
  have hprod : 0 ≤ z * err := mul_nonneg hz herr
  have hsqrt_sq : (Real.sqrt (z * err)) ^ 2 = z * err :=
    Real.sq_sqrt hprod
  have hscaledF_le : scaledF ≤ Real.sqrt (z * err) := by
    have hsqrt_nonnegative : 0 ≤ Real.sqrt (z * err) := Real.sqrt_nonneg _
    nlinarith
  have hsqrt_mul : Real.sqrt (z * err) = Real.sqrt z * Real.sqrt err := by
    rw [Real.sqrt_mul hz]
  rw [hsqrt_mul] at hscaledF_le
  linarith

/-- Once the forward operator error obeys `h ≤ 4 * eta`, the scalar
`noise_control` inequality is automatic for the tomography choices
`z s = s * h / a` and `noise = 64 * eta / a`.  Thus the remaining content
of the noise input is the probabilistic forward-error bound, not this
constant calculation. -/
theorem noise_control_of_forward_bound
    (a h eta : ℝ) (ha : 0 < a) (hh : h ≤ 4 * eta) (s : ℕ) :
    16 * ((s : ℝ) * h / a) ≤ (64 * eta / a) * (s : ℝ) := by
  have hs : 0 ≤ (s : ℝ) := Nat.cast_nonneg s
  have hscaled : (s : ℝ) * h ≤ (s : ℝ) * (4 * eta) :=
    mul_le_mul_of_nonneg_left hh hs
  have hnum : 16 * (s : ℝ) * h ≤ 64 * eta * (s : ℝ) := by
    nlinarith
  calc
    16 * ((s : ℝ) * h / a) = (16 * (s : ℝ) * h) / a := by ring
    _ ≤ (64 * eta * (s : ℝ)) / a :=
      (div_le_div_iff_of_pos_right ha).2 hnum
    _ = (64 * eta / a) * (s : ℝ) := by ring

/-- Minimax risk when both the nonadaptive design and estimator may vary. -/
noncomputable def unrestrictedRisk
    {Design Estimator : Type*} (risk : Design → Estimator → ℝ) : ℝ :=
  sInf (Set.range fun p : Design × Estimator => risk p.1 p.2)

/-- Minimax risk when the measurement design is fixed and only the estimator
may vary. -/
noncomputable def fixedDesignRisk
    {Design Estimator : Type*} (risk : Design → Estimator → ℝ)
    (design : Design) : ℝ :=
  sInf (Set.range fun estimator : Estimator => risk design estimator)

/-- Optimizing over all designs cannot have larger risk than restricting to
one fixed design.  This is the semantic proof of experiment inclusion. -/
theorem unrestrictedRisk_le_fixedDesignRisk
    {Design Estimator : Type*} [Nonempty Estimator]
    (risk : Design → Estimator → ℝ)
    (hrisk : ∀ design estimator, 0 ≤ risk design estimator)
    (design : Design) :
    unrestrictedRisk risk ≤ fixedDesignRisk risk design := by
  unfold unrestrictedRisk fixedDesignRisk
  apply csInf_le_csInf
  · refine ⟨0, ?_⟩
    rintro _ ⟨p, rfl⟩
    exact hrisk p.1 p.2
  · exact Set.range_nonempty _
  · rintro _ ⟨estimator, rfl⟩
    exact ⟨(design, estimator), rfl⟩

/-- The former proposition-valued placeholder `DesignRiskInclusion` is
automatically inhabited for risks defined by the two infima above. -/
theorem designRiskInclusion_of_infima
    {Design Estimator : Type*} [Nonempty Estimator]
    (risk : Design → Estimator → ℝ)
    (hrisk : ∀ design estimator, 0 ≤ risk design estimator)
    (design : Design) :
    DesignRiskInclusion (unrestrictedRisk risk)
      (fixedDesignRisk risk design) := by
  exact unrestrictedRisk_le_fixedDesignRisk risk hrisk design

/-- Minimax sandwich with experiment inclusion discharged from the actual
infimum definitions rather than supplied as a theorem hypothesis. -/
theorem two_experiment_minimax_of_infima
    {Design Estimator : Type*} [Nonempty Estimator]
    (risk : Design → Estimator → ℝ)
    (hrisk : ∀ design estimator, 0 ≤ risk design estimator)
    (design : Design) (rate lowerConstant upperConstant : ℝ)
    (hlower : lowerConstant * rate ≤ unrestrictedRisk risk)
    (hupper : fixedDesignRisk risk design ≤ upperConstant * rate) :
    (lowerConstant * rate ≤ unrestrictedRisk risk ∧
      unrestrictedRisk risk ≤ upperConstant * rate) ∧
    (lowerConstant * rate ≤ fixedDesignRisk risk design ∧
      fixedDesignRisk risk design ≤ upperConstant * rate) := by
  exact two_experiment_minimax_sandwich hlower
    (unrestrictedRisk_le_fixedDesignRisk risk hrisk design) hupper

end TomographyOracleCore
