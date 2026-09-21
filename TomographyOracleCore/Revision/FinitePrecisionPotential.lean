import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Stability of projected subgradient iteration under finite precision

The results in this file prove error accumulation from local, checkable
approximation certificates. They do not postulate an eigensolver or a
projection algorithm. The same results apply to the real Hilbert space of
complex matrices equipped with the Frobenius norm.
-/

namespace TomographyOracleCore.Revision.FinitePrecision

open scoped BigOperators InnerProductSpace

section Perturbation

variable {E : Type*} [NormedAddCommGroup E]

/-- A nearby feasible projection changes the potential by at most the
displayed linear-plus-quadratic error. In the density-matrix application
`R = sqrt 2`, the diameter of the feasible set. -/
theorem nearby_projection_potential
    (p q z : E) {R epsilon : ℝ}
    (hR : 0 ≤ R) (hepsilon : 0 ≤ epsilon)
    (hdiam : ‖p - z‖ ≤ R) (happrox : ‖q - p‖ ≤ epsilon) :
    ‖q - z‖ ^ 2 ≤ ‖p - z‖ ^ 2 + 2 * R * epsilon + epsilon ^ 2 := by
  have htriangle : ‖q - z‖ ≤ epsilon + ‖p - z‖ := by
    calc
      ‖q - z‖ = ‖(q - p) + (p - z)‖ := by congr 1; abel
      _ ≤ ‖q - p‖ + ‖p - z‖ := norm_add_le _ _
      _ ≤ epsilon + ‖p - z‖ := by linarith
  have hsq := pow_le_pow_left₀ (norm_nonneg (q - z)) htriangle 2
  have hcross := mul_le_mul_of_nonneg_right hdiam hepsilon
  nlinarith

end Perturbation

section Subgradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A local epsilon-subgradient inequality, exact projection comparison,
and a feasible approximation to that projection imply the perturbed
potential recurrence used in the paper. -/
theorem inexact_projected_step
    (f : E → ℝ) (x z g p q : E) {h G epsilonS epsilonP R : ℝ}
    (hh : 0 ≤ h) (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hepsilonP : 0 ≤ epsilonP)
    (hsubgradient : f x - f z ≤ ⟪g, x - z⟫_ℝ + epsilonS)
    (hgradient : ‖g‖ ≤ G)
    (hprojection : ‖p - z‖ ≤ ‖x - h • g - z‖)
    (hdiameter : ‖p - z‖ ≤ R)
    (hrounding : ‖q - p‖ ≤ epsilonP) :
    ‖q - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 - 2 * h * (f x - f z) +
      h ^ 2 * G ^ 2 + 2 * h * epsilonS +
      2 * R * epsilonP + epsilonP ^ 2 := by
  have hperturb := nearby_projection_potential p q z hR hepsilonP
    hdiameter hrounding
  have hprojSq := pow_le_pow_left₀ (norm_nonneg (p - z)) hprojection 2
  have hstepIdentity :
      ‖x - h • g - z‖ ^ 2 = ‖x - z‖ ^ 2 -
        2 * h * ⟪g, x - z⟫_ℝ + h ^ 2 * ‖g‖ ^ 2 := by
    have hrewrite : x - h • g - z = (x - z) - h • g := by abel
    rw [hrewrite, norm_sub_sq_real, real_inner_smul_right,
      real_inner_comm (x - z) g, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hh]
    ring
  have hgSq := pow_le_pow_left₀ (norm_nonneg g) hgradient 2
  have hscaledGrad := mul_le_mul_of_nonneg_left hgSq (sq_nonneg h)
  have hscaledSub := mul_le_mul_of_nonneg_left hsubgradient hh
  nlinarith

end Subgradient

/-- Telescope the perturbed recurrence without hiding the perturbation in
a shifted objective or an assumed global convergence theorem. -/
theorem inexact_solver_telescope
    (potential gap : ℕ → ℝ) (h G epsilonS epsilonP R : ℝ) (J : ℕ)
    (hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        2 * R * epsilonP + epsilonP ^ 2) :
    2 * h * (∑ j ∈ Finset.range J, gap j) ≤
      potential 0 - potential J + (J : ℝ) *
        (h ^ 2 * G ^ 2 + 2 * h * epsilonS +
          2 * R * epsilonP + epsilonP ^ 2) := by
  induction J with
  | zero => simp
  | succ J ih =>
      have hprior := ih (fun j hj => hstep j (Nat.lt_trans hj (Nat.lt_succ_self J)))
      have hlast := hstep J (Nat.lt_succ_self J)
      rw [Finset.sum_range_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith

/-- Exact final error formula, including both sources of finite-precision
loss. The initial squared distance is at most two for density matrices. -/
theorem inexact_solver_average_bound
    (potential gap : ℕ → ℝ) (h G epsilonS epsilonP R : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 0 < J)
    (hzero : potential 0 ≤ 2) (hend : 0 ≤ potential J)
    (hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        2 * R * epsilonP + epsilonP ^ 2) :
    (∑ j ∈ Finset.range J, gap j) / (J : ℝ) ≤
      1 / (h * (J : ℝ)) + h * G ^ 2 / 2 + epsilonS +
        (2 * R * epsilonP + epsilonP ^ 2) / (2 * h) := by
  have htel := inexact_solver_telescope potential gap h G epsilonS epsilonP R J hstep
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  apply (div_le_iff₀ hJreal).2
  have hid :
      2 * h * ((1 / (h * (J : ℝ)) + h * G ^ 2 / 2 + epsilonS +
        (2 * R * epsilonP + epsilonP ^ 2) / (2 * h)) * (J : ℝ)) =
      2 + (J : ℝ) * (h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        2 * R * epsilonP + epsilonP ^ 2) := by
    field_simp [hh.ne', hJreal.ne']
    <;> ring
  have hscaled :
      2 * h * (∑ j ∈ Finset.range J, gap j) ≤
      2 * h * ((1 / (h * (J : ℝ)) + h * G ^ 2 / 2 + epsilonS +
        (2 * R * epsilonP + epsilonP ^ 2) / (2 * h)) * (J : ℝ)) := by
    rw [hid]
    linarith
  exact le_of_mul_le_mul_left hscaled (show 0 < 2 * h by positivity)

/-- A concrete allocation of the optimization tolerance among iteration,
subgradient, and feasible-projection errors. The coarse density diameter
bound `R = 2` avoids irrational arithmetic in the precision schedule. -/
theorem inexact_solver_gamma_budget
    (potential gap : ℕ → ℝ) (h G gamma epsilonS epsilonP : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 0 < J)
    (hzero : potential 0 ≤ 2) (hend : 0 ≤ potential J)
    (hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        4 * epsilonP + epsilonP ^ 2)
    (hiterations : 4 ≤ h * (J : ℝ) * gamma)
    (hvariance : h * G ^ 2 ≤ gamma / 2)
    (hspectral : epsilonS ≤ gamma / 4)
    (hprojection : epsilonP ≤ h * gamma / 10)
    (hepsilonP : 0 ≤ epsilonP) (hepsilonP_le : epsilonP ≤ 1) :
    (∑ j ∈ Finset.range J, gap j) / (J : ℝ) ≤ gamma := by
  have hformula := inexact_solver_average_bound potential gap h G epsilonS epsilonP 2 J
    hh hJ hzero hend (by convert hstep using 1 <;> norm_num)
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hbase : 1 / (h * (J : ℝ)) ≤ gamma / 4 := by
    apply (div_le_iff₀ (mul_pos hh hJreal)).2
    nlinarith
  have hsquare : epsilonP ^ 2 ≤ epsilonP := by
    nlinarith
  have hproj : (2 * 2 * epsilonP + epsilonP ^ 2) / (2 * h) ≤ gamma / 4 := by
    apply (div_le_iff₀ (show 0 < 2 * h by positivity)).2
    nlinarith
  linarith

/-- The stated rational precision choices satisfy the budget above:
`h = gamma/(2 G²)`, spectral error `gamma/4`, projection error
`h*gamma/10`, and at most a constant-factor enlargement of the exact
iteration count. -/
theorem explicit_precision_schedule
    {G gamma : ℝ} (hG : 1 ≤ G) (hgamma : 0 < gamma) (hgamma_le : gamma ≤ 1)
    (J : ℕ) (hiterations : 8 * G ^ 2 ≤ (J : ℝ) * gamma ^ 2) :
    let h := gamma / (2 * G ^ 2)
    0 < h ∧ h * G ^ 2 ≤ gamma / 2 ∧
      0 ≤ h * gamma / 10 ∧ h * gamma / 10 ≤ 1 ∧
      4 ≤ h * (J : ℝ) * gamma := by
  dsimp only
  let h := gamma / (2 * G ^ 2)
  have hGpos : 0 < G := by linarith
  have hGsq : 1 ≤ G ^ 2 := by nlinarith
  have hh : 0 < h := by dsimp [h]; positivity
  have hidentity : h * G ^ 2 = gamma / 2 := by
    dsimp [h]
    field_simp
  have hsmall : h ≤ 1 / 2 := by
    have h := mul_nonneg hh.le (sub_nonneg.mpr hGsq)
    nlinarith
  have hproduct : h * gamma ≤ 1 / 2 := by
    have h := mul_le_mul_of_nonneg_left hgamma_le hh.le
    nlinarith
  refine ⟨hh, hidentity.le, by positivity, by nlinarith, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hiterations hh.le
  have hJnonneg : 0 ≤ (J : ℝ) := by positivity
  have hcalc : h * ((J : ℝ) * gamma ^ 2) =
      (h * (J : ℝ) * gamma) * gamma := by ring
  rw [hcalc] at hmul
  have hleft : h * (8 * G ^ 2) = 4 * gamma := by nlinarith [hidentity]
  rw [hleft] at hmul
  exact le_of_mul_le_mul_right hmul hgamma

end TomographyOracleCore.Revision.FinitePrecision
