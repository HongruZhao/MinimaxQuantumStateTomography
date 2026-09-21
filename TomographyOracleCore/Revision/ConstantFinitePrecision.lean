import TomographyOracleCore.Revision.FinitePrecisionPotential
namespace TomographyOracleCore.Revision.FinitePrecision
open scoped BigOperators
theorem inexact_solver_average_bound_unit_radius
    (potential gap : ℕ → ℝ) (h G epsilonS epsilonP R : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 0 < J)
    (hzero : potential 0 ≤ 1) (hend : 0 ≤ potential J)
    (hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        2 * R * epsilonP + epsilonP ^ 2) :
    (∑ j ∈ Finset.range J, gap j) / (J : ℝ) ≤
      1 / (2 * h * (J : ℝ)) + h * G ^ 2 / 2 + epsilonS +
        (2 * R * epsilonP + epsilonP ^ 2) / (2 * h) := by
  have htel := inexact_solver_telescope potential gap h G epsilonS epsilonP R J hstep
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  apply (div_le_iff₀ hJreal).2
  have hid :
      2 * h * ((1 / (2 * h * (J : ℝ)) + h * G ^ 2 / 2 + epsilonS +
        (2 * R * epsilonP + epsilonP ^ 2) / (2 * h)) * (J : ℝ)) =
      1 + (J : ℝ) * (h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        2 * R * epsilonP + epsilonP ^ 2) := by
    field_simp [hh.ne', hJreal.ne']
    <;> ring
  have hscaled :
      2 * h * (∑ j ∈ Finset.range J, gap j) ≤
      2 * h * ((1 / (2 * h * (J : ℝ)) + h * G ^ 2 / 2 + epsilonS +
        (2 * R * epsilonP + epsilonP ^ 2) / (2 * h)) * (J : ℝ)) := by
    rw [hid]
    linarith
  exact le_of_mul_le_mul_left hscaled (show 0 < 2 * h by positivity)

/-- A concrete allocation of the optimization tolerance among iteration,
subgradient, and feasible-projection errors. The coarse density diameter
bound `R = 2` avoids irrational arithmetic in the precision schedule. -/
theorem inexact_solver_gamma_budget_unit_radius
    (potential gap : ℕ → ℝ) (h G gamma epsilonS epsilonP : ℝ) (J : ℕ)
    (hh : 0 < h) (hJ : 0 < J)
    (hzero : potential 0 ≤ 1) (hend : 0 ≤ potential J)
    (hstep : ∀ j < J,
      potential (j + 1) ≤ potential j - 2 * h * gap j +
        h ^ 2 * G ^ 2 + 2 * h * epsilonS +
        4 * epsilonP + epsilonP ^ 2)
    (hiterations : 2 ≤ h * (J : ℝ) * gamma)
    (hvariance : h * G ^ 2 ≤ gamma / 2)
    (hspectral : epsilonS ≤ gamma / 4)
    (hprojection : epsilonP ≤ h * gamma / 10)
    (hepsilonP : 0 ≤ epsilonP) (hepsilonP_le : epsilonP ≤ 1) :
    (∑ j ∈ Finset.range J, gap j) / (J : ℝ) ≤ gamma := by
  have hformula := inexact_solver_average_bound_unit_radius potential gap h G epsilonS epsilonP 2 J
    hh hJ hzero hend (by convert hstep using 1 <;> norm_num)
  have hJreal : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hbase : 1 / (2 * h * (J : ℝ)) ≤ gamma / 4 := by
    apply (div_le_iff₀ (show 0 < 2 * h * (J : ℝ) by positivity)).2
    nlinarith
  have hsquare : epsilonP ^ 2 ≤ epsilonP := by
    nlinarith
  have hproj : (2 * 2 * epsilonP + epsilonP ^ 2) / (2 * h) ≤ gamma / 4 := by
    apply (div_le_iff₀ (show 0 < 2 * h by positivity)).2
    nlinarith
  linarith


end TomographyOracleCore.Revision.FinitePrecision
