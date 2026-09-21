import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

/-- Under the intermediate condition `U ≤ D³`, `1/D` is below the
canonical square-root rate for `U` samples. -/
theorem inv_dimension_le_sqrt_dimension_div_samples
    (D U : ℕ) (hD : 0 < D) (hU : 0 < U)
    (hcube : (U : ℝ) ≤ (D : ℝ) ^ 3) :
    1 / (D : ℝ) ≤ Real.sqrt ((D : ℝ) / (U : ℝ)) := by
  have hDreal : 0 < (D : ℝ) := by exact_mod_cast hD
  have hUreal : 0 < (U : ℝ) := by exact_mod_cast hU
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  simp only [div_pow, one_pow]
  apply (div_le_div_iff₀ (sq_pos_of_pos hDreal) hUreal).2
  nlinarith

end TomographyOracleCore
