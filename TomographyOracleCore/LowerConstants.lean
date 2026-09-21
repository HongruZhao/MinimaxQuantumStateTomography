import TomographyOracleCore.MathlibImports

namespace TomographyOracleCore

/-!
# Explicit constants in the spectral-decay lower bound

These are the constants displayed in the manuscript after Grassmann packing,
the one-copy information calculation, Fano extraction, and the final
dimension comparison.  Defining and proving their positivity does not assert
that the corresponding lower bound has been proved.
-/

/-- Exponent extracted from the metric Grassmann packing argument. -/
noncomputable def grassmannGamma0 : ℝ := 25 / 4608

/-- Information-radius scale used before Fano's inequality. -/
noncomputable def lowerInformationConstant : ℝ :=
  Real.sqrt (3 * grassmannGamma0 / 128)

/-- Coefficient multiplying the three-way hard-family scale. -/
noncomputable def hardFamilyScaleConstant (alpha : ℝ) : ℝ :=
  min (1 / 4) (min ((2 : ℝ) ^ (1 - alpha)) lowerInformationConstant)

/-- One explicit expected-risk constant admitted by the paper's elementary
constant calculation. -/
noncomputable def explicitDecayLowerConstant (alpha : ℝ) : ℝ :=
  11 * hardFamilyScaleConstant alpha / (1024 * Real.sqrt 2)

theorem grassmannGamma0_pos : 0 < grassmannGamma0 := by
  norm_num [grassmannGamma0]

theorem lowerInformationConstant_pos : 0 < lowerInformationConstant := by
  rw [lowerInformationConstant, Real.sqrt_pos]
  exact div_pos (mul_pos (by norm_num) grassmannGamma0_pos) (by norm_num)

theorem hardFamilyScaleConstant_pos (alpha : ℝ) :
    0 < hardFamilyScaleConstant alpha := by
  unfold hardFamilyScaleConstant
  apply lt_min
  · norm_num
  · apply lt_min
    · exact Real.rpow_pos_of_pos (by norm_num) _
    · exact lowerInformationConstant_pos

theorem hardFamilyScaleConstant_le_quarter (alpha : ℝ) :
    hardFamilyScaleConstant alpha ≤ 1 / 4 := by
  exact min_le_left _ _

theorem hardFamilyScaleConstant_le_decay (alpha : ℝ) :
    hardFamilyScaleConstant alpha ≤ (2 : ℝ) ^ (1 - alpha) := by
  exact (min_le_right _ _).trans (min_le_left _ _)

theorem hardFamilyScaleConstant_le_information (alpha : ℝ) :
    hardFamilyScaleConstant alpha ≤ lowerInformationConstant := by
  exact (min_le_right _ _).trans (min_le_right _ _)

theorem explicitDecayLowerConstant_pos (alpha : ℝ) :
    0 < explicitDecayLowerConstant alpha := by
  unfold explicitDecayLowerConstant
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  exact div_pos
    (mul_pos (by norm_num) (hardFamilyScaleConstant_pos alpha))
    (mul_pos (by norm_num) hsqrt)

end TomographyOracleCore
