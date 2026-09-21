import TomographyOracleCore.HardMass

namespace TomographyOracleCore

/-!
# Scalar information-radius algebra for the lower bound

This module proves the exact numerical implication used after the one-copy
information estimate.  It contains no KL-divergence, packing, Fano, or
tomography assertion: those enter only through explicit theorem premises.

No declaration in this file is an axiom.
-/

/-- The square of the manuscript's information-radius constant is the exact
coefficient chosen to leave a factor `1/16` of the Grassmann exponent. -/
theorem lowerInformationConstant_sq :
    lowerInformationConstant ^ 2 = 3 * grassmannGamma0 / 128 := by
  unfold lowerInformationConstant
  exact Real.sq_sqrt
    (div_nonneg (mul_nonneg (by norm_num) grassmannGamma0_pos.le)
      (by norm_num))

/-- Exact scalar information-radius implication from the manuscript.

If `b ≤ c_I m √(k/T)`, then an information bound of the form
`T * 8 b² / (3m)` consumes at most one sixteenth of the Grassmann exponent
`γ₀ m k`. -/
theorem informationRadius_le_grassmannExponent_div_sixteen
    (m k T b : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) (hb : 0 ≤ b)
    (hbscale :
      b ≤ lowerInformationConstant * m * Real.sqrt (k / T)) :
    T * (8 * b ^ 2 / (3 * m)) ≤
      grassmannGamma0 * m * k / 16 := by
  have hquot : 0 ≤ k / T := div_nonneg hk.le hT.le
  have hsqrt : 0 ≤ Real.sqrt (k / T) := Real.sqrt_nonneg _
  have hscaleNonneg :
      0 ≤ lowerInformationConstant * m * Real.sqrt (k / T) :=
    mul_nonneg
      (mul_nonneg lowerInformationConstant_pos.le hm.le) hsqrt
  have hbSq :
      b ^ 2 ≤
        (lowerInformationConstant * m * Real.sqrt (k / T)) ^ 2 :=
    (sq_le_sq₀ hb hscaleNonneg).2 hbscale
  have hsqrtSq : (Real.sqrt (k / T)) ^ 2 = k / T :=
    Real.sq_sqrt hquot
  have hbSqBound :
      b ^ 2 ≤
        (3 * grassmannGamma0 / 128) * m ^ 2 * (k / T) := by
    calc
      b ^ 2 ≤
          (lowerInformationConstant * m * Real.sqrt (k / T)) ^ 2 := hbSq
      _ = lowerInformationConstant ^ 2 * m ^ 2 *
          (Real.sqrt (k / T)) ^ 2 := by ring
      _ = (3 * grassmannGamma0 / 128) * m ^ 2 * (k / T) := by
        rw [lowerInformationConstant_sq, hsqrtSq]
  have hcoefficient : 0 ≤ T * 8 / (3 * m) := by positivity
  calc
    T * (8 * b ^ 2 / (3 * m)) =
        (T * 8 / (3 * m)) * b ^ 2 := by ring
    _ ≤ (T * 8 / (3 * m)) *
        ((3 * grassmannGamma0 / 128) * m ^ 2 * (k / T)) :=
      mul_le_mul_of_nonneg_left hbSqBound hcoefficient
    _ = grassmannGamma0 * m * k / 16 := by
      field_simp [hm.ne', hT.ne']
      ring

/-- Composition with an explicit lower bound on packing log-cardinality. -/
theorem informationRadius_le_logCardinality_div_sixteen
    (m k T b logCardinality : ℝ)
    (hm : 0 < m) (hk : 0 < k) (hT : 0 < T) (hb : 0 ≤ b)
    (hbscale :
      b ≤ lowerInformationConstant * m * Real.sqrt (k / T))
    (hpacking : grassmannGamma0 * m * k ≤ logCardinality) :
    T * (8 * b ^ 2 / (3 * m)) ≤ logCardinality / 16 := by
  exact (informationRadius_le_grassmannExponent_div_sixteen
    m k T b hm hk hT hb hbscale).trans
      (div_le_div_of_nonneg_right hpacking (by norm_num))

/-- The manuscript hard-family mass automatically satisfies the exact scalar
information budget when `η = √(k/T)`. -/
theorem hardFamilyMass_informationRadius_le_grassmannExponent_div_sixteen
    (m : ℕ) (L alpha k T : ℝ)
    (hm : 1 ≤ m) (hL : 0 ≤ L) (hk : 0 < k) (hT : 0 < T) :
    T *
        (8 * (hardFamilyMass m L (Real.sqrt (k / T)) alpha) ^ 2 /
          (3 * (m : ℝ))) ≤
      grassmannGamma0 * (m : ℝ) * k / 16 := by
  have hmReal : 0 < (m : ℝ) := by exact_mod_cast hm
  have heta : 0 ≤ Real.sqrt (k / T) := Real.sqrt_nonneg _
  apply informationRadius_le_grassmannExponent_div_sixteen
    (m : ℝ) k T (hardFamilyMass m L (Real.sqrt (k / T)) alpha)
    hmReal hk hT
  · exact hardFamilyMass_nonnegative m L (Real.sqrt (k / T)) alpha hL heta
  · simpa only [mul_assoc] using
      hardFamilyMass_le_information_scale
        m L (Real.sqrt (k / T)) alpha heta

/-- Hard-family corollary already composed with a supplied Grassmann packing
log-cardinality lower bound. -/
theorem hardFamilyMass_informationRadius_le_logCardinality_div_sixteen
    (m : ℕ) (L alpha k T logCardinality : ℝ)
    (hm : 1 ≤ m) (hL : 0 ≤ L) (hk : 0 < k) (hT : 0 < T)
    (hpacking :
      grassmannGamma0 * (m : ℝ) * k ≤ logCardinality) :
    T *
        (8 * (hardFamilyMass m L (Real.sqrt (k / T)) alpha) ^ 2 /
          (3 * (m : ℝ))) ≤
      logCardinality / 16 := by
  exact
    (hardFamilyMass_informationRadius_le_grassmannExponent_div_sixteen
      m L alpha k T hm hL hk hT).trans
      (div_le_div_of_nonneg_right hpacking (by norm_num))

end TomographyOracleCore
