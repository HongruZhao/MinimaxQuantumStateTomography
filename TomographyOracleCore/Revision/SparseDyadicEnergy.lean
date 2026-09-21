import TomographyOracleCore.Revision.SparseGoodPartitionBound
import TomographyOracleCore.Revision.SparseBadPartitionFraction

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace TomographyOracleCore.Revision.SparseDyadicEnergy

open SparseCoefficientGeometry SparseSampleSuprema SparseDyadicScales SparseRecursionWeights
open SparseGoodPartitionBound SparseBadPartitionFraction
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The three terms in the proved quadratic estimate need coefficients
4, 16*C, and 64*C^2. Since C>=1, 64*C^2 suffices for all three. -/
def energyConstant : ℝ := 64 * crossConstant ^ 2

theorem crossConstant_ge_one : 1 ≤ crossConstant := by norm_num [crossConstant, recursionConstant]
theorem energyConstant_pos : 0 < energyConstant := by
  have h := crossConstant_ge_one
  unfold energyConstant
  positivity

theorem scalar_quadratic_bound {F U V : ℝ} (h : F ^ 2 ≤ U + V * F) :
    F ^ 2 ≤ 2 * U + V ^ 2 := by nlinarith [sq_nonneg (F - V)]

/-- The sharp sparse-energy estimate at every retained dyadic scale, on one
explicit event with controlled probability. All auxiliary proof inputs have
been discharged into the sample law and its sixth-moment condition elsewhere. -/
theorem sparseNorm_sq_le_on_good_event {N : ℕ} (X : Fin N → E)
    {kappa s M q : ℝ} (hkappa : 0 < kappa) (hs : 0 < s) (hM : 0 ≤ M) (hq : 0 ≤ q)
    (hentry : ∀ i j, i ≠ j → |⟪X i, X j⟫_ℝ| ≤ M)
    (hfixed : ∀ i, ‖X i‖ ^ 2 ≤ q)
    (hgood : X ∉ globalFailure kappa s N) (J : ℕ) (hJN : size J ≤ N) :
    sparseNorm X (size J) ^ 2 ≤ energyConstant *
      (q + amplification N * M + kappa ^ 2 * s * Real.sqrt ((N : ℝ) * size J)) := by
  have ha : 0 ≤ amplification N := le_trans (by norm_num) (amplification_ge_one N)
  have hC : 0 ≤ crossConstant := le_trans (by norm_num) crossConstant_ge_one
  have hF := sparseNorm_nonneg X (size J)
  have hW := signalWeight_nonneg (N : ℝ) J
  let B := crossConstant * (amplification N * M + kappa * Real.sqrt s * signalWeight N J * sparseNorm X (size J))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpart : ∀ I : Finset (Fin N), X ∉ SparsePartitionFailure.partitionFailure kappa s I →
      crossNorm X (size J) I ≤ B := by
    intro I hI
    exact crossNorm_le_on_good_partition X I hkappa hs hM hentry hI J hJN
  have hfrac : badFraction kappa s X ≤ 1 / 8 := (lt_of_not_ge hgood).le
  have hf := sparse_energy_le_of_good_fraction X kappa s hq hB hfixed hpart hfrac
  have hpoly : sparseNorm X (size J) ^ 2 ≤
      (2 * q + 8 * crossConstant * amplification N * M) +
        (8 * crossConstant * kappa * Real.sqrt s * signalWeight N J) * sparseNorm X (size J) := by
    dsimp [B] at hf
    nlinarith
  have hquad := scalar_quadratic_bound hpoly
  have heq : (8 * crossConstant * kappa * Real.sqrt s * signalWeight N J) ^ 2 =
      64 * crossConstant ^ 2 * (kappa ^ 2 * s * Real.sqrt ((N : ℝ) * size J)) := by
    simp only [mul_pow, Real.sq_sqrt hs.le, signalWeight_sq]
    ring
  rw [heq] at hquad
  have h1 : 4 ≤ energyConstant := by
    unfold energyConstant
    nlinarith [crossConstant_ge_one]
  have h2 : 16 * crossConstant ≤ energyConstant := by
    unfold energyConstant
    nlinarith [crossConstant_ge_one]
  have h3 : 64 * crossConstant ^ 2 ≤ energyConstant := by
    unfold energyConstant
    nlinarith [sq_nonneg crossConstant]
  have hqmul := mul_le_mul_of_nonneg_right h1 hq
  have hMmul := mul_le_mul_of_nonneg_right h2 (mul_nonneg ha hM)
  have hSmul := mul_le_mul_of_nonneg_right h3
    (show 0 ≤ kappa ^ 2 * s * Real.sqrt ((N : ℝ) * size J) by positivity)
  nlinarith

end
end TomographyOracleCore.Revision.SparseDyadicEnergy
