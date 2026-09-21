import TomographyOracleCore.Revision.BinaryPauliFourthBasis

namespace TomographyOracleCore.Revision.CliffordFourthOmega

open BinaryCliffordNeutralFourth BinaryPauliFourthBasis
open scoped BigOperators

noncomputable section

def pauliFourthPower (K : ℕ) (p : PauliLabel K) : FourthPauliMatrix K :=
  matrixTensorFour (hermitianBinaryPauliMatrix K p) (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K p) (hermitianBinaryPauliMatrix K p)

/-- The exceptional Clifford invariant, with the normalization Omega = d Pi. -/
def pauliFourthOmega (K : ℕ) : FourthPauliMatrix K :=
  ((2 : ℂ) ^ K)⁻¹ • ∑ p : PauliLabel K, pauliFourthPower K p

theorem unitaryFourthConjugation_pauliFourthPower
    (K : ℕ) {g : binarySymplecticGroup K}
    {U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ}
    (hU : IsUnitaryPauliLift K g U) (p : PauliLabel K) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) (pauliFourthPower K p) =
      pauliFourthPower K (g.val p) := by
  obtain ⟨c, _, hc, hconj⟩ := hU.conjugates_hermitian K p
  unfold pauliFourthPower
  rw [unitaryFourthConjugation_tensorFour, hconj, matrixTensorFour_smul]
  have hfour : c * c * c * c = 1 := by
    calc
      _ = (c * c) * (c * c) := by ring
      _ = 1 := by rw [hc]; norm_num
  rw [hfour, one_smul]

/-- Any physical Clifford Pauli lift fixes Omega exactly. -/
theorem unitaryFourthConjugation_fixes_omega
    (K : ℕ) {g : binarySymplecticGroup K}
    {U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ}
    (hU : IsUnitaryPauliLift K g U) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) (pauliFourthOmega K) =
      pauliFourthOmega K := by
  unfold pauliFourthOmega
  rw [map_smul, map_sum]
  simp_rw [unitaryFourthConjugation_pauliFourthPower K hU]
  congr 1
  exact Equiv.sum_comp g.val.toEquiv (pauliFourthPower K)

theorem hermitianPauliPhase_four (K : ℕ) (p : PauliLabel K) :
    hermitianPauliPhase K p * hermitianPauliPhase K p *
      hermitianPauliPhase K p * hermitianPauliPhase K p = 1 := by
  unfold hermitianPauliPhase
  split_ifs <;> simp [Complex.I_mul_I]

theorem pauliFourthPower_eq_binary (K : ℕ) (p : PauliLabel K) :
    pauliFourthPower K p =
      matrixTensorFour (binaryPauliMatrix K p) (binaryPauliMatrix K p)
        (binaryPauliMatrix K p) (binaryPauliMatrix K p) := by
  unfold pauliFourthPower hermitianBinaryPauliMatrix
  rw [matrixTensorFour_smul, hermitianPauliPhase_four, one_smul]

def fourthPauliShiftMatches {K : ℕ}
    (x y : FourthIndex (PauliBinaryWord K)) (a : PauliBinaryWord K) : Prop :=
  x.1 = y.1 + a ∧ x.2.1 = y.2.1 + a ∧
    x.2.2.1 = y.2.2.1 + a ∧ x.2.2.2 = y.2.2.2 + a

instance {K : ℕ} (x y : FourthIndex (PauliBinaryWord K)) (a : PauliBinaryWord K) :
    Decidable (fourthPauliShiftMatches x y a) := by
  unfold fourthPauliShiftMatches
  infer_instance

def fourthWordSum {K : ℕ} (x : FourthIndex (PauliBinaryWord K)) : PauliBinaryWord K :=
  x.1 + x.2.1 + x.2.2.1 + x.2.2.2

/-- Exact monomial entry of four identical Paulis: the fourth roots of
unity cancel, leaving one binary character. -/
theorem pauliFourthPower_apply
    (K : ℕ) (p : PauliLabel K) (x y : FourthIndex (PauliBinaryWord K)) :
    pauliFourthPower K p x y =
      if fourthPauliShiftMatches x y p.1 then
        (binaryWordCharacter K p.2 (fourthWordSum y) : ℂ) else 0 := by
  rw [pauliFourthPower_eq_binary, matrixTensorFour_apply]
  by_cases h0 : x.1 = y.1 + p.1 <;>
    by_cases h1 : x.2.1 = y.2.1 + p.1 <;>
    by_cases h2 : x.2.2.1 = y.2.2.1 + p.1 <;>
    by_cases h3 : x.2.2.2 = y.2.2.2 + p.1 <;>
    simp [binaryPauliMatrix, fourthPauliShiftMatches, fourthWordSum,
      h0, h1, h2, h3, binaryWordCharacter_add_right]

theorem shiftMatches_unique
    {K : ℕ} (x y : FourthIndex (PauliBinaryWord K)) (a : PauliBinaryWord K)
    (h : fourthPauliShiftMatches x y a) : a = x.1 + y.1 := by
  rw [h.1]
  symm
  calc
    y.1 + a + y.1 = (y.1 + y.1) + a := by abel
    _ = a := by rw [binaryWord_add_self, zero_add]

def fourthOmegaSupport {K : ℕ} (x y : FourthIndex (PauliBinaryWord K)) : Prop :=
  fourthWordSum y = 0 ∧ fourthPauliShiftMatches x y (x.1 + y.1)

instance {K : ℕ} (x y : FourthIndex (PauliBinaryWord K)) :
    Decidable (fourthOmegaSupport x y) := by
  unfold fourthOmegaSupport
  infer_instance

/-- Walsh orthogonality evaluates the full Pauli sum: Omega is an explicit
zero-one matrix in binary-word coordinates. -/
theorem pauliFourthOmega_apply
    (K : ℕ) (x y : FourthIndex (PauliBinaryWord K)) :
    pauliFourthOmega K x y = if fourthOmegaSupport x y then 1 else 0 := by
  classical
  unfold pauliFourthOmega
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  simp_rw [pauliFourthPower_apply]
  have hinner (a : PauliBinaryWord K) :
      (∑ b : PauliBinaryWord K,
        if fourthPauliShiftMatches x y a then
          (binaryWordCharacter K b (fourthWordSum y) : ℂ) else 0) =
        if fourthPauliShiftMatches x y a then
          (if fourthWordSum y = 0 then (2 : ℂ) ^ K else 0) else 0 := by
    by_cases ha : fourthPauliShiftMatches x y a
    · simp only [ha, if_true]
      exact sum_complex_binaryWordCharacter K _
    · simp [ha]
  simp_rw [hinner]
  by_cases hy : fourthWordSum y = 0
  · simp only [hy, if_true]
    rw [Finset.sum_eq_single (x.1 + y.1)]
    · by_cases hm : fourthPauliShiftMatches x y (x.1 + y.1)
      · simp [fourthOmegaSupport, hy, hm]
      · simp [fourthOmegaSupport, hy, hm]
    · intro a ha hane
      have hm : ¬fourthPauliShiftMatches x y a := fun h => hane (shiftMatches_unique x y a h)
      simp [hm]
    · simp
  · simp [hy, fourthOmegaSupport]

end

end TomographyOracleCore.Revision.CliffordFourthOmega
