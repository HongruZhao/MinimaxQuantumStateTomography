import TomographyOracleCore.Revision.CliffordFourthOmega
import TomographyOracleCore.Revision.FourthReplicaPermutations
import TomographyOracleCore.PeriodicCliffordFourthBoundary

namespace TomographyOracleCore.Revision.PauliOmegaProjection

open CliffordFourthOmega FourthReplicaPermutations BinaryCliffordNeutralFourth
open scoped BigOperators InnerProductSpace

noncomputable section

theorem pauliFourthPower_mul (K : ℕ) (p q : PauliLabel K) :
    pauliFourthPower K p * pauliFourthPower K q = pauliFourthPower K (p + q) := by
  simp only [pauliFourthPower_eq_binary, ← matrixTensorFour_mul, binaryPauliMatrix_mul]
  rw [matrixTensorFour_smul]
  have hs : (binaryWordCharacter K p.2 q.1 : ℂ) *
      (binaryWordCharacter K p.2 q.1 : ℂ) = 1 := by
    exact_mod_cast binaryWordCharacter_sq K p.2 q.1
  have hfour : (binaryWordCharacter K p.2 q.1 : ℂ) *
      (binaryWordCharacter K p.2 q.1 : ℂ) *
      (binaryWordCharacter K p.2 q.1 : ℂ) *
      (binaryWordCharacter K p.2 q.1 : ℂ) = 1 := by
    calc
      _ = ((binaryWordCharacter K p.2 q.1 : ℂ) *
        (binaryWordCharacter K p.2 q.1 : ℂ)) ^ 2 := by ring
      _ = 1 := by rw [hs]; norm_num
  rw [hfour, one_smul]

theorem pauliFourthPower_hermitian (K : ℕ) (p : PauliLabel K) :
    (pauliFourthPower K p).IsHermitian := by
  change (pauliFourthPower K p).conjTranspose = pauliFourthPower K p
  simp only [pauliFourthPower, ← matrixTensorFour_conjTranspose,
    hermitianBinaryPauliMatrix_conjTranspose]

theorem sum_pauliFourthPower_mul (K : ℕ) :
    (∑ p : PauliLabel K, pauliFourthPower K p) *
      (∑ p : PauliLabel K, pauliFourthPower K p) =
        (Fintype.card (PauliLabel K) : ℂ) • ∑ p : PauliLabel K, pauliFourthPower K p := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, pauliFourthPower_mul]
  have hshift (p : PauliLabel K) :
      (∑ q : PauliLabel K, pauliFourthPower K (p + q)) =
        ∑ q : PauliLabel K, pauliFourthPower K q :=
    Equiv.sum_comp (Equiv.addLeft p) (pauliFourthPower K)
  simp_rw [hshift]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]

/-- The normalized exceptional sector is an actual orthogonal projection. -/
def pauliFourthProjection (K : ℕ) : FourthPauliMatrix K :=
  (Fintype.card (PauliLabel K) : ℂ)⁻¹ • ∑ p : PauliLabel K, pauliFourthPower K p

theorem pauliFourthProjection_idempotent (K : ℕ) :
    pauliFourthProjection K * pauliFourthProjection K = pauliFourthProjection K := by
  have hc : (Fintype.card (PauliLabel K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  unfold pauliFourthProjection
  rw [smul_mul_smul, sum_pauliFourthPower_mul, smul_smul]
  congr 1
  field_simp

theorem pauliFourthProjection_hermitian (K : ℕ) :
    (pauliFourthProjection K).IsHermitian := by
  change (pauliFourthProjection K).conjTranspose = pauliFourthProjection K
  unfold pauliFourthProjection
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [star_inv₀, star_natCast, (pauliFourthPower_hermitian K _).eq]

theorem card_pauliLabel_complex (K : ℕ) :
    (Fintype.card (PauliLabel K) : ℂ) = ((2 : ℂ) ^ K) ^ 2 := by
  simp [PauliLabel, PauliBinaryWord, Fintype.card_fun, pow_two]

theorem pauliFourthOmega_eq_scaled_projection (K : ℕ) :
    pauliFourthOmega K = (2 : ℂ) ^ K • pauliFourthProjection K := by
  unfold pauliFourthOmega pauliFourthProjection
  rw [smul_smul, card_pauliLabel_complex]
  congr 1
  have h : (2 : ℂ) ^ K ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

theorem replicaPermutation_commute_projection (K : ℕ) (pi : Equiv.Perm (Fin 4)) :
    fourthReplicaPermutationMatrix (ι := PauliBinaryWord K) pi * pauliFourthProjection K =
      pauliFourthProjection K * fourthReplicaPermutationMatrix pi := by
  unfold pauliFourthProjection
  rw [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact fourthReplicaPermutationMatrix_commute_tensorFourth pi _

end
end TomographyOracleCore.Revision.PauliOmegaProjection
