import TomographyOracleCore.BinaryCliffordWebbHaarBridge
import TomographyOracleCore.BinaryCliffordWebbTotalPauliClassification
import TomographyOracleCore.BinaryPauliTensorBasis

namespace TomographyOracleCore

open scoped BigOperators

noncomputable section

/-- The concrete finite twirl applied to a Hermitian Pauli tensor is exactly
the averaged third moment used by the Webb case analysis. -/
theorem finitePauliCosetThirdTwirl_hermitianPauliTensorThree
    (K : ℕ) (p q r : PauliLabel K) :
    finitePauliCosetThirdTwirl K
        (matrixTensorThree
          (hermitianBinaryPauliMatrix K p)
          (hermitianBinaryPauliMatrix K q)
          (hermitianBinaryPauliMatrix K r)) =
      averagedHermitianPauliThirdMoment K p q r := by
  rfl

/-- Haar averaging fixes the entire six-permutation Webb subspace. -/
theorem pauliHaarThirdTwirl_eq_self_of_mem_webbPermutationSubmodule
    (K : ℕ) (X : ThirdM K)
    (hX : X ∈ webbPermutationSubmodule K) :
    pauliHaarThirdTwirl K X = X := by
  unfold webbPermutationSubmodule at hX
  refine Submodule.span_induction
    (p := fun X _ ↦ pauliHaarThirdTwirl K X = X) ?_ ?_ ?_ ?_ hX
  · intro X hX
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
    rcases hX with hX | hX | hX | hX | hX | hX
    all_goals subst X <;> simp
  · exact map_zero (pauliHaarThirdTwirlLinearMap K)
  · intro X Y hX hY hTX hTY
    change pauliHaarThirdTwirlLinearMap K (X + Y) = X + Y
    change pauliHaarThirdTwirlLinearMap K X = X at hTX
    change pauliHaarThirdTwirlLinearMap K Y = Y at hTY
    rw [map_add, hTX, hTY]
  · intro c X hX hTX
    change pauliHaarThirdTwirlLinearMap K (c • X) = c • X
    change pauliHaarThirdTwirlLinearMap K X = X at hTX
    rw [map_smul, hTX]

/-- Webb's three cases plus Haar fixed-permutations identify the finite and
Haar third moments on every Hermitian Pauli tensor. -/
theorem finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl_on_pauliTensor
    (K : ℕ) (p q r : PauliLabel K) :
    finitePauliCosetThirdTwirl K
        (matrixTensorThree
          (hermitianBinaryPauliMatrix K p)
          (hermitianBinaryPauliMatrix K q)
          (hermitianBinaryPauliMatrix K r)) =
      pauliHaarThirdTwirl K
        (matrixTensorThree
          (hermitianBinaryPauliMatrix K p)
          (hermitianBinaryPauliMatrix K q)
          (hermitianBinaryPauliMatrix K r)) := by
  let P := matrixTensorThree
    (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)
    (hermitianBinaryPauliMatrix K r)
  have hmem : finitePauliCosetThirdTwirl K P ∈
      webbPermutationSubmodule K := by
    rw [finitePauliCosetThirdTwirl_hermitianPauliTensorThree]
    exact averagedHermitianPauliThirdMoment_mem_webbPermutationSubmodule K p q r
  have hfix := pauliHaarThirdTwirl_eq_self_of_mem_webbPermutationSubmodule
    K _ hmem
  have hright := pauliHaarThirdTwirl_finitePauliCosetThirdTwirl K P
  change finitePauliCosetThirdTwirl K P = pauliHaarThirdTwirl K P
  rw [← hright, hfix]

/-- The concrete generated Pauli-coset Clifford ensemble has exactly the
normalized Haar third twirl on every operator. -/
theorem finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl
    (K : ℕ) (X : ThirdM K) :
    finitePauliCosetThirdTwirl K X = pauliHaarThirdTwirl K X := by
  rw [hermitianPauliTensorThree_reconstruction K X]
  change finitePauliCosetThirdTwirlLinearMap K
      (((((2 : ℂ) ^ K) ^ 3))⁻¹ •
        ∑ p : PauliLabel K, ∑ q : PauliLabel K, ∑ r : PauliLabel K,
          (∑ a : TripleIndex (PauliBinaryWord K),
            ∑ b : TripleIndex (PauliBinaryWord K),
              hermitianPauliTensorThree K p q r b a * X a b) •
            hermitianPauliTensorThree K p q r) =
    pauliHaarThirdTwirlLinearMap K
      (((((2 : ℂ) ^ K) ^ 3))⁻¹ •
        ∑ p : PauliLabel K, ∑ q : PauliLabel K, ∑ r : PauliLabel K,
          (∑ a : TripleIndex (PauliBinaryWord K),
            ∑ b : TripleIndex (PauliBinaryWord K),
              hermitianPauliTensorThree K p q r b a * X a b) •
            hermitianPauliTensorThree K p q r)
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  simpa [hermitianPauliTensorThree] using
    finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl_on_pauliTensor K p q r

/-- Linear-map form of the exact third-design identity. -/
theorem finitePauliCosetThirdTwirlLinearMap_eq_pauliHaarThirdTwirlLinearMap
    (K : ℕ) :
    finitePauliCosetThirdTwirlLinearMap K =
      pauliHaarThirdTwirlLinearMap K := by
  apply LinearMap.ext
  intro X
  exact finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl K X

end
end TomographyOracleCore

