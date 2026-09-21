import TomographyOracleCore.Revision.BinaryPauliFourthBasis
import TomographyOracleCore.BinaryCliffordFiniteSecondMoment

namespace TomographyOracleCore.Revision.BinaryCliffordFourthRange

open BinaryCliffordNeutralFourth BinaryPauliFourthBasis BinaryPauliTripleSignatures
open scoped BigOperators

noncomputable section

/-- Pointwise physical conjugation, with all dependence on the free Pauli
coordinate collected in a single commutation character. -/
theorem pauliCosetFourthAction_character
    (K : ℕ) (a : PauliLabel K) (g : binaryTransvectionGroup K)
    (p : Fin 4 → PauliLabel K) :
    pauliCosetCliffordFourthAction K (a, g) (hermitianPauliTensorFour K p) =
      ((∏ i, binaryTransvectionHermitianPhase K g (p i)) *
        (pauliCharacter K a (∑ i, g.val.val (p i)) : ℂ)) •
          hermitianPauliTensorFour K (fun i => g.val.val (p i)) := by
  change unitaryMatrixConjugationLinearMap
      (unitaryTensorFourth (pauliCosetCliffordUnitary K (a, g)))
      (matrixTensorFour (hermitianBinaryPauliMatrix K (p 0))
        (hermitianBinaryPauliMatrix K (p 1)) (hermitianBinaryPauliMatrix K (p 2))
        (hermitianBinaryPauliMatrix K (p 3))) = _
  rw [unitaryFourthConjugation_tensorFour]
  simp_rw [pauliCosetCliffordUnitary_conjugates_hermitianPauli]
  rw [matrixTensorFour_smul]
  change _ • matrixTensorFour _ _ _ _ = _ • matrixTensorFour _ _ _ _
  congr 1
  simp only [Fin.prod_univ_four, Fin.sum_univ_four, pauliCharacter_add_right]
  push_cast
  ring

theorem sum_complex_pauliCharacter_right_eq_zero
    (K : ℕ) (v : PauliLabel K) (hv : v ≠ 0) :
    (∑ a : PauliLabel K, (pauliCharacter K a v : ℂ)) = 0 := by
  have h : (∑ a : PauliLabel K, pauliCharacter K a v) = 0 := by
    simpa only [pauliCharacter_comm K _ v] using sum_pauliCharacter_eq_zero K hv
  exact_mod_cast h

/-- Every nonneutral tensor is annihilated by the actual finite ensemble. -/
theorem finiteCliffordFourthAverage_eq_zero_of_sum_ne_zero
    (K : ℕ) (p : Fin 4 → PauliLabel K) (hsum : ∑ i, p i ≠ 0) :
    finiteCliffordFourthAverage K (hermitianPauliTensorFour K p) = 0 := by
  unfold finiteCliffordFourthAverage
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  suffices hz : (∑ e : PauliCosetCliffordEnsemble K,
      pauliCosetCliffordFourthAction K e (hermitianPauliTensorFour K p)) = 0 by
    rw [hz, smul_zero]
  rw [Fintype.sum_prod_type_right]
  apply Finset.sum_eq_zero
  intro g hg
  simp_rw [pauliCosetFourthAction_character]
  rw [← Finset.sum_smul, ← Finset.mul_sum]
  have hsumg : (∑ i, g.val.val (p i)) ≠ 0 := by
    rw [← map_sum]
    intro hz
    apply hsum
    exact g.val.val.injective (by simpa only [map_zero] using hz)
  rw [sum_complex_pauliCharacter_right_eq_zero K _ hsumg, mul_zero, zero_smul]

/-- A zero-sum ordinary Pauli tensor is a nonzero scalar multiple of a
neutral product tensor. -/
theorem hermitianPauliTensorFour_eq_smul_neutral_of_sum_zero
    (K : ℕ) (p : Fin 4 → PauliLabel K) (hsum : ∑ i, p i = 0) :
    ∃ c : ℂ, c ≠ 0 ∧ hermitianPauliTensorFour K p =
      c • neutralFourthPauliTensor K ![p 0, p 1, p 2] := by
  have heq : p 0 + p 1 + p 2 = p 3 := by
    rw [Fin.sum_univ_four] at hsum
    have h := congrArg (fun v => v + p 3) hsum
    simpa only [add_assoc, pauliLabel_add_self, add_zero, zero_add] using h
  let c := hermitianPauliProductPhase K (p 0) (p 1) *
    hermitianPauliProductPhase K (p 0 + p 1) (p 2)
  have hc : c ≠ 0 := mul_ne_zero
    (hermitianPauliProductPhase_ne_zero K _ _)
    (hermitianPauliProductPhase_ne_zero K _ _)
  have hproduct : hermitianBinaryPauliMatrix K (p 0) *
      hermitianBinaryPauliMatrix K (p 1) * hermitianBinaryPauliMatrix K (p 2) =
      c • hermitianBinaryPauliMatrix K (p 3) := by
    rw [hermitianBinaryPauliMatrix_mul, Matrix.smul_mul,
      hermitianBinaryPauliMatrix_mul, smul_smul, heq]
  have hneutral : neutralFourthPauliTensor K ![p 0, p 1, p 2] =
      c • hermitianPauliTensorFour K p := by
    change matrixTensorFour (hermitianBinaryPauliMatrix K (p 0))
      (hermitianBinaryPauliMatrix K (p 1)) (hermitianBinaryPauliMatrix K (p 2))
      (hermitianBinaryPauliMatrix K (p 0) * hermitianBinaryPauliMatrix K (p 1) *
        hermitianBinaryPauliMatrix K (p 2)) = _
    rw [hproduct]
    change matrixTensorFour (hermitianBinaryPauliMatrix K (p 0))
      (hermitianBinaryPauliMatrix K (p 1)) (hermitianBinaryPauliMatrix K (p 2))
      (c • hermitianBinaryPauliMatrix K (p 3)) =
      c • matrixTensorFour (hermitianBinaryPauliMatrix K (p 0))
        (hermitianBinaryPauliMatrix K (p 1)) (hermitianBinaryPauliMatrix K (p 2))
        (hermitianBinaryPauliMatrix K (p 3))
    simpa only [one_smul, one_mul] using
      matrixTensorFour_smul 1 1 1 c
        (hermitianBinaryPauliMatrix K (p 0)) (hermitianBinaryPauliMatrix K (p 1))
        (hermitianBinaryPauliMatrix K (p 2)) (hermitianBinaryPauliMatrix K (p 3))
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  rw [hneutral, smul_smul, inv_mul_cancel₀ hc, one_smul]

def neutralFourthAverageSpan (K : ℕ) : Submodule ℂ (FourthPauliMatrix K) :=
  Submodule.span ℂ (Set.range (neutralFourthOrbitAverage K))

/-- The full physical fourth-copy average takes its values in the span of
the neutral orbit averages. No range or commutant premise is assumed. -/
theorem finiteCliffordFourthAverage_mem_neutralAverageSpan
    (K : ℕ) (X : FourthPauliMatrix K) :
    finiteCliffordFourthAverage K X ∈ neutralFourthAverageSpan K := by
  have hX : X ∈ Submodule.span ℂ (Set.range (hermitianPauliTensorFour K)) := by
    rw [span_hermitianPauliTensorFour_eq_top]
    trivial
  induction hX using Submodule.span_induction with
  | mem Y hY =>
    obtain ⟨p, rfl⟩ := hY
    by_cases hsum : ∑ i, p i = 0
    · obtain ⟨c, _, heq⟩ := hermitianPauliTensorFour_eq_smul_neutral_of_sum_zero K p hsum
      rw [heq, map_smul, finiteCliffordFourthAverage_neutral]
      exact Submodule.smul_mem _ c (Submodule.subset_span ⟨_, rfl⟩)
    · rw [finiteCliffordFourthAverage_eq_zero_of_sum_ne_zero K p hsum]
      exact Submodule.zero_mem _
  | zero => simpa only [map_zero] using (neutralFourthAverageSpan K).zero_mem
  | add Y Z hY hZ ihY ihZ =>
    simpa only [map_add] using (neutralFourthAverageSpan K).add_mem ihY ihZ
  | smul c Y hY ihY =>
    simpa only [map_smul] using (neutralFourthAverageSpan K).smul_mem c ihY

/-- Choose one value for each realized signature. Unused signatures receive
zero and do not enter any assertion about the physical ensemble. -/
def fourthSignatureAverage (K : ℕ) (s : TripleSignature) : FourthPauliMatrix K :=
  if h : ∃ x : Fin 3 → PauliLabel K, tripleSignature K x = s then
    neutralFourthOrbitAverage K (Classical.choose h)
  else 0

theorem fourthSignatureAverage_at_signature
    (K : ℕ) (x : Fin 3 → PauliLabel K) :
    fourthSignatureAverage K (tripleSignature K x) = neutralFourthOrbitAverage K x := by
  have hex : ∃ y : Fin 3 → PauliLabel K, tripleSignature K y = tripleSignature K x :=
    ⟨x, rfl⟩
  rw [fourthSignatureAverage, dif_pos hex]
  exact neutralFourthOrbitAverage_eq_of_signature_eq K _ x (Classical.choose_spec hex)

theorem finiteCliffordFourthAverage_range_le_signatureSpan (K : ℕ) :
    (finiteCliffordFourthAverage K).range ≤
      Submodule.span ℂ (Set.range (fourthSignatureAverage K)) := by
  intro Y hY
  obtain ⟨X, rfl⟩ := hY
  have hmem := finiteCliffordFourthAverage_mem_neutralAverageSpan K X
  apply Submodule.span_mono _ hmem
  rintro Z ⟨x, rfl⟩
  exact ⟨tripleSignature K x, fourthSignatureAverage_at_signature K x⟩

/-- Unconditional dimension bound for the range of the literal physical
four-copy Clifford average, uniformly in the number of qubits. -/
theorem finrank_finiteCliffordFourthAverage_range_le_thirty (K : ℕ) :
    Module.finrank ℂ (finiteCliffordFourthAverage K).range ≤ 30 := by
  classical
  refine (Submodule.finrank_mono
    (finiteCliffordFourthAverage_range_le_signatureSpan K)).trans ?_
  refine (finrank_span_le_card (Set.range (fourthSignatureAverage K))).trans ?_
  rw [Set.toFinset_card]
  exact (Fintype.card_range_le (fourthSignatureAverage K)).trans_eq card_tripleSignature

end

end TomographyOracleCore.Revision.BinaryCliffordFourthRange
