import TomographyOracleCore.BinaryCliffordFiniteFourthRepresentation
import TomographyOracleCore.BinaryCliffordFiniteThirdMoment
import TomographyOracleCore.Revision.BinaryPauliTripleSignatures

/-!
# The physical fourth-copy action on neutral Pauli tensors

Using the product of the first three Paulis in the fourth slot absorbs every
Clifford sign twice. Thus the literal Pauli-coset ensemble acts by an exact
permutation of these tensors. No projective group realization is assumed.
-/

namespace TomographyOracleCore.Revision.BinaryCliffordNeutralFourth

open BinaryPauliTripleSignatures
open scoped BigOperators

noncomputable section

theorem matrixTensorFour_smul
    {ι : Type*} (a b c d : ℂ) (A B C D : Matrix ι ι ℂ) :
    matrixTensorFour (a • A) (b • B) (c • C) (d • D) =
      (a * b * c * d) • matrixTensorFour A B C D := by
  ext x y
  simp only [matrixTensorFour_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem unitaryFourthConjugation_tensorFour
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B C D : Matrix ι ι ℂ) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
        (matrixTensorFour A B C D) =
      matrixTensorFour
        ((U.val * A) * U.val.conjTranspose)
        ((U.val * B) * U.val.conjTranspose)
        ((U.val * C) * U.val.conjTranspose)
        ((U.val * D) * U.val.conjTranspose) := by
  change ((matrixTensorFour U.val U.val U.val U.val * matrixTensorFour A B C D) *
    (matrixTensorFour U.val U.val U.val U.val).conjTranspose) = _
  rw [← matrixTensorFour_conjTranspose,
    ← matrixTensorFour_mul, ← matrixTensorFour_mul]

abbrev FourthPauliMatrix (K : ℕ) :=
  Matrix (FourthIndex (PauliBinaryWord K)) (FourthIndex (PauliBinaryWord K)) ℂ

def neutralFourthPauliTensor (K : ℕ) (x : Fin 3 → PauliLabel K) :
    FourthPauliMatrix K :=
  matrixTensorFour
    (hermitianBinaryPauliMatrix K (x 0))
    (hermitianBinaryPauliMatrix K (x 1))
    (hermitianBinaryPauliMatrix K (x 2))
    (hermitianBinaryPauliMatrix K (x 0) * hermitianBinaryPauliMatrix K (x 1) *
      hermitianBinaryPauliMatrix K (x 2))

/-- All signs cancel in the literal fourth-copy conjugation. -/
theorem unitaryFourthConjugation_neutral
    (K : ℕ) {g : binarySymplecticGroup K}
    {U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ}
    (hU : IsUnitaryPauliLift K g U) (x : Fin 3 → PauliLabel K) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
        (neutralFourthPauliTensor K x) =
      neutralFourthPauliTensor K (fun i => g.val (x i)) := by
  obtain ⟨a, _, ha, h0⟩ := hU.conjugates_hermitian K (x 0)
  obtain ⟨b, _, hb, h1⟩ := hU.conjugates_hermitian K (x 1)
  obtain ⟨c, _, hc, h2⟩ := hU.conjugates_hermitian K (x 2)
  unfold neutralFourthPauliTensor
  rw [unitaryFourthConjugation_tensorFour,
    unitaryConjugation_mul, unitaryConjugation_mul, h0, h1, h2]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [matrixTensorFour_smul]
  have hphase : a * b * c * (c * (b * a)) = 1 := by
    calc
      _ = (a * a) * (b * b) * (c * c) := by ring
      _ = 1 := by rw [ha, hb, hc]; norm_num
  rw [hphase, one_smul]

/-- The chosen Pauli-coset lifts implement the unsigned triple action. -/
theorem pauliCosetCliffordFourthAction_neutral
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) (x : Fin 3 → PauliLabel K) :
    pauliCosetCliffordFourthAction K e (neutralFourthPauliTensor K x) =
      neutralFourthPauliTensor K (fun i => e.2.val.val (x i)) :=
  unitaryFourthConjugation_neutral K (pauliCosetCliffordUnitary_spec K e) x

def finiteCliffordFourthAverage (K : ℕ) :
    FourthPauliMatrix K →ₗ[ℂ] FourthPauliMatrix K :=
  (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹ •
    ∑ e : PauliCosetCliffordEnsemble K, pauliCosetCliffordFourthAction K e

def neutralFourthOrbitAverage (K : ℕ) (x : Fin 3 → PauliLabel K) :
    FourthPauliMatrix K :=
  (Fintype.card (binaryTransvectionGroup K) : ℂ)⁻¹ •
    ∑ g : binaryTransvectionGroup K,
      neutralFourthPauliTensor K (fun i => g.val.val (x i))

/-- The free Pauli coordinate cancels from the normalized physical average. -/
theorem finiteCliffordFourthAverage_neutral
    (K : ℕ) (x : Fin 3 → PauliLabel K) :
    finiteCliffordFourthAverage K (neutralFourthPauliTensor K x) =
      neutralFourthOrbitAverage K x := by
  unfold finiteCliffordFourthAverage neutralFourthOrbitAverage
  simp only [LinearMap.smul_apply, LinearMap.sum_apply,
    pauliCosetCliffordFourthAction_neutral]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  change ((Fintype.card (PauliLabel K × binaryTransvectionGroup K) : ℂ)⁻¹ *
    (Fintype.card (PauliLabel K) : ℂ)) = _
  rw [Fintype.card_prod, Nat.cast_mul]
  have hp : (Fintype.card (PauliLabel K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- A right translation of the finite generated group leaves the average
unchanged. -/
theorem neutralFourthOrbitAverage_translate
    (K : ℕ) (g : binaryTransvectionGroup K) (x : Fin 3 → PauliLabel K) :
    neutralFourthOrbitAverage K (fun i => g.val.val (x i)) =
      neutralFourthOrbitAverage K x := by
  unfold neutralFourthOrbitAverage
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight g)
    (fun h : binaryTransvectionGroup K =>
      neutralFourthPauliTensor K (fun i => h.val.val (x i)))

/-- The physical averages have at most thirty distinct neutral values. -/
theorem neutralFourthOrbitAverage_eq_of_signature_eq
    (K : ℕ) (x y : Fin 3 → PauliLabel K)
    (h : tripleSignature K x = tripleSignature K y) :
    neutralFourthOrbitAverage K x = neutralFourthOrbitAverage K y := by
  obtain ⟨g, hg⟩ := exists_map_triple_of_signature_eq K x y h
  have heq : (fun i => g.val.val (x i)) = y := funext hg
  rw [← heq, neutralFourthOrbitAverage_translate]

end

end TomographyOracleCore.Revision.BinaryCliffordNeutralFourth
