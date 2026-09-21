import TomographyOracleCore.Revision.BinaryPauliOrbitClassification

/-!
# Thirty possible fourth-copy Pauli orbit signatures

A zero-sum quadruple is determined by its first three labels. Its orbit is
determined by the binary linear relations among those labels and their three
symplectic pairings. There are exactly thirty compatible signatures. The
finite count below is checked by kernel reduction, not `native_decide`.
-/

namespace TomographyOracleCore.Revision.BinaryPauliTripleSignatures

open BinaryPauliOrbitClassification
open scoped BigOperators

def tripleCoefficients (a : Fin 8) (i : Fin 3) : ZMod 2 :=
  if a.val.testBit i.val then 1 else 0

theorem tripleCoefficients_zero : tripleCoefficients 0 = 0 := by decide

theorem tripleCoefficients_xor : ∀ a b : Fin 8,
    tripleCoefficients (a ^^^ b) = tripleCoefficients a + tripleCoefficients b := by
  decide

theorem tripleCoefficients_surjective : Function.Surjective tripleCoefficients := by
  decide

def alternatingTriplePairing (b : Fin 3 → ZMod 2) : Fin 3 → Fin 3 → ZMod 2 :=
  ![![0, b 0, b 1], ![b 0, 0, b 2], ![b 1, b 2, 0]]

abbrev TripleSignatureCode := (Fin 8 → Bool) × (Fin 3 → ZMod 2)

def ValidTripleSignature (s : TripleSignatureCode) : Prop :=
  s.1 0 = true ∧
  (∀ a b : Fin 8, s.1 a = true → s.1 b = true → s.1 (a ^^^ b) = true) ∧
  (∀ a : Fin 8, s.1 a = true → ∀ i : Fin 3,
    ∑ j, tripleCoefficients a j * alternatingTriplePairing s.2 j i = 0)

instance (s : TripleSignatureCode) : Decidable (ValidTripleSignature s) := by
  unfold ValidTripleSignature
  infer_instance

abbrev TripleSignature := {s : TripleSignatureCode // ValidTripleSignature s}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Exhaustive count of all relation spaces and alternating pairings that
vanish on those relations. -/
theorem card_tripleSignature : Fintype.card TripleSignature = 30 := by
  decide

noncomputable section

def tripleSignatureCode (K : ℕ) (x : Fin 3 → PauliLabel K) : TripleSignatureCode :=
  (fun a => decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients a) = 0),
    ![pauliSymplecticForm K (x 0) (x 1),
      pauliSymplecticForm K (x 0) (x 2),
      pauliSymplecticForm K (x 1) (x 2)])

theorem alternatingTriplePairing_signature_eq
    (K : ℕ) (x : Fin 3 → PauliLabel K) (i j : Fin 3) :
    alternatingTriplePairing (tripleSignatureCode K x).2 i j =
      pauliSymplecticForm K (x i) (x j) := by
  fin_cases i <;> fin_cases j <;>
    simp only [alternatingTriplePairing, tripleSignatureCode,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      pauliSymplecticForm_self] <;>
    first | rfl | exact pauliSymplecticForm_symm K _ _

theorem tripleSignatureCode_valid (K : ℕ) (x : Fin 3 → PauliLabel K) :
    ValidTripleSignature (tripleSignatureCode K x) := by
  refine ⟨?_, ?_, ?_⟩
  · change decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients 0) = 0) = true
    simp [tripleCoefficients_zero]
  · intro a b ha hb
    change decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients a) = 0) = true at ha
    change decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients b) = 0) = true at hb
    change decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients (a ^^^ b)) = 0) = true
    simp only [decide_eq_true_eq] at ha hb ⊢
    rw [tripleCoefficients_xor, map_add, ha, hb, add_zero]
  · intro a ha i
    change decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients a) = 0) = true at ha
    have hz := of_decide_eq_true ha
    have hb := congrArg (fun v => pauliSymplecticForm K v (x i)) hz
    simp only [map_zero, LinearMap.zero_apply, Fintype.linearCombination_apply,
      map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at hb
    simpa only [alternatingTriplePairing_signature_eq] using hb

def tripleSignature (K : ℕ) (x : Fin 3 → PauliLabel K) : TripleSignature :=
  ⟨tripleSignatureCode K x, tripleSignatureCode_valid K x⟩

/-- The finite signature is complete, including all dependent triples. -/
theorem exists_map_triple_of_signature_eq
    (K : ℕ) (x y : Fin 3 → PauliLabel K)
    (h : tripleSignature K x = tripleSignature K y) :
    ∃ g : binaryTransvectionGroup K, ∀ i, g.1.1 (x i) = y i := by
  have hc : tripleSignatureCode K x = tripleSignatureCode K y := congrArg Subtype.val h
  apply exists_map_family_of_relations_and_pairings K x y
  · intro a
    obtain ⟨b, rfl⟩ := tripleCoefficients_surjective a
    have he := congrArg (fun s : TripleSignatureCode => s.1 b) hc
    change decide (Fintype.linearCombination (ZMod 2) x (tripleCoefficients b) = 0) =
      decide (Fintype.linearCombination (ZMod 2) y (tripleCoefficients b) = 0) at he
    exact decide_eq_decide.mp he
  · intro i j
    rw [← alternatingTriplePairing_signature_eq,
      ← alternatingTriplePairing_signature_eq, hc]

end

end TomographyOracleCore.Revision.BinaryPauliTripleSignatures
