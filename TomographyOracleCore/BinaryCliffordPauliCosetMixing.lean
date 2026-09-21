import TomographyOracleCore.BinaryCliffordPauliCosetEnsemble

namespace TomographyOracleCore

/-!
# Distributional Pauli invariance and two-mixing

This module verifies the two finite-ensemble hypotheses that precede Webb's
matrix third-twirl argument.  Left multiplication by any Hermitian Pauli
permutes the Pauli-coset labels, up to a nonzero global phase, and the second
coordinate uniformly mixes every ordered pair class with fixed commutation
sign.

These statements are inputs to, not substitutes for, the matrix 3-twirl
identity.
-/

/-- Nonzero phase in the product of two Hermitian binary Paulis. -/
noncomputable def hermitianPauliProductPhase
    (K : ℕ) (a b : PauliLabel K) : ℂ :=
  hermitianPauliPhase K a * hermitianPauliPhase K b *
    (binaryWordCharacter K a.2 b.1 : ℂ) *
      (hermitianPauliPhase K (a + b))⁻¹

theorem hermitianPauliProductPhase_ne_zero
    (K : ℕ) (a b : PauliLabel K) :
    hermitianPauliProductPhase K a b ≠ 0 := by
  unfold hermitianPauliProductPhase
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (hermitianPauliPhase_ne_zero K a)
        (hermitianPauliPhase_ne_zero K b)
    · exact_mod_cast binarySign_ne_zero (binaryDotProduct K a.2 b.1)
  · exact inv_ne_zero (hermitianPauliPhase_ne_zero K (a + b))

@[simp] theorem norm_hermitianPauliPhase
    (K : ℕ) (p : PauliLabel K) :
    ‖hermitianPauliPhase K p‖ = 1 := by
  unfold hermitianPauliPhase
  split_ifs <;> simp

@[simp] theorem abs_binaryWordCharacter
    (K : ℕ) (x y : PauliBinaryWord K) :
    |binaryWordCharacter K x y| = 1 := by
  rcases binaryWordCharacter_eq_one_or_neg_one K x y with h | h
  · simp [h]
  · simp [h]

/-- The explicit multiplication phase is on the unit circle. -/
theorem norm_hermitianPauliProductPhase
    (K : ℕ) (a b : PauliLabel K) :
    ‖hermitianPauliProductPhase K a b‖ = 1 := by
  simp [hermitianPauliProductPhase]

/-- Hermitian Paulis multiply to the Hermitian Pauli at the sum label, up
to an explicit nonzero phase. -/
theorem hermitianBinaryPauliMatrix_mul
    (K : ℕ) (a b : PauliLabel K) :
    hermitianBinaryPauliMatrix K a * hermitianBinaryPauliMatrix K b =
      hermitianPauliProductPhase K a b •
        hermitianBinaryPauliMatrix K (a + b) := by
  unfold hermitianBinaryPauliMatrix hermitianPauliProductPhase
  rw [Matrix.smul_mul, Matrix.mul_smul, binaryPauliMatrix_mul,
    smul_smul, smul_smul]
  simp only [smul_smul]
  apply congrArg (fun c : ℂ ↦ c • binaryPauliMatrix K (a + b))
  field_simp [hermitianPauliPhase_ne_zero]

/-- Translation of the Pauli coordinate is a permutation of the finite
Pauli-coset ensemble. -/
noncomputable def pauliCosetLeftTranslation
    (K : ℕ) (b : PauliLabel K) :
    PauliCosetCliffordEnsemble K ≃ PauliCosetCliffordEnsemble K where
  toFun e := (b + e.1, e.2)
  invFun e := (b + e.1, e.2)
  left_inv e := by
    apply Prod.ext
    · change b + (b + e.1) = e.1
      rw [← add_assoc, pauliLabel_add_self, zero_add]
    · rfl
  right_inv e := by
    apply Prod.ext
    · change b + (b + e.1) = e.1
      rw [← add_assoc, pauliLabel_add_self, zero_add]
    · rfl

/-- Concrete distributional Pauli invariance: left multiplication by a
Pauli sends each ensemble unitary to the translated label, up to global
phase. -/
theorem pauliCosetCliffordUnitary_left_pauli
    (K : ℕ) (b : PauliLabel K)
    (e : PauliCosetCliffordEnsemble K) :
    ∃ phase : ℂ, phase ≠ 0 ∧
      hermitianBinaryPauliMatrix K b * pauliCosetCliffordUnitary K e =
        phase • pauliCosetCliffordUnitary K
          (pauliCosetLeftTranslation K b e) := by
  refine ⟨hermitianPauliProductPhase K b e.1,
    hermitianPauliProductPhase_ne_zero K b e.1, ?_⟩
  change hermitianBinaryPauliMatrix K b *
      (hermitianBinaryPauliMatrix K e.1 *
        (binaryTransvectionUnitaryLift K e.2).1) =
    hermitianPauliProductPhase K b e.1 •
      (hermitianBinaryPauliMatrix K (b + e.1) *
        (binaryTransvectionUnitaryLift K e.2).1)
  rw [← mul_assoc, hermitianBinaryPauliMatrix_mul, Matrix.smul_mul]

/-- Pauli left invariance with the physically relevant unit-modulus phase. -/
theorem pauliCosetCliffordUnitary_left_pauli_unit_phase
    (K : ℕ) (b : PauliLabel K)
    (e : PauliCosetCliffordEnsemble K) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧
      hermitianBinaryPauliMatrix K b * pauliCosetCliffordUnitary K e =
        phase • pauliCosetCliffordUnitary K
          (pauliCosetLeftTranslation K b e) := by
  refine ⟨hermitianPauliProductPhase K b e.1,
    norm_hermitianPauliProductPhase K b e.1, ?_⟩
  change hermitianBinaryPauliMatrix K b *
      (hermitianBinaryPauliMatrix K e.1 *
        (binaryTransvectionUnitaryLift K e.2).1) =
    hermitianPauliProductPhase K b e.1 •
      (hermitianBinaryPauliMatrix K (b + e.1) *
        (binaryTransvectionUnitaryLift K e.2).1)
  rw [← mul_assoc, hermitianBinaryPauliMatrix_mul, Matrix.smul_mul]

/-- Pair-hit events for the Pauli-coset ensemble depend only on its
symplectic second coordinate. -/
abbrev PauliCosetPairActionEvent
    {K : ℕ} {c : ZMod 2}
    (x : PauliPairClass K c) (A : Finset (PauliPairClass K c)) :=
  {e : PauliCosetCliffordEnsemble K // e.2 • x ∈ A}

noncomputable instance pauliCosetPairActionEventFintype
    {K : ℕ} {c : ZMod 2}
    (x : PauliPairClass K c) (A : Finset (PauliPairClass K c)) :
    Fintype (PauliCosetPairActionEvent x A) :=
  Fintype.ofInjective
    (fun e : PauliCosetPairActionEvent x A ↦ e.1)
    (fun _ _ h ↦ Subtype.ext h)

/-- Factor a Pauli-coset pair-hit event into its free Pauli coordinate and
the corresponding generated-group event. -/
noncomputable def pauliCosetPairActionEventEquiv
    {K : ℕ} {c : ZMod 2}
    (x : PauliPairClass K c) (A : Finset (PauliPairClass K c)) :
    PauliCosetPairActionEvent x A ≃
      PauliLabel K ×
        {g : binaryTransvectionGroup K // g • x ∈ A} where
  toFun e := (e.1.1, ⟨e.1.2, e.2⟩)
  invFun e := ⟨(e.1, e.2.1), e.2.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv e := rfl

/-- Exact Pauli 2-mixing ratio for the uniform Pauli-coset ensemble.  For
every ordered nonidentity pair and every subset of its commutation class,
the image is uniform on that class. -/
theorem uniform_pauliCoset_pair_action_event_ratio
    {K : ℕ} {c : ZMod 2}
    (x : PauliPairClass K c) (A : Finset (PauliPairClass K c)) :
    ((Fintype.card (PauliCosetPairActionEvent x A) : ℕ) : ℝ) /
        Fintype.card (PauliCosetCliffordEnsemble K) =
      (A.card : ℝ) / Fintype.card (PauliPairClass K c) := by
  classical
  have hpauli : (Fintype.card (PauliLabel K) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PauliLabel K) ≠ 0)
  calc
    ((Fintype.card (PauliCosetPairActionEvent x A) : ℕ) : ℝ) /
          Fintype.card (PauliCosetCliffordEnsemble K) =
        ((Fintype.card (PauliLabel K) : ℕ) : ℝ) *
            ((Fintype.card
              {g : binaryTransvectionGroup K // g • x ∈ A} : ℕ) : ℝ) /
          (((Fintype.card (PauliLabel K) : ℕ) : ℝ) *
            Fintype.card (binaryTransvectionGroup K)) := by
      rw [Fintype.card_congr (pauliCosetPairActionEventEquiv x A)]
      change
        ((Fintype.card
          (PauliLabel K ×
            {g : binaryTransvectionGroup K // g • x ∈ A}) : ℕ) : ℝ) /
            Fintype.card
              (PauliLabel K × binaryTransvectionGroup K) = _
      rw [Fintype.card_prod (PauliLabel K)
          {g : binaryTransvectionGroup K // g • x ∈ A},
        Fintype.card_prod (PauliLabel K) (binaryTransvectionGroup K)]
      push_cast
      rfl
    _ = ((Fintype.card
              {g : binaryTransvectionGroup K // g • x ∈ A} : ℕ) : ℝ) /
          Fintype.card (binaryTransvectionGroup K) := by
      field_simp [hpauli]
    _ = (A.card : ℝ) / Fintype.card (PauliPairClass K c) :=
      uniform_action_event_ratio
        (G := binaryTransvectionGroup K) (x := x) A

end TomographyOracleCore
