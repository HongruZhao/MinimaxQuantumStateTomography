import TomographyOracleCore.BinaryCliffordWebbClassExpansion

namespace TomographyOracleCore
open scoped BigOperators

abbrev DoubleIndex (ι : Type*) := ι × ι

def matrixTensorTwo {ι : Type*} (A B : Matrix ι ι ℂ) :
    Matrix (DoubleIndex ι) (DoubleIndex ι) ℂ :=
  fun x y ↦ A x.1 y.1 * B x.2 y.2

theorem matrixTensorTwo_mul {ι : Type*} [Fintype ι]
    (A₁ A₂ B₁ B₂ : Matrix ι ι ℂ) :
    matrixTensorTwo (A₁ * B₁) (A₂ * B₂) =
      matrixTensorTwo A₁ A₂ * matrixTensorTwo B₁ B₂ := by
  ext x y
  simp only [matrixTensorTwo, Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem matrixTensorTwo_conjTranspose {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ) :
    matrixTensorTwo A.conjTranspose B.conjTranspose =
      (matrixTensorTwo A B).conjTranspose := by
  ext x y
  simp [matrixTensorTwo, Matrix.conjTranspose_apply]

theorem matrixTensorTwo_smul {ι : Type*}
    (a b : ℂ) (A B : Matrix ι ι ℂ) :
    matrixTensorTwo (a • A) (b • B) =
      (a * b) • matrixTensorTwo A B := by
  ext x y
  simp [matrixTensorTwo]
  ring

noncomputable def pauliCosetCliffordTensorSquare
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  matrixTensorTwo (pauliCosetCliffordUnitary K e).1
    (pauliCosetCliffordUnitary K e).1

noncomputable def conjugatedMatrixTensorTwo
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A B : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  (pauliCosetCliffordTensorSquare K e * matrixTensorTwo A B) *
    (pauliCosetCliffordTensorSquare K e).conjTranspose

theorem conjugatedMatrixTensorTwo_eq
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A B : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorTwo K e A B =
      matrixTensorTwo
        (((pauliCosetCliffordUnitary K e).1 * A) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose)
        (((pauliCosetCliffordUnitary K e).1 * B) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose) := by
  unfold conjugatedMatrixTensorTwo pauliCosetCliffordTensorSquare
  rw [← matrixTensorTwo_conjTranspose]
  rw [← matrixTensorTwo_mul, ← matrixTensorTwo_mul]

noncomputable def hermitianPauliTensorTwo
    (K : ℕ) (p q : PauliLabel K) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  matrixTensorTwo (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)

noncomputable def conjugatedHermitianPauliTensorTwo
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (p q : PauliLabel K) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  conjugatedMatrixTensorTwo K e
    (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)

theorem hermitianBinaryPauliMatrix_sandwich_hermitian
    (K : ℕ) (a p : PauliLabel K) :
    (hermitianBinaryPauliMatrix K a *
        hermitianBinaryPauliMatrix K p) *
      hermitianBinaryPauliMatrix K a =
        (pauliCharacter K a p : ℂ) •
          hermitianBinaryPauliMatrix K p := by
  change (hermitianBinaryPauliMatrix K a *
      (hermitianPauliPhase K p • binaryPauliMatrix K p)) *
    hermitianBinaryPauliMatrix K a =
      (pauliCharacter K a p : ℂ) •
        (hermitianPauliPhase K p • binaryPauliMatrix K p)
  rw [Matrix.mul_smul, Matrix.smul_mul,
    hermitianBinaryPauliMatrix_sandwich, smul_smul]
  module

noncomputable def binaryTransvectionHermitianPhase
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) : ℂ :=
  Classical.choose
    ((binaryTransvectionUnitaryLift_spec K g).conjugates_hermitian K p)

theorem binaryTransvectionHermitianPhase_sq
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) :
    binaryTransvectionHermitianPhase K g p *
      binaryTransvectionHermitianPhase K g p = 1 :=
  (Classical.choose_spec
    ((binaryTransvectionUnitaryLift_spec K g).conjugates_hermitian K p)).2.1

theorem binaryTransvectionHermitianPhase_spec
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) :
    (((binaryTransvectionUnitaryLift K g).1 *
        hermitianBinaryPauliMatrix K p) *
      (binaryTransvectionUnitaryLift K g).1.conjTranspose) =
        binaryTransvectionHermitianPhase K g p •
          hermitianBinaryPauliMatrix K (g.1.1 p) :=
  (Classical.choose_spec
    ((binaryTransvectionUnitaryLift_spec K g).conjugates_hermitian K p)).2.2

theorem pauliCosetCliffordUnitary_conjugates_hermitianPauli
    (K : ℕ) (a : PauliLabel K) (g : binaryTransvectionGroup K)
    (p : PauliLabel K) :
    (((pauliCosetCliffordUnitary K (a, g)).1 *
        hermitianBinaryPauliMatrix K p) *
      (pauliCosetCliffordUnitary K (a, g)).1.conjTranspose) =
      (binaryTransvectionHermitianPhase K g p *
        (pauliCharacter K a (g.1.1 p) : ℂ)) •
          hermitianBinaryPauliMatrix K (g.1.1 p) := by
  change ((((hermitianBinaryPauliMatrix K a *
      (binaryTransvectionUnitaryLift K g).1) *
        hermitianBinaryPauliMatrix K p) *
      (hermitianBinaryPauliMatrix K a *
        (binaryTransvectionUnitaryLift K g).1).conjTranspose) = _)
  rw [Matrix.conjTranspose_mul,
    hermitianBinaryPauliMatrix_conjTranspose]
  calc
    (((hermitianBinaryPauliMatrix K a *
          (binaryTransvectionUnitaryLift K g).1) *
        hermitianBinaryPauliMatrix K p) *
      ((binaryTransvectionUnitaryLift K g).1.conjTranspose *
        hermitianBinaryPauliMatrix K a)) =
        (hermitianBinaryPauliMatrix K a *
          ((((binaryTransvectionUnitaryLift K g).1 *
            hermitianBinaryPauliMatrix K p) *
            (binaryTransvectionUnitaryLift K g).1.conjTranspose))) *
          hermitianBinaryPauliMatrix K a := by noncomm_ring
    _ = (hermitianBinaryPauliMatrix K a *
          (binaryTransvectionHermitianPhase K g p •
            hermitianBinaryPauliMatrix K (g.1.1 p))) *
          hermitianBinaryPauliMatrix K a := by
      rw [binaryTransvectionHermitianPhase_spec]
    _ = binaryTransvectionHermitianPhase K g p •
          ((hermitianBinaryPauliMatrix K a *
            hermitianBinaryPauliMatrix K (g.1.1 p)) *
            hermitianBinaryPauliMatrix K a) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = binaryTransvectionHermitianPhase K g p •
          ((pauliCharacter K a (g.1.1 p) : ℂ) •
            hermitianBinaryPauliMatrix K (g.1.1 p)) := by
      rw [hermitianBinaryPauliMatrix_sandwich_hermitian]
    _ = _ := by rw [smul_smul]

noncomputable def baseLiftedHermitianPauliTensorTwo
    (K : ℕ) (g : binaryTransvectionGroup K)
    (p q : PauliLabel K) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  (binaryTransvectionHermitianPhase K g p *
    binaryTransvectionHermitianPhase K g q) •
      hermitianPauliTensorTwo K (g.1.1 p) (g.1.1 q)

theorem conjugatedHermitianPauliTensorTwo_eq_pairCharacter
    (K : ℕ) (a : PauliLabel K) (g : binaryTransvectionGroup K)
    (p q : PauliLabel K) :
    conjugatedHermitianPauliTensorTwo K (a, g) p q =
      ((pauliCharacter K a (g.1.1 p) : ℂ) *
        (pauliCharacter K a (g.1.1 q) : ℂ)) •
          baseLiftedHermitianPauliTensorTwo K g p q := by
  rw [conjugatedHermitianPauliTensorTwo,
    conjugatedMatrixTensorTwo_eq,
    pauliCosetCliffordUnitary_conjugates_hermitianPauli,
    pauliCosetCliffordUnitary_conjugates_hermitianPauli,
    matrixTensorTwo_smul]
  unfold baseLiftedHermitianPauliTensorTwo hermitianPauliTensorTwo
  rw [smul_smul]
  apply congrArg (fun z : ℂ ↦ z •
    matrixTensorTwo
      (hermitianBinaryPauliMatrix K (g.1.1 p))
      (hermitianBinaryPauliMatrix K (g.1.1 q)))
  ring

theorem sum_pauliCosetClifford_pairCharacter_smul_eq_zero
    {V : Type*} [AddCommMonoid V] [Module ℂ V]
    (K : ℕ) (p q : PauliLabel K) (hsum : p + q ≠ 0)
    (X : binaryTransvectionGroup K → V) :
    ∑ e : PauliCosetCliffordEnsemble K,
      ((pauliCharacter K e.1 (e.2.1.1 p) : ℂ) *
        (pauliCharacter K e.1 (e.2.1.1 q) : ℂ)) • X e.2 = 0 := by
  have hsum3 : p + q + 0 ≠ 0 := by simpa using hsum
  simpa [complexPauliTripleCharacter, pauliTripleCharacter] using
    sum_pauliCosetClifford_tripleCharacter_smul_eq_zero
      K p q 0 hsum3 X

noncomputable def averagedHermitianPauliSecondMoment
    (K : ℕ) (p q : PauliLabel K) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
    ∑ e : PauliCosetCliffordEnsemble K,
      conjugatedHermitianPauliTensorTwo K e p q

theorem averagedHermitianPauliSecondMoment_eq_zero_of_ne
    (K : ℕ) (p q : PauliLabel K) (hpq : p ≠ q) :
    averagedHermitianPauliSecondMoment K p q = 0 := by
  have hsum : p + q ≠ 0 := by
    intro h
    apply hpq
    calc
      p = p + 0 := by simp
      _ = p + (p + q) := by rw [h]
      _ = q := by rw [← add_assoc, pauliLabel_add_self, zero_add]
  unfold averagedHermitianPauliSecondMoment
  have hzero :
      (∑ e : PauliCosetCliffordEnsemble K,
        conjugatedHermitianPauliTensorTwo K e p q) = 0 := by
    simp_rw [show ∀ e : PauliCosetCliffordEnsemble K,
      conjugatedHermitianPauliTensorTwo K e p q =
        ((pauliCharacter K e.1 (e.2.1.1 p) : ℂ) *
          (pauliCharacter K e.1 (e.2.1.1 q) : ℂ)) •
            baseLiftedHermitianPauliTensorTwo K e.2 p q by
      intro e
      exact conjugatedHermitianPauliTensorTwo_eq_pairCharacter
        K e.1 e.2 p q]
    exact sum_pauliCosetClifford_pairCharacter_smul_eq_zero
      K p q hsum (fun g ↦ baseLiftedHermitianPauliTensorTwo K g p q)
  rw [hzero, smul_zero]

theorem conjugatedHermitianPauliTensorTwo_same_eq
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) (p : PauliLabel K) :
    conjugatedHermitianPauliTensorTwo K e p p =
      hermitianPauliTensorTwo K (e.2.1.1 p) (e.2.1.1 p) := by
  obtain ⟨c, hc0, hc2, hc⟩ :=
    (pauliCosetCliffordUnitary_spec K e).conjugates_hermitian K p
  unfold conjugatedHermitianPauliTensorTwo hermitianPauliTensorTwo
  rw [conjugatedMatrixTensorTwo_eq, hc, matrixTensorTwo_smul, hc2,
    one_smul]

theorem averagedHermitianPauliSecondMoment_same_eq_nonidentity_average
    (K : ℕ) (Q : NonidentityPauliLabel K) :
    averagedHermitianPauliSecondMoment K Q.1 Q.1 =
      ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
        ∑ R : NonidentityPauliLabel K,
          hermitianPauliTensorTwo K R.1 R.1 := by
  classical
  let f : NonidentityPauliLabel K →
      Matrix (DoubleIndex (PauliBinaryWord K))
        (DoubleIndex (PauliBinaryWord K)) ℂ :=
    fun R ↦ hermitianPauliTensorTwo K R.1 R.1
  have hgroup :
      (∑ g : binaryTransvectionGroup K,
        hermitianPauliTensorTwo K (g.1.1 Q.1) (g.1.1 Q.1)) =
        Fintype.card (ActionFiber
          (G := binaryTransvectionGroup K) Q Q) •
          (∑ R : NonidentityPauliLabel K,
            hermitianPauliTensorTwo K R.1 R.1) := by
    change (∑ g : binaryTransvectionGroup K, f (g • Q)) =
      Fintype.card (ActionFiber
        (G := binaryTransvectionGroup K) Q Q) •
          (∑ R : NonidentityPauliLabel K, f R)
    exact uniform_action_sum
      (G := binaryTransvectionGroup K)
      (Ω := NonidentityPauliLabel K) Q f
  have hsum :
      (∑ e : PauliCosetCliffordEnsemble K,
        conjugatedHermitianPauliTensorTwo K e Q.1 Q.1) =
        (Fintype.card (PauliLabel K) *
          Fintype.card (ActionFiber
            (G := binaryTransvectionGroup K) Q Q)) •
          (∑ R : NonidentityPauliLabel K,
            hermitianPauliTensorTwo K R.1 R.1) := by
    rw [Fintype.sum_prod_type]
    simp_rw [conjugatedHermitianPauliTensorTwo_same_eq]
    rw [hgroup]
    simp
    simp only [mul_assoc]
  have hpauli : (Fintype.card (PauliLabel K) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PauliLabel K) ≠ 0)
  have horbit :
      (Fintype.card (NonidentityPauliLabel K) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨Q⟩).ne'
  have hfiber :
      (Fintype.card (ActionFiber
        (G := binaryTransvectionGroup K) Q Q) : ℂ) ≠ 0 := by
    letI : Nonempty (ActionFiber
        (G := binaryTransvectionGroup K) Q Q) :=
      ⟨⟨1, one_smul (binaryTransvectionGroup K) Q⟩⟩
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (ActionFiber
        (G := binaryTransvectionGroup K) Q Q) ≠ 0)
  have hcardEnsemble :
      Fintype.card (PauliCosetCliffordEnsemble K) =
        Fintype.card (PauliLabel K) *
          (Fintype.card (NonidentityPauliLabel K) *
            Fintype.card (ActionFiber
              (G := binaryTransvectionGroup K) Q Q)) := by
    rw [Fintype.card_prod,
      action_card (G := binaryTransvectionGroup K)
        (Ω := NonidentityPauliLabel K) Q]
  have hcoeff :
      (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹ *
          (Fintype.card (PauliLabel K) *
            Fintype.card (ActionFiber
              (G := binaryTransvectionGroup K) Q Q) : ℕ) =
        (Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹ := by
    rw [hcardEnsemble]
    push_cast
    field_simp [hpauli, horbit, hfiber]
  unfold averagedHermitianPauliSecondMoment
  rw [hsum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hcoeff]

noncomputable def registerSwapTwo (K : ℕ) :
    Matrix (DoubleIndex (PauliBinaryWord K))
      (DoubleIndex (PauliBinaryWord K)) ℂ :=
  fun x y ↦ if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0

theorem sum_hermitianPauliTensorTwo_eq_swap (K : ℕ) :
    (∑ p : PauliLabel K, hermitianPauliTensorTwo K p p) =
      ((2 : ℂ) ^ K) • registerSwapTwo K := by
  classical
  ext x y
  have hsumapply :
      ((∑ p : PauliLabel K, hermitianPauliTensorTwo K p p) x y) =
        ∑ p : PauliLabel K, (hermitianPauliTensorTwo K p p) x y := by
    exact Matrix.sum_apply x y Finset.univ
      (fun p : PauliLabel K ↦ hermitianPauliTensorTwo K p p)
  rw [hsumapply, Matrix.smul_apply]
  change (∑ p : PauliLabel K,
      hermitianBinaryPauliMatrix K p x.1 y.1 *
        hermitianBinaryPauliMatrix K p x.2 y.2) =
    ((2 : ℂ) ^ K) *
      (if x.1 = y.2 ∧ x.2 = y.1 then 1 else 0)
  rw [hermitianBinaryPauli_completeness]
  simp [eq_comm]

theorem hermitianPauliTensorTwo_zero_zero (K : ℕ) :
    hermitianPauliTensorTwo K 0 0 = 1 := by
  classical
  ext x y
  simp [hermitianPauliTensorTwo, hermitianBinaryPauliMatrix_zero,
    matrixTensorTwo, Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [h1, h2] <;> aesop

theorem sum_nonidentity_hermitianPauliTensorTwo (K : ℕ) :
    (∑ R : NonidentityPauliLabel K,
      hermitianPauliTensorTwo K R.1 R.1) =
        ((2 : ℂ) ^ K) • registerSwapTwo K - 1 := by
  have hsplit := Fintype.sum_eq_add_sum_subtype_ne
    (fun p : PauliLabel K ↦ hermitianPauliTensorTwo K p p) 0
  rw [sum_hermitianPauliTensorTwo_eq_swap,
    hermitianPauliTensorTwo_zero_zero] at hsplit
  apply eq_sub_of_add_eq
  simpa [add_comm] using hsplit.symm

theorem averagedHermitianPauliSecondMoment_same_eq_swap
    (K : ℕ) (Q : NonidentityPauliLabel K) :
    averagedHermitianPauliSecondMoment K Q.1 Q.1 =
      ((Fintype.card (NonidentityPauliLabel K) : ℂ)⁻¹) •
        (((2 : ℂ) ^ K) • registerSwapTwo K - 1) := by
  rw [averagedHermitianPauliSecondMoment_same_eq_nonidentity_average,
    sum_nonidentity_hermitianPauliTensorTwo]

theorem averagedHermitianPauliSecondMoment_zero_zero (K : ℕ) :
    averagedHermitianPauliSecondMoment K 0 0 = 1 := by
  classical
  unfold averagedHermitianPauliSecondMoment
  have hpoint : ∀ e : PauliCosetCliffordEnsemble K,
      conjugatedHermitianPauliTensorTwo K e 0 0 = 1 := by
    intro e
    rw [conjugatedHermitianPauliTensorTwo_same_eq]
    simp [hermitianPauliTensorTwo_zero_zero]
  simp_rw [hpoint]
  have hcard : (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (PauliCosetCliffordEnsemble K) ≠ 0)
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  rw [inv_mul_cancel₀ hcard, one_smul]

end TomographyOracleCore
