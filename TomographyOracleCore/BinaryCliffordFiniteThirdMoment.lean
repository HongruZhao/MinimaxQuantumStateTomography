import TomographyOracleCore.BinaryCliffordWebbPauliCancellation

namespace TomographyOracleCore

open scoped BigOperators

/-!
# Concrete finite-ensemble third moments

This module begins the matrix case analysis in Webb's Pauli-basis proof of
the Clifford third-design theorem.  It defines the literal tensor-cube
conjugation twirl of the finite Pauli-coset ensemble and proves the complete
Pauli-invariance cancellation case: every Pauli tensor whose three labels
have nonzero binary sum has exactly zero third moment.
-/

/-- Index set for a three-fold tensor product. -/
abbrev TripleIndex (ι : Type*) := ι × ι × ι

/-- Entrywise Kronecker product of three square matrices. -/
def matrixTensorThree {ι : Type*}
    (A B C : Matrix ι ι ℂ) :
    Matrix (TripleIndex ι) (TripleIndex ι) ℂ :=
  fun x y ↦ A x.1 y.1 * B x.2.1 y.2.1 * C x.2.2 y.2.2

/-- Three-fold tensor products preserve matrix multiplication. -/
theorem matrixTensorThree_mul {ι : Type*} [Fintype ι]
    (A₁ A₂ A₃ B₁ B₂ B₃ : Matrix ι ι ℂ) :
    matrixTensorThree (A₁ * B₁) (A₂ * B₂) (A₃ * B₃) =
      matrixTensorThree A₁ A₂ A₃ *
        matrixTensorThree B₁ B₂ B₃ := by
  ext x y
  simp only [matrixTensorThree, Matrix.mul_apply, Fintype.sum_prod_type]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Three-fold tensor products commute with conjugate transpose. -/
theorem matrixTensorThree_conjTranspose {ι : Type*} [Fintype ι]
    (A B C : Matrix ι ι ℂ) :
    matrixTensorThree A.conjTranspose B.conjTranspose C.conjTranspose =
      (matrixTensorThree A B C).conjTranspose := by
  ext x y
  simp [matrixTensorThree, Matrix.conjTranspose_apply]

/-- Scalar factors multiply across a three-fold tensor product. -/
theorem matrixTensorThree_smul {ι : Type*}
    (a b c : ℂ) (A B C : Matrix ι ι ℂ) :
    matrixTensorThree (a • A) (b • B) (c • C) =
      (a * b * c) • matrixTensorThree A B C := by
  ext x y
  simp [matrixTensorThree]
  ring

/-- Three Pauli matrices as one operator on the tensor-cube space. -/
noncomputable def binaryPauliTensorThree (K : ℕ)
    (p q r : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  matrixTensorThree (binaryPauliMatrix K p)
    (binaryPauliMatrix K q) (binaryPauliMatrix K r)

/-- Tensor cube of one concrete Pauli-coset Clifford unitary. -/
noncomputable def pauliCosetCliffordTensorCube
    (K : ℕ) (e : PauliCosetCliffordEnsemble K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  matrixTensorThree (pauliCosetCliffordUnitary K e).1
    (pauliCosetCliffordUnitary K e).1
    (pauliCosetCliffordUnitary K e).1

/-- Literal tensor-cube conjugation of three arbitrary local operators. -/
noncomputable def conjugatedMatrixTensorThree
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A B C : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  (pauliCosetCliffordTensorCube K e * matrixTensorThree A B C) *
    (pauliCosetCliffordTensorCube K e).conjTranspose

/-- Tensor-cube conjugation factors into three ordinary conjugations. -/
theorem conjugatedMatrixTensorThree_eq
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (A B C : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    conjugatedMatrixTensorThree K e A B C =
      matrixTensorThree
        (((pauliCosetCliffordUnitary K e).1 * A) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose)
        (((pauliCosetCliffordUnitary K e).1 * B) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose)
        (((pauliCosetCliffordUnitary K e).1 * C) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose) := by
  unfold conjugatedMatrixTensorThree pauliCosetCliffordTensorCube
  rw [← matrixTensorThree_conjTranspose]
  rw [← matrixTensorThree_mul, ← matrixTensorThree_mul]

/-- Literal three-fold conjugation of a Pauli tensor by one ensemble unitary. -/
noncomputable def conjugatedBinaryPauliTensorThree
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (p q r : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  (pauliCosetCliffordTensorCube K e * binaryPauliTensorThree K p q r) *
    (pauliCosetCliffordTensorCube K e).conjTranspose

/-- Tensor-cube conjugation factors into the three individual conjugations. -/
theorem conjugatedBinaryPauliTensorThree_eq
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (p q r : PauliLabel K) :
    conjugatedBinaryPauliTensorThree K e p q r =
      matrixTensorThree
        (((pauliCosetCliffordUnitary K e).1 * binaryPauliMatrix K p) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose)
        (((pauliCosetCliffordUnitary K e).1 * binaryPauliMatrix K q) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose)
        (((pauliCosetCliffordUnitary K e).1 * binaryPauliMatrix K r) *
          (pauliCosetCliffordUnitary K e).1.conjTranspose) := by
  unfold conjugatedBinaryPauliTensorThree pauliCosetCliffordTensorCube
    binaryPauliTensorThree
  rw [← matrixTensorThree_conjTranspose]
  rw [← matrixTensorThree_mul, ← matrixTensorThree_mul]

/-- Ordinary unitary conjugation preserves multiplication. -/
theorem unitaryConjugation_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (A B : Matrix ι ι ℂ) :
    (U.1 * (A * B)) * U.1.conjTranspose =
      ((U.1 * A) * U.1.conjTranspose) *
        ((U.1 * B) * U.1.conjTranspose) := by
  have hUleft : U.1.conjTranspose * U.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp U.2)
  calc
    (U.1 * (A * B)) * U.1.conjTranspose =
        (U.1 * A) * (U.1.conjTranspose * U.1) *
          (B * U.1.conjTranspose) := by
      rw [hUleft]
      noncomm_ring
    _ = ((U.1 * A) * U.1.conjTranspose) *
          ((U.1 * B) * U.1.conjTranspose) := by noncomm_ring

/-- The Pauli coordinate in the coset completion contributes exactly the
binary commutation character to conjugation. -/
theorem pauliCosetCliffordUnitary_conjugates_binaryPauli
    (K : ℕ) (a : PauliLabel K) (g : binaryTransvectionGroup K)
    (p : PauliLabel K) (phase : ℂ)
    (hphase :
      (((binaryTransvectionUnitaryLift K g).1 * binaryPauliMatrix K p) *
          (binaryTransvectionUnitaryLift K g).1.conjTranspose) =
        phase • binaryPauliMatrix K (g.1.1 p)) :
    (((pauliCosetCliffordUnitary K (a, g)).1 *
        binaryPauliMatrix K p) *
      (pauliCosetCliffordUnitary K (a, g)).1.conjTranspose) =
      (phase * (pauliCharacter K a (g.1.1 p) : ℂ)) •
        binaryPauliMatrix K (g.1.1 p) := by
  change ((((hermitianBinaryPauliMatrix K a *
      (binaryTransvectionUnitaryLift K g).1) *
        binaryPauliMatrix K p) *
      (hermitianBinaryPauliMatrix K a *
        (binaryTransvectionUnitaryLift K g).1).conjTranspose) = _)
  rw [Matrix.conjTranspose_mul,
    hermitianBinaryPauliMatrix_conjTranspose]
  calc
    (((hermitianBinaryPauliMatrix K a *
          (binaryTransvectionUnitaryLift K g).1) *
        binaryPauliMatrix K p) *
      ((binaryTransvectionUnitaryLift K g).1.conjTranspose *
        hermitianBinaryPauliMatrix K a)) =
        (hermitianBinaryPauliMatrix K a *
          ((((binaryTransvectionUnitaryLift K g).1 *
            binaryPauliMatrix K p) *
            (binaryTransvectionUnitaryLift K g).1.conjTranspose))) *
          hermitianBinaryPauliMatrix K a := by noncomm_ring
    _ = (hermitianBinaryPauliMatrix K a *
          (phase • binaryPauliMatrix K (g.1.1 p))) *
          hermitianBinaryPauliMatrix K a := by rw [hphase]
    _ = phase •
          ((hermitianBinaryPauliMatrix K a *
            binaryPauliMatrix K (g.1.1 p)) *
            hermitianBinaryPauliMatrix K a) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = phase • ((pauliCharacter K a (g.1.1 p) : ℂ) •
          binaryPauliMatrix K (g.1.1 p)) := by
      rw [hermitianBinaryPauliMatrix_sandwich]
    _ = (phase * (pauliCharacter K a (g.1.1 p) : ℂ)) •
          binaryPauliMatrix K (g.1.1 p) := by rw [smul_smul]

/-- A scalar appearing between two Hermitian involutions under unitary
conjugation must square to one. -/
theorem conjugation_phase_sq_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (U : Matrix.unitaryGroup ι ℂ)
    (H H' : Matrix ι ι ℂ) (phase : ℂ)
    (hHsq : H * H = 1) (hH'sq : H' * H' = 1)
    (hconj : (U.1 * H) * U.1.conjTranspose = phase • H') :
    phase * phase = 1 := by
  have hUleft : U.1.conjTranspose * U.1 = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp U.2)
  have hUright : U.1 * U.1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.2)
  have hleft :
      (((U.1 * H) * U.1.conjTranspose) *
        ((U.1 * H) * U.1.conjTranspose)) = 1 := by
    calc
      (((U.1 * H) * U.1.conjTranspose) *
          ((U.1 * H) * U.1.conjTranspose)) =
          (U.1 * H) * (U.1.conjTranspose * U.1) *
            (H * U.1.conjTranspose) := by noncomm_ring
      _ = (U.1 * (H * H)) * U.1.conjTranspose := by
        rw [hUleft]
        simp only [mul_one]
        noncomm_ring
      _ = U.1 * U.1.conjTranspose := by rw [hHsq, mul_one]
      _ = 1 := hUright
  have hscalar :
      (phase * phase) • (1 : Matrix ι ι ℂ) = 1 := by
    have hprod : (phase • H') * (phase • H') = 1 := by
      rw [← hconj]
      exact hleft
    calc
      (phase * phase) • (1 : Matrix ι ι ℂ) =
          (phase * phase) • (H' * H') := by rw [hH'sq]
      _ = phase • (phase • (H' * H')) := by rw [smul_smul]
      _ = (phase • H') * (phase • H') := by
        rw [Matrix.smul_mul, Matrix.mul_smul]
      _ = 1 := hprod
  exact smul_left_injective ℂ
    (one_ne_zero : (1 : Matrix ι ι ℂ) ≠ 0) (by simpa using hscalar)

/-- A unitary Pauli lift sends every Hermitian Pauli to the Hermitian Pauli
at the transported label with a sign whose square is one. -/
theorem IsUnitaryPauliLift.conjugates_hermitian
    (K : ℕ) {g : binarySymplecticGroup K}
    {U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ}
    (hU : IsUnitaryPauliLift K g U) (p : PauliLabel K) :
    ∃ phase : ℂ, phase ≠ 0 ∧ phase * phase = 1 ∧
      ((U.1 * hermitianBinaryPauliMatrix K p) * U.1.conjTranspose) =
        phase • hermitianBinaryPauliMatrix K (g.1 p) := by
  obtain ⟨c, hc, hconj⟩ := hU p
  let phase : ℂ := hermitianPauliPhase K p * c *
    (hermitianPauliPhase K (g.1 p))⁻¹
  have hphase : phase ≠ 0 := by
    unfold phase
    exact mul_ne_zero
      (mul_ne_zero (hermitianPauliPhase_ne_zero K p) hc)
      (inv_ne_zero (hermitianPauliPhase_ne_zero K (g.1 p)))
  have hherm :
      ((U.1 * hermitianBinaryPauliMatrix K p) * U.1.conjTranspose) =
        phase • hermitianBinaryPauliMatrix K (g.1 p) := by
    unfold hermitianBinaryPauliMatrix phase
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj, smul_smul, smul_smul]
    apply congrArg (fun z : ℂ ↦ z • binaryPauliMatrix K (g.1 p))
    field_simp [hermitianPauliPhase_ne_zero]
  refine ⟨phase, hphase, ?_, hherm⟩
  exact conjugation_phase_sq_eq_one U
    (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K (g.1 p)) phase
    (hermitianBinaryPauliMatrix_sq K p)
    (hermitianBinaryPauliMatrix_sq K (g.1 p)) hherm

/-- Webb's Case-2 Pauli tensor, written using the actual product in its
third register. -/
noncomputable def hermitianPauliProductTensorThree
    (K : ℕ) (p q : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  matrixTensorThree
    (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)
    (hermitianBinaryPauliMatrix K p *
      hermitianBinaryPauliMatrix K q)

/-- Literal tensor-cube conjugation of Webb's Case-2 Pauli tensor. -/
noncomputable def conjugatedHermitianPauliProductTensorThree
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (p q : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  conjugatedMatrixTensorThree K e
    (hermitianBinaryPauliMatrix K p)
    (hermitianBinaryPauliMatrix K q)
    (hermitianBinaryPauliMatrix K p *
      hermitianBinaryPauliMatrix K q)

/-- Pointwise Case-2 phase cancellation: all physical Clifford signs occur
twice, so the conjugated tensor depends only on the transported label pair. -/
theorem conjugatedHermitianPauliProductTensorThree_eq
    (K : ℕ) (e : PauliCosetCliffordEnsemble K)
    (p q : PauliLabel K) :
    conjugatedHermitianPauliProductTensorThree K e p q =
      hermitianPauliProductTensorThree K
        (e.2.1.1 p) (e.2.1.1 q) := by
  obtain ⟨cp, hcp0, hcp2, hp⟩ :=
    (pauliCosetCliffordUnitary_spec K e).conjugates_hermitian K p
  obtain ⟨cq, hcq0, hcq2, hq⟩ :=
    (pauliCosetCliffordUnitary_spec K e).conjugates_hermitian K q
  have hcoef : cp * cq * (cp * cq) = 1 := by
    calc
      cp * cq * (cp * cq) = (cp * cp) * (cq * cq) := by ring
      _ = 1 := by rw [hcp2, hcq2, one_mul]
  unfold conjugatedHermitianPauliProductTensorThree
    hermitianPauliProductTensorThree
  rw [conjugatedMatrixTensorThree_eq,
    unitaryConjugation_mul, hp, hq]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    matrixTensorThree_smul, hcoef, one_smul]

/-- A finite transitive group action averages every function uniformly over
the target type, in exact unnormalized fiber-count form. -/
theorem uniform_action_sum
    {G Ω V : Type*} [Group G] [Fintype G] [Fintype Ω]
    [DecidableEq Ω] [MulAction G Ω]
    [MulAction.IsPretransitive G Ω] [AddCommMonoid V]
    (x : Ω) (f : Ω → V) :
    (∑ g : G, f (g • x)) =
      Fintype.card (ActionFiber (G := G) x x) •
        (∑ y : Ω, f y) := by
  calc
    (∑ g : G, f (g • x)) =
        ∑ z : Σ y : Ω, ActionFiber (G := G) x y, f z.1 :=
      Equiv.sum_comp (actionEquivSigmaFibers (G := G) x)
        (fun z : Σ y : Ω, ActionFiber (G := G) x y ↦ f z.1)
    _ = ∑ y : Ω, ∑ _h : ActionFiber (G := G) x y, f y :=
      Fintype.sum_sigma _
    _ = ∑ y : Ω,
        Fintype.card (ActionFiber (G := G) x y) • f y := by
      apply Fintype.sum_congr
      intro y
      simp
    _ = ∑ y : Ω,
        Fintype.card (ActionFiber (G := G) x x) • f y := by
      apply Fintype.sum_congr
      intro y
      rw [actionFiber_card_eq x y x]
    _ = Fintype.card (ActionFiber (G := G) x x) •
          (∑ y : Ω, f y) := by rw [Finset.smul_sum]

/-- Uniform physical Case-2 third moment over the Pauli-coset ensemble. -/
noncomputable def averagedHermitianPauliProductThirdMoment
    (K : ℕ) (p q : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
    ∑ e : PauliCosetCliffordEnsemble K,
      conjugatedHermitianPauliProductTensorThree K e p q

/-- Exact normalized Case-2 identity: for every ordered distinct
nonidentity input pair, the concrete physical third moment is the uniform
matrix sum over its complete fixed-commutation pair class. -/
theorem averagedHermitianPauliProductThirdMoment_eq_pairClass
    (K : ℕ) {c : ZMod 2} (x : PauliPairClass K c) :
    averagedHermitianPauliProductThirdMoment K x.1.1 x.1.2 =
      ((Fintype.card (PauliPairClass K c) : ℂ)⁻¹) •
        ∑ y : PauliPairClass K c,
          hermitianPauliProductTensorThree K y.1.1 y.1.2 := by
  classical
  let f : PauliPairClass K c →
      Matrix (TripleIndex (PauliBinaryWord K))
        (TripleIndex (PauliBinaryWord K)) ℂ :=
    fun y ↦ hermitianPauliProductTensorThree K y.1.1 y.1.2
  have hgroup :
      (∑ g : binaryTransvectionGroup K,
        hermitianPauliProductTensorThree K
          (g.1.1 x.1.1) (g.1.1 x.1.2)) =
        Fintype.card
            (ActionFiber (G := binaryTransvectionGroup K) x x) •
          (∑ y : PauliPairClass K c,
            hermitianPauliProductTensorThree K y.1.1 y.1.2) := by
    change (∑ g : binaryTransvectionGroup K, f (g • x)) =
      Fintype.card
          (ActionFiber (G := binaryTransvectionGroup K) x x) •
        (∑ y : PauliPairClass K c, f y)
    exact uniform_action_sum
      (G := binaryTransvectionGroup K) (Ω := PauliPairClass K c) x f
  have hsum :
      (∑ e : PauliCosetCliffordEnsemble K,
        conjugatedHermitianPauliProductTensorThree K e x.1.1 x.1.2) =
        (Fintype.card (PauliLabel K) *
          Fintype.card
            (ActionFiber (G := binaryTransvectionGroup K) x x)) •
          (∑ y : PauliPairClass K c,
            hermitianPauliProductTensorThree K y.1.1 y.1.2) := by
    rw [Fintype.sum_prod_type]
    simp_rw [conjugatedHermitianPauliProductTensorThree_eq]
    rw [hgroup]
    simp
    simp only [mul_assoc]
  have hpauli : (Fintype.card (PauliLabel K) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card (PauliLabel K) ≠ 0)
  have hpair : (Fintype.card (PauliPairClass K c) : ℂ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_pos_iff.mpr ⟨x⟩).ne'
  have hfiber :
      (Fintype.card
        (ActionFiber (G := binaryTransvectionGroup K) x x) : ℂ) ≠ 0 := by
    letI : Nonempty
        (ActionFiber (G := binaryTransvectionGroup K) x x) :=
      ⟨⟨1, one_smul (binaryTransvectionGroup K) x⟩⟩
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card
        (ActionFiber (G := binaryTransvectionGroup K) x x) ≠ 0)
  have hcardEnsemble :
      Fintype.card (PauliCosetCliffordEnsemble K) =
        Fintype.card (PauliLabel K) *
          (Fintype.card (PauliPairClass K c) *
            Fintype.card
              (ActionFiber (G := binaryTransvectionGroup K) x x)) := by
    rw [Fintype.card_prod,
      action_card (G := binaryTransvectionGroup K)
        (Ω := PauliPairClass K c) x]
  have hcoeff :
      (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹ *
          (Fintype.card (PauliLabel K) *
            Fintype.card
              (ActionFiber (G := binaryTransvectionGroup K) x x) : ℕ) =
        (Fintype.card (PauliPairClass K c) : ℂ)⁻¹ := by
    rw [hcardEnsemble]
    push_cast
    field_simp [hpauli, hpair, hfiber]
  unfold averagedHermitianPauliProductThirdMoment
  rw [hsum, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, hcoeff]

/-- Chosen scalar in the conjugation action of the generated-group lift on
one unphased Pauli basis matrix. -/
noncomputable def binaryTransvectionPauliPhase
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) : ℂ :=
  Classical.choose (binaryTransvectionUnitaryLift_spec K g p)

theorem binaryTransvectionPauliPhase_ne_zero
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) :
    binaryTransvectionPauliPhase K g p ≠ 0 :=
  (Classical.choose_spec (binaryTransvectionUnitaryLift_spec K g p)).1

theorem binaryTransvectionPauliPhase_spec
    (K : ℕ) (g : binaryTransvectionGroup K) (p : PauliLabel K) :
    (((binaryTransvectionUnitaryLift K g).1 * binaryPauliMatrix K p) *
        (binaryTransvectionUnitaryLift K g).1.conjTranspose) =
      binaryTransvectionPauliPhase K g p •
        binaryPauliMatrix K (g.1.1 p) :=
  (Classical.choose_spec (binaryTransvectionUnitaryLift_spec K g p)).2

/-- The symplectic-coordinate tensor factor left after extracting the three
free-Pauli commutation characters. -/
noncomputable def baseLiftedBinaryPauliTensorThree
    (K : ℕ) (g : binaryTransvectionGroup K)
    (p q r : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  (binaryTransvectionPauliPhase K g p *
      binaryTransvectionPauliPhase K g q *
      binaryTransvectionPauliPhase K g r) •
    binaryPauliTensorThree K (g.1.1 p) (g.1.1 q) (g.1.1 r)

/-- Pointwise extraction of Webb's three Pauli commutation characters from
the literal physical tensor-cube conjugation. -/
theorem conjugatedBinaryPauliTensorThree_eq_tripleCharacter
    (K : ℕ) (a : PauliLabel K) (g : binaryTransvectionGroup K)
    (p q r : PauliLabel K) :
    conjugatedBinaryPauliTensorThree K (a, g) p q r =
      complexPauliTripleCharacter K a
        (g.1.1 p) (g.1.1 q) (g.1.1 r) •
          baseLiftedBinaryPauliTensorThree K g p q r := by
  rw [conjugatedBinaryPauliTensorThree_eq,
    pauliCosetCliffordUnitary_conjugates_binaryPauli K a g p
      (binaryTransvectionPauliPhase K g p)
      (binaryTransvectionPauliPhase_spec K g p),
    pauliCosetCliffordUnitary_conjugates_binaryPauli K a g q
      (binaryTransvectionPauliPhase K g q)
      (binaryTransvectionPauliPhase_spec K g q),
    pauliCosetCliffordUnitary_conjugates_binaryPauli K a g r
      (binaryTransvectionPauliPhase K g r)
      (binaryTransvectionPauliPhase_spec K g r),
    matrixTensorThree_smul]
  unfold baseLiftedBinaryPauliTensorThree complexPauliTripleCharacter
    pauliTripleCharacter binaryPauliTensorThree
  rw [smul_smul]
  apply congrArg (fun z : ℂ ↦ z •
    matrixTensorThree (binaryPauliMatrix K (g.1.1 p))
      (binaryPauliMatrix K (g.1.1 q))
      (binaryPauliMatrix K (g.1.1 r)))
  push_cast
  ring

/-- Uniform finite Pauli-coset third conjugation moment. -/
noncomputable def averagedPauliCosetThirdMoment
    (K : ℕ) (p q r : PauliLabel K) :
    Matrix (TripleIndex (PauliBinaryWord K))
      (TripleIndex (PauliBinaryWord K)) ℂ :=
  ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
    ∑ e : PauliCosetCliffordEnsemble K,
      conjugatedBinaryPauliTensorThree K e p q r

/-- Complete physical Webb Case-3 matrix cancellation: if the three Pauli
labels have nonzero binary sum, their literal finite tensor-cube third
moment is exactly the zero matrix. -/
theorem averagedPauliCosetThirdMoment_eq_zero
    (K : ℕ) (p q r : PauliLabel K) (hsum : p + q + r ≠ 0) :
    averagedPauliCosetThirdMoment K p q r = 0 := by
  unfold averagedPauliCosetThirdMoment
  have hzero :
      (∑ e : PauliCosetCliffordEnsemble K,
        conjugatedBinaryPauliTensorThree K e p q r) = 0 := by
    simp_rw [show ∀ e : PauliCosetCliffordEnsemble K,
        conjugatedBinaryPauliTensorThree K e p q r =
          complexPauliTripleCharacter K e.1
            (e.2.1.1 p) (e.2.1.1 q) (e.2.1.1 r) •
              baseLiftedBinaryPauliTensorThree K e.2 p q r by
      intro e
      exact conjugatedBinaryPauliTensorThree_eq_tripleCharacter
        K e.1 e.2 p q r]
    exact sum_pauliCosetClifford_tripleCharacter_smul_eq_zero
      K p q r hsum (fun g ↦ baseLiftedBinaryPauliTensorThree K g p q r)
  rw [hzero, smul_zero]

end TomographyOracleCore
