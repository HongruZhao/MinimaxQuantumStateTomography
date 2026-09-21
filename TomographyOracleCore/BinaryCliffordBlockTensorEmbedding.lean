import TomographyOracleCore.BinaryCliffordPauliCosetEnsemble
import TomographyOracleCore.BinarySymplecticBlockChannel

namespace TomographyOracleCore

open scoped BigOperators
noncomputable section

/-- Reindex a global binary computational-basis word as consecutive blocks. -/
noncomputable def binaryWordBlockEquiv (m K : ℕ) :
    PauliBinaryWord (m * K) ≃ (Fin m → PauliBinaryWord K) where
  toFun x j i := x (finProdFinEquiv (j, i))
  invFun X a :=
    let ji := finProdFinEquiv.symm a
    X ji.1 ji.2
  left_inv x := by
    funext a
    exact congrArg x (by
      simpa [finProdFinEquiv_symm_apply] using
        (finProdFinEquiv.apply_symm_apply a))
  right_inv X := by
    funext j i
    simp

@[simp] theorem binaryWordBlockEquiv_apply
    (m K : ℕ) (x : PauliBinaryWord (m * K))
    (j : Fin m) (i : Fin K) :
    binaryWordBlockEquiv m K x j i = x (finProdFinEquiv (j, i)) := rfl

@[simp] theorem binaryWordBlockEquiv_add
    (m K : ℕ) (x y : PauliBinaryWord (m * K)) (j : Fin m) :
    binaryWordBlockEquiv m K (x + y) j =
      binaryWordBlockEquiv m K x j + binaryWordBlockEquiv m K y j := rfl

@[simp] theorem binaryWordBlockEquiv_zero
    (m K : ℕ) (j : Fin m) :
    binaryWordBlockEquiv m K (0 : PauliBinaryWord (m * K)) j = 0 := rfl

@[simp] theorem pauliLabelBlockEquiv_fst
    (m K : ℕ) (p : PauliLabel (m * K)) (j : Fin m) :
    (pauliLabelBlockEquiv m K p j).1 =
      binaryWordBlockEquiv m K p.1 j := rfl

@[simp] theorem pauliLabelBlockEquiv_snd
    (m K : ℕ) (p : PauliLabel (m * K)) (j : Fin m) :
    (pauliLabelBlockEquiv m K p j).2 =
      binaryWordBlockEquiv m K p.2 j := rfl

theorem binarySign_sum_finset {ι : Type*}
    (s : Finset ι) (f : ι → ZMod 2) :
    binarySign (∑ i ∈ s, f i) = ∏ i ∈ s, binarySign (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [binarySign_add, ih]

theorem binarySign_fintype_sum {ι : Type*} [Fintype ι]
    (f : ι → ZMod 2) :
    binarySign (∑ i, f i) = ∏ i, binarySign (f i) := by
  simpa using binarySign_sum_finset Finset.univ f

/-- A global binary character factors over consecutive blocks. -/
theorem binaryWordCharacter_block_factorization
    (m K : ℕ) (x y : PauliBinaryWord (m * K)) :
    binaryWordCharacter (m * K) x y =
      ∏ j : Fin m,
        binaryWordCharacter K
          (binaryWordBlockEquiv m K x j)
          (binaryWordBlockEquiv m K y j) := by
  unfold binaryWordCharacter binaryDotProduct
  rw [show (∑ i : Fin (m * K), x i * y i) =
      ∑ ji : Fin m × Fin K,
        x (finProdFinEquiv ji) * y (finProdFinEquiv ji) by
      apply Fintype.sum_equiv finProdFinEquiv.symm
      intro i
      rw [finProdFinEquiv.apply_symm_apply]]
  rw [Fintype.sum_prod_type, binarySign_fintype_sum]
  apply Finset.prod_congr rfl
  intro j hj
  rfl

/-- Tensor product of one local matrix on each consecutive block, written
entrywise on binary computational-basis words. -/
noncomputable def blockTensorMatrix
    (m K : ℕ)
    (A : Fin m → Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    Matrix (PauliBinaryWord (m * K)) (PauliBinaryWord (m * K)) ℂ :=
  fun x y ↦ ∏ j : Fin m,
    A j (binaryWordBlockEquiv m K x j) (binaryWordBlockEquiv m K y j)

/-- A global binary Pauli is the tensor product of its consecutive-block
Paulis. -/
theorem binaryPauliMatrix_eq_blockTensorMatrix
    (m K : ℕ) (p : PauliLabel (m * K)) :
    binaryPauliMatrix (m * K) p =
      blockTensorMatrix m K (fun j ↦
        binaryPauliMatrix K (pauliLabelBlockEquiv m K p j)) := by
  classical
  ext a b
  simp only [binaryPauliMatrix, blockTensorMatrix]
  by_cases hab : a = b + p.1
  · rw [if_pos hab]
    have hblocks : ∀ j : Fin m,
        binaryWordBlockEquiv m K a j =
          binaryWordBlockEquiv m K b j +
            (pauliLabelBlockEquiv m K p j).1 := by
      intro j
      rw [hab]
      rfl
    simp_rw [if_pos (hblocks _)]
    have hchar := congrArg (fun t : ℝ ↦ (t : ℂ))
      (binaryWordCharacter_block_factorization m K p.2 b)
    push_cast at hchar
    simpa using hchar
  · rw [if_neg hab]
    have hblock : ∃ j : Fin m,
        binaryWordBlockEquiv m K a j ≠
          binaryWordBlockEquiv m K b j +
            (pauliLabelBlockEquiv m K p j).1 := by
      by_contra h
      push_neg at h
      apply hab
      apply (binaryWordBlockEquiv m K).injective
      funext j
      exact h j
    obtain ⟨j, hj⟩ := hblock
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    have hj' : binaryWordBlockEquiv m K a j ≠
        binaryWordBlockEquiv m K b j + binaryWordBlockEquiv m K p.1 j := by
      simpa using hj
    simp [hj']

@[simp] theorem blockTensorMatrix_one (m K : ℕ) :
    blockTensorMatrix m K (fun _ ↦ 1) = 1 := by
  classical
  ext x y
  simp only [blockTensorMatrix, Matrix.one_apply]
  by_cases hxy : x = y
  · subst y
    simp
  · have hblock : ∃ j : Fin m,
        binaryWordBlockEquiv m K x j ≠ binaryWordBlockEquiv m K y j := by
      by_contra h
      push_neg at h
      apply hxy
      exact (binaryWordBlockEquiv m K).injective (funext h)
    obtain ⟨j, hj⟩ := hblock
    rw [if_neg hxy]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

theorem blockTensorMatrix_conjTranspose
    (m K : ℕ)
    (A : Fin m → Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    (blockTensorMatrix m K A).conjTranspose =
      blockTensorMatrix m K (fun j ↦ (A j).conjTranspose) := by
  classical
  ext x y
  simp [blockTensorMatrix, Matrix.conjTranspose_apply, map_prod]

theorem blockTensorMatrix_mul
    (m K : ℕ)
    (A B : Fin m → Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    blockTensorMatrix m K (fun j ↦ A j * B j) =
      blockTensorMatrix m K A * blockTensorMatrix m K B := by
  classical
  ext x y
  simp only [blockTensorMatrix, Matrix.mul_apply]
  symm
  calc
    (∑ z : PauliBinaryWord (m * K),
        (∏ j : Fin m,
            A j (binaryWordBlockEquiv m K x j)
              (binaryWordBlockEquiv m K z j)) *
          ∏ j : Fin m,
            B j (binaryWordBlockEquiv m K z j)
              (binaryWordBlockEquiv m K y j)) =
      ∑ Z : Fin m → PauliBinaryWord K,
        ∏ j : Fin m,
          A j (binaryWordBlockEquiv m K x j) (Z j) *
            B j (Z j) (binaryWordBlockEquiv m K y j) := by
        apply Fintype.sum_equiv (binaryWordBlockEquiv m K)
        intro z
        rw [← Finset.prod_mul_distrib]
    _ = ∏ j : Fin m,
        ∑ z : PauliBinaryWord K,
          A j (binaryWordBlockEquiv m K x j) z *
            B j z (binaryWordBlockEquiv m K y j) := by
      rw [Fintype.prod_sum]
    _ = ∏ j : Fin m,
        (A j * B j) (binaryWordBlockEquiv m K x j)
          (binaryWordBlockEquiv m K y j) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [Matrix.mul_apply]

theorem blockTensorMatrix_smul
    (m K : ℕ) (c : Fin m → ℂ)
    (A : Fin m → Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) :
    blockTensorMatrix m K (fun j ↦ c j • A j) =
      (∏ j : Fin m, c j) • blockTensorMatrix m K A := by
  classical
  ext x y
  simp only [blockTensorMatrix, Matrix.smul_apply, smul_eq_mul,
    ← Finset.prod_mul_distrib]

/-- Consecutive tensor product of actual local unitaries. -/
noncomputable def blockTensorUnitary
    (m K : ℕ)
    (U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ := by
  refine ⟨blockTensorMatrix m K (fun j ↦ (U j).1), ?_⟩
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    blockTensorMatrix_conjTranspose, ← blockTensorMatrix_mul]
  have hlocal : (fun j : Fin m ↦ (U j).1 * (U j).1.conjTranspose) =
      fun _ ↦ (1 : Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) := by
    funext j
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp (U j).2)
  rw [hlocal, blockTensorMatrix_one]

@[simp] theorem blockTensorUnitary_coe
    (m K : ℕ)
    (U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ) :
    (blockTensorUnitary m K U).1 =
      blockTensorMatrix m K (fun j ↦ (U j).1) := rfl

/-- Blockwise action of local generated Clifford labels on a global Pauli. -/
noncomputable def blockPauliAction
    (m K : ℕ) (g : Fin m → binaryTransvectionGroup K)
    (p : PauliLabel (m * K)) : PauliLabel (m * K) :=
  (pauliLabelBlockEquiv m K).symm
    (fun j ↦ (g j).1.1 (pauliLabelBlockEquiv m K p j))

@[simp] theorem pauliLabelBlockEquiv_blockPauliAction
    (m K : ℕ) (g : Fin m → binaryTransvectionGroup K)
    (p : PauliLabel (m * K)) (j : Fin m) :
    pauliLabelBlockEquiv m K (blockPauliAction m K g p) j =
      (g j).1.1 (pauliLabelBlockEquiv m K p j) := by
  simp [blockPauliAction]

/-- Tensoring specified local Pauli lifts gives a literal global Pauli lift,
with the product of the local nonzero phases. -/
theorem blockTensorUnitary_conjugates_binaryPauli
    (m K : ℕ)
    (g : Fin m → binaryTransvectionGroup K)
    (U : Fin m → Matrix.unitaryGroup (PauliBinaryWord K) ℂ)
    (hU : ∀ j, IsUnitaryPauliLift K (g j).1 (U j))
    (p : PauliLabel (m * K)) :
    ∃ phase : ℂ, phase ≠ 0 ∧
      (((blockTensorUnitary m K U).1 * binaryPauliMatrix (m * K) p) *
          (blockTensorUnitary m K U).1.conjTranspose) =
        phase • binaryPauliMatrix (m * K) (blockPauliAction m K g p) := by
  classical
  choose phase hphase hconj using
    fun j : Fin m ↦ hU j (pauliLabelBlockEquiv m K p j)
  refine ⟨∏ j : Fin m, phase j, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr (by
      intro j hj
      exact hphase j)
  · rw [blockTensorUnitary_coe,
      binaryPauliMatrix_eq_blockTensorMatrix,
      blockTensorMatrix_conjTranspose,
      ← blockTensorMatrix_mul, ← blockTensorMatrix_mul]
    simp_rw [hconj]
    rw [blockTensorMatrix_smul,
      binaryPauliMatrix_eq_blockTensorMatrix]
    apply congrArg (fun M ↦ (∏ j : Fin m, phase j) • M)
    apply congrArg (blockTensorMatrix m K)
    funext j
    rw [pauliLabelBlockEquiv_blockPauliAction]

/-- Consecutive block tensor of local Pauli-coset Clifford unitaries. -/
noncomputable def blockPauliCosetCliffordUnitary
    (m K : ℕ) (e : Fin m → PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ :=
  blockTensorUnitary m K (fun j ↦ pauliCosetCliffordUnitary K (e j))

/-- The concrete independent Pauli-coset block unitary implements the
blockwise generated symplectic action on every global Pauli. -/
theorem blockPauliCosetCliffordUnitary_conjugates_binaryPauli
    (m K : ℕ) (e : Fin m → PauliCosetCliffordEnsemble K)
    (p : PauliLabel (m * K)) :
    ∃ phase : ℂ, phase ≠ 0 ∧
      (((blockPauliCosetCliffordUnitary m K e).1 *
          binaryPauliMatrix (m * K) p) *
          (blockPauliCosetCliffordUnitary m K e).1.conjTranspose) =
        phase • binaryPauliMatrix (m * K)
          (blockPauliAction m K (fun j ↦ (e j).2) p) := by
  exact blockTensorUnitary_conjugates_binaryPauli m K
    (fun j ↦ (e j).2)
    (fun j ↦ pauliCosetCliffordUnitary K (e j))
    (fun j ↦ pauliCosetCliffordUnitary_spec K (e j)) p

end
end TomographyOracleCore

