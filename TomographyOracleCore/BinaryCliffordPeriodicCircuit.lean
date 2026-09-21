import TomographyOracleCore.BinaryCliffordBlockTensorEmbedding
import TomographyOracleCore.BinaryCliffordWebbHaarBridge
import Mathlib.GroupTheory.Perm.Fin

namespace TomographyOracleCore

open scoped BigOperators
noncomputable section

/-- Cyclic shift of `Fin N` by `s`, defined as the `s`th power of the full
cycle.  The empty register is fixed. -/
def cyclicQubitShift : (N : ℕ) → ℕ → Equiv.Perm (Fin N)
  | 0, _ => Equiv.refl _
  | N + 1, s => (Fin.cycleRange (Fin.last N)) ^ s

/-- Coordinate reindexing of binary words induced by a qubit permutation. -/
def permuteBinaryWord {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    PauliBinaryWord N ≃ PauliBinaryWord N where
  toFun x i := x (σ.symm i)
  invFun x i := x (σ i)
  left_inv x := by
    funext i
    simp
  right_inv x := by
    funext i
    simp

@[simp] theorem permuteBinaryWord_apply {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (x : PauliBinaryWord N) (i : Fin N) :
    permuteBinaryWord σ x i = x (σ.symm i) := rfl

@[simp] theorem permuteBinaryWord_symm_apply {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (x : PauliBinaryWord N) (i : Fin N) :
    (permuteBinaryWord σ).symm x i = x (σ i) := rfl

@[simp] theorem permuteBinaryWord_add {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (x y : PauliBinaryWord N) :
    permuteBinaryWord σ (x + y) =
      permuteBinaryWord σ x + permuteBinaryWord σ y := rfl

@[simp] theorem permuteBinaryWord_symm_add {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (x y : PauliBinaryWord N) :
    (permuteBinaryWord σ).symm (x + y) =
      (permuteBinaryWord σ).symm x + (permuteBinaryWord σ).symm y := rfl

/-- Qubit permutations preserve the binary character. -/
theorem binaryWordCharacter_permuteBinaryWord {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (x y : PauliBinaryWord N) :
    binaryWordCharacter N (permuteBinaryWord σ x)
        (permuteBinaryWord σ y) = binaryWordCharacter N x y := by
  unfold binaryWordCharacter binaryDotProduct
  congr 1
  symm
  apply Fintype.sum_equiv σ
  intro i
  simp

/-- Coordinate reindexing of both halves of a Pauli label. -/
def permutePauliLabel {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    PauliLabel N ≃ PauliLabel N :=
  Equiv.prodCongr (permuteBinaryWord σ) (permuteBinaryWord σ)

@[simp] theorem permutePauliLabel_fst {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (p : PauliLabel N) :
    (permutePauliLabel σ p).1 = permuteBinaryWord σ p.1 := rfl

@[simp] theorem permutePauliLabel_snd {N : ℕ}
    (σ : Equiv.Perm (Fin N)) (p : PauliLabel N) :
    (permutePauliLabel σ p).2 = permuteBinaryWord σ p.2 := rfl

theorem permutationMatrix_conjTranspose
    {α : Type*} [Fintype α] [DecidableEq α] (σ : α ≃ α) :
    (permutationMatrix σ).conjTranspose = permutationMatrix σ.symm := by
  classical
  ext x y
  change star (if y = σ x then (1 : ℂ) else 0) =
    if x = σ.symm y then 1 else 0
  by_cases h : y = σ x
  · rw [if_pos h, star_one]
    rw [if_pos (by simpa using (congrArg σ.symm h).symm)]
  · rw [if_neg h, star_zero]
    rw [if_neg (by
      intro h'
      apply h
      simpa using (congrArg σ h').symm)]

theorem permutationMatrix_mem_unitaryGroup
    {α : Type*} [Fintype α] [DecidableEq α] (σ : α ≃ α) :
    permutationMatrix σ ∈ Matrix.unitaryGroup α ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    permutationMatrix_conjTranspose]
  ext x y
  rw [permutationMatrix_mul_apply]
  simp [permutationMatrix, Matrix.one_apply]

/-- Computational-basis permutation unitary induced by a qubit permutation. -/
def binaryWordPermutationUnitary {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    Matrix.unitaryGroup (PauliBinaryWord N) ℂ :=
  ⟨permutationMatrix (permuteBinaryWord σ),
    permutationMatrix_mem_unitaryGroup (permuteBinaryWord σ)⟩

/-- A computational-basis qubit permutation conjugates a Pauli by the same
coordinate permutation, with no phase. -/
theorem binaryWordPermutationUnitary_conjugates_binaryPauli
    {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : PauliLabel N) :
    (((binaryWordPermutationUnitary σ).1 * binaryPauliMatrix N p) *
        (binaryWordPermutationUnitary σ).1.conjTranspose) =
      binaryPauliMatrix N (permutePauliLabel σ p) := by
  classical
  ext x y
  rw [show (binaryWordPermutationUnitary σ).1 =
      permutationMatrix (permuteBinaryWord σ) by rfl,
    permutationMatrix_conjTranspose,
    mul_permutationMatrix_apply,
    permutationMatrix_mul_apply]
  simp only [binaryPauliMatrix]
  change (if (permuteBinaryWord σ).symm x =
        (permuteBinaryWord σ).symm y + p.1 then
      (binaryWordCharacter N p.2 ((permuteBinaryWord σ).symm y) : ℂ)
    else 0) =
    if x = y + permuteBinaryWord σ p.1 then
      (binaryWordCharacter N (permuteBinaryWord σ p.2) y : ℂ)
    else 0
  by_cases hxy : (permuteBinaryWord σ).symm x =
      (permuteBinaryWord σ).symm y + p.1
  · rw [if_pos hxy]
    have hxy' : x = y + permuteBinaryWord σ p.1 := by
      have h := congrArg (permuteBinaryWord σ) hxy
      simpa using h
    rw [if_pos hxy']
    have hchar := binaryWordCharacter_permuteBinaryWord σ p.2
      ((permuteBinaryWord σ).symm y)
    simpa using hchar.symm
  · rw [if_neg hxy]
    have hxy' : x ≠ y + permuteBinaryWord σ p.1 := by
      intro h
      apply hxy
      have h' := congrArg (permuteBinaryWord σ).symm h
      simpa using h'
    rw [if_neg hxy']

/-- The physical `s`-site cyclic shift on an `N`-qubit register. -/
def cyclicQubitShiftUnitary (N s : ℕ) :
    Matrix.unitaryGroup (PauliBinaryWord N) ℂ :=
  binaryWordPermutationUnitary (cyclicQubitShift N s)

/-- Composition rule for two concrete unitary Pauli conjugations. -/
theorem unitaryPauliConjugation_mul
    {N : ℕ}
    (U V : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (p q r : PauliLabel N) (c d : ℂ)
    (hV : (V.1 * binaryPauliMatrix N p) * V.1.conjTranspose =
      c • binaryPauliMatrix N q)
    (hU : (U.1 * binaryPauliMatrix N q) * U.1.conjTranspose =
      d • binaryPauliMatrix N r) :
    (((U * V).1 * binaryPauliMatrix N p) *
        (U * V).1.conjTranspose) =
      (c * d) • binaryPauliMatrix N r := by
  change (((U.1 * V.1) * binaryPauliMatrix N p) *
      (U.1 * V.1).conjTranspose) = _
  rw [Matrix.conjTranspose_mul]
  calc
    ((U.1 * V.1) * binaryPauliMatrix N p) *
        (V.1.conjTranspose * U.1.conjTranspose) =
      (U.1 * ((V.1 * binaryPauliMatrix N p) * V.1.conjTranspose)) *
        U.1.conjTranspose := by noncomm_ring
    _ = (U.1 * (c • binaryPauliMatrix N q)) * U.1.conjTranspose := by
      rw [hV]
    _ = c • ((U.1 * binaryPauliMatrix N q) * U.1.conjTranspose) := by
      rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = c • (d • binaryPauliMatrix N r) := by rw [hU]
    _ = (c * d) • binaryPauliMatrix N r := by rw [smul_smul]

/-- Pauli-label action of a block layer shifted by the qubit permutation
`σ`. -/
noncomputable def shiftedBlockPauliAction
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (g : Fin m → binaryTransvectionGroup K)
    (p : PauliLabel (m * K)) : PauliLabel (m * K) :=
  permutePauliLabel σ
    (blockPauliAction m K g (permutePauliLabel σ.symm p))

/-- Concrete shifted block layer obtained by conjugating the consecutive
block tensor with a qubit-permutation unitary. -/
noncomputable def shiftedBlockPauliCosetCliffordUnitary
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : Fin m → PauliCosetCliffordEnsemble K) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ :=
  binaryWordPermutationUnitary σ *
    (blockPauliCosetCliffordUnitary m K e *
      binaryWordPermutationUnitary σ.symm)

set_option maxHeartbeats 1200000 in
theorem shiftedBlockPauliCosetCliffordUnitary_conjugates_binaryPauli
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : Fin m → PauliCosetCliffordEnsemble K)
    (p : PauliLabel (m * K)) :
    ∃ phase : ℂ, phase ≠ 0 ∧
      (((shiftedBlockPauliCosetCliffordUnitary m K σ e).1 *
          binaryPauliMatrix (m * K) p) *
          (shiftedBlockPauliCosetCliffordUnitary m K σ e).1.conjTranspose) =
        phase • binaryPauliMatrix (m * K)
          (shiftedBlockPauliAction m K σ (fun j ↦ (e j).2) p) := by
  obtain ⟨phase, hphase, hblock⟩ :=
    blockPauliCosetCliffordUnitary_conjugates_binaryPauli m K e
      (permutePauliLabel σ.symm p)
  refine ⟨phase, hphase, ?_⟩
  have hright := binaryWordPermutationUnitary_conjugates_binaryPauli
    σ.symm p
  have hfirst := unitaryPauliConjugation_mul
    (blockPauliCosetCliffordUnitary m K e)
    (binaryWordPermutationUnitary σ.symm)
    p (permutePauliLabel σ.symm p)
    (blockPauliAction m K (fun j ↦ (e j).2)
      (permutePauliLabel σ.symm p)) 1 phase
      (by simpa using hright) hblock
  have hleft := binaryWordPermutationUnitary_conjugates_binaryPauli σ
    (blockPauliAction m K (fun j ↦ (e j).2)
      (permutePauliLabel σ.symm p))
  simpa [shiftedBlockPauliCosetCliffordUnitary,
      shiftedBlockPauliAction, one_mul] using
    unitaryPauliConjugation_mul
      (binaryWordPermutationUnitary σ)
      (blockPauliCosetCliffordUnitary m K e *
        binaryWordPermutationUnitary σ.symm)
      p
      (blockPauliAction m K (fun j ↦ (e j).2)
        (permutePauliLabel σ.symm p))
      (permutePauliLabel σ
        (blockPauliAction m K (fun j ↦ (e j).2)
          (permutePauliLabel σ.symm p)))
      phase 1 (by simpa only [one_mul] using hfirst)
        (by simpa only [one_smul] using hleft)

/-- Finite pair of independent local Clifford choices for the two periodic
layers. -/
abbrev PeriodicTwoLayerCliffordEnsemble (m K : ℕ) :=
  (Fin m → PauliCosetCliffordEnsemble K) ×
    (Fin m → PauliCosetCliffordEnsemble K)

/-- Pauli-label action of a shifted first block layer followed by an
unshifted second block layer. -/
noncomputable def periodicTwoLayerPauliAction
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K)
    (p : PauliLabel (m * K)) : PauliLabel (m * K) :=
  blockPauliAction m K (fun j ↦ (e.2 j).2)
    (shiftedBlockPauliAction m K σ (fun j ↦ (e.1 j).2) p)

/-- Literal two-layer periodic circuit unitary. -/
noncomputable def periodicTwoLayerCliffordUnitary
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ :=
  blockPauliCosetCliffordUnitary m K e.2 *
    shiftedBlockPauliCosetCliffordUnitary m K σ e.1

/-- The literal two-layer unitary implements the displayed periodic
blockwise Pauli action, up to a nonzero phase. -/
theorem periodicTwoLayerCliffordUnitary_conjugates_binaryPauli
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K)
    (p : PauliLabel (m * K)) :
    ∃ phase : ℂ, phase ≠ 0 ∧
      (((periodicTwoLayerCliffordUnitary m K σ e).1 *
          binaryPauliMatrix (m * K) p) *
          (periodicTwoLayerCliffordUnitary m K σ e).1.conjTranspose) =
        phase • binaryPauliMatrix (m * K)
          (periodicTwoLayerPauliAction m K σ e p) := by
  obtain ⟨c, hc, hfirst⟩ :=
    shiftedBlockPauliCosetCliffordUnitary_conjugates_binaryPauli
      m K σ e.1 p
  obtain ⟨d, hd, hsecond⟩ :=
    blockPauliCosetCliffordUnitary_conjugates_binaryPauli m K e.2
      (shiftedBlockPauliAction m K σ (fun j ↦ (e.1 j).2) p)
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  simpa [periodicTwoLayerCliffordUnitary, periodicTwoLayerPauliAction] using
    unitaryPauliConjugation_mul
      (blockPauliCosetCliffordUnitary m K e.2)
      (shiftedBlockPauliCosetCliffordUnitary m K σ e.1)
      p
      (shiftedBlockPauliAction m K σ (fun j ↦ (e.1 j).2) p)
      (periodicTwoLayerPauliAction m K σ e p)
      c d hfirst hsecond

/-- The Cho--Kim half-block periodic architecture, with shift `K/2`. -/
noncomputable def choKimPeriodicTwoLayerCliffordUnitary
    (m K : ℕ) (e : PeriodicTwoLayerCliffordEnsemble m K) :
    Matrix.unitaryGroup (PauliBinaryWord (m * K)) ℂ :=
  periodicTwoLayerCliffordUnitary m K (cyclicQubitShift (m * K) (K / 2)) e

end
end TomographyOracleCore

