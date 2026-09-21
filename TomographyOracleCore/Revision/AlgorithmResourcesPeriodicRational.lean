import TomographyOracleCore.Revision.AlgorithmResourcesPeriodicAverage
import TomographyOracleCore.Revision.MatrixSolverRationalPauli

/-! An executable rational periodic-channel multiplier table.

This uses an orbit average over at most d² Pauli labels for each of the d²
inputs. It avoids Clifford-group enumeration. The paper's faster two-state
transfer implementation is not needed for this polynomial-in-d construction.
-/

namespace TomographyOracleCore.Revision.AlgorithmResources

open MatrixSolver
open scoped BigOperators

def qPauliBlock {m K : ℕ} (p : PauliLabel (m * K)) (j : Fin m) : PauliLabel K :=
  (fun i => p.1 (finProdFinEquiv (j, i)), fun i => p.2 (finProdFinEquiv (j, i)))

def qPermutePauli {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : PauliLabel N) : PauliLabel N :=
  (fun i => p.1 (σ.symm i), fun i => p.2 (σ.symm i))

def qCyclicShift : (N : ℕ) → ℕ → Equiv.Perm (Fin N)
  | 0, _ => Equiv.refl _
  | N + 1, s => (Fin.cycleRange (Fin.last N)) ^ s

def qActiveBlocks {m K : ℕ} (p : PauliLabel (m * K)) : ℕ :=
  (Finset.univ.filter (fun j : Fin m => qPauliBlock p j ≠ 0)).card

def qOrbitWords {m K : ℕ} (p : PauliLabel (m * K)) : Finset (PauliLabel (m * K)) :=
  Finset.univ.filter (fun q => ∀ j : Fin m, qPauliBlock q j = 0 ↔ qPauliBlock p j = 0)

/-- All enumerations are over binary Pauli words, whose number is d². -/
def qPeriodicHit (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) : ℚ :=
  let orbit := qOrbitWords (qPermutePauli σ.symm p)
  (∑ q ∈ orbit, (1 / ((2 : ℚ) ^ K + 1)) ^ qActiveBlocks (qPermutePauli σ q)) / orbit.card

def qPeriodicFullMultiplier (n K : ℕ) (p : PauliLabel ((n / K) * K)) : ℚ :=
  if p = 0 then 1 else
    ((2 : ℚ) ^ n + 1) *
      qPeriodicHit (n / K) K (qCyclicShift ((n / K) * K) (K / 2)) p

noncomputable section
set_option maxHeartbeats 1000000

@[simp] theorem qPauliBlock_eq {m K : ℕ} (p : PauliLabel (m * K)) (j : Fin m) :
    qPauliBlock p j = pauliLabelBlockEquiv m K p j := rfl

@[simp] theorem qPermutePauli_eq {N : ℕ} (σ : Equiv.Perm (Fin N)) (p : PauliLabel N) :
    qPermutePauli σ p = permutePauliLabel σ p := rfl

@[simp] theorem qCyclicShift_eq (N s : ℕ) : qCyclicShift N s = cyclicQubitShift N s := by
  cases N <;> rfl

@[simp] theorem qActiveBlocks_eq {m K : ℕ} (p : PauliLabel (m * K)) :
    qActiveBlocks p = activeBlockCount (globalPauliOptionalBlocks p) := by
  simp only [qActiveBlocks, activeBlockCount, globalPauliOptionalBlocks,
    Ne, optionalNonidentityPauliBlock_eq_none_iff, qPauliBlock_eq]
  rfl

theorem qOrbitWords_self_mem {m K : ℕ} (p : PauliLabel (m * K)) : p ∈ qOrbitWords p := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun _ => Iff.rfl⟩

theorem qOrbitWords_card_pos {m K : ℕ} (p : PauliLabel (m * K)) : 0 < (qOrbitWords p).card :=
  Finset.card_pos.mpr ⟨p, qOrbitWords_self_mem p⟩

theorem qOrbitWords_card_le {m K : ℕ} (p : PauliLabel (m * K)) :
    (qOrbitWords p).card ≤ 4 ^ (m * K) := by
  calc
    _ ≤ (Finset.univ : Finset (PauliLabel (m * K))).card := Finset.card_filter_le _ _
    _ = _ := by simp [PauliLabel, PauliBinaryWord, ← mul_pow]

theorem qOrbitWords_card_eq {m K : ℕ} (p : PauliLabel (m * K)) :
    (qOrbitWords p).card = Fintype.card (GlobalSupportOrbit m K p) := by
  classical
  simp only [qOrbitWords, qPauliBlock_eq, GlobalSupportOrbit, Fintype.card_subtype]
  rfl

theorem qOrbitWords_sum_eq {m K : ℕ} (p : PauliLabel (m * K))
    (f : PauliLabel (m * K) → ℝ) :
    (∑ q ∈ qOrbitWords p, f q) = ∑ q : GlobalSupportOrbit m K p, f q.1 := by
  classical
  exact Finset.sum_subtype (qOrbitWords p) (by
    intro q
    simp only [qOrbitWords, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl) f

/-- The actual rational computation equals the literal physical Clifford
hit probability. No multiplier identity is assumed. -/
theorem qPeriodicHit_cast (m K : ℕ) (hK : 0 < K)
    (σ : Equiv.Perm (Fin (m * K))) (p : PauliLabel (m * K)) :
    (qPeriodicHit m K σ p : ℝ) = periodicTwoLayerHitProbability m K σ p := by
  rw [periodic_hit_as_orbit_average m K hK σ p]
  unfold qPeriodicHit
  push_cast
  rw [qOrbitWords_sum_eq, qOrbitWords_card_eq]
  simp only [qPermutePauli_eq, qActiveBlocks_eq]
  rfl

theorem qPeriodicFullMultiplier_cast (n K : ℕ) (hK : 0 < K)
    (p : PauliLabel ((n / K) * K)) :
    (qPeriodicFullMultiplier n K p : ℝ) =
      choKimPeriodicFullCalibratedEigenvalue (n := n) (K := K) p := by
  unfold qPeriodicFullMultiplier choKimPeriodicFullCalibratedEigenvalue
  split_ifs with hp
  · norm_num
  · rw [Rat.cast_mul, Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one,
      qPeriodicHit_cast _ _ hK, qCyclicShift_eq]
    rfl

/-- End-to-end rational periodic channel evaluation, with the multiplier
table computed from the circuit geometry rather than supplied by a contract. -/
theorem rationalPeriodicPauliChannel_correct {n K : ℕ} (hdiv : K ∣ n) (hK : 0 < K)
    (A : Matrix (PauliBinaryWord ((n / K) * K)) (PauliBinaryWord ((n / K) * K)) QComplex) :
    castQMatrix (rationalPauliChannel ((n / K) * K) (qPeriodicFullMultiplier n K) A) =
      choKimPeriodicFullCalibratedBinaryLinearChannel hdiv (castQMatrix A) := by
  exact rationalPauliChannel_periodic_correct hdiv (qPeriodicFullMultiplier n K)
    (qPeriodicFullMultiplier_cast n K hK) A

#print axioms qPeriodicFullMultiplier_cast
#print axioms rationalPeriodicPauliChannel_correct

end
end TomographyOracleCore.Revision.AlgorithmResources
