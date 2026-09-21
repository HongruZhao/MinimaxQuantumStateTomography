import TomographyOracleCore.PeriodicCliffordFourthSectorInverse

namespace TomographyOracleCore

noncomputable section

open scoped Matrix

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-!
# Uniqueness of the explicit fourth-sector projection

The representation-theoretic input still missing from the physical Clifford
average is separated here from the finite linear algebra.  Once an operator
lies in the span of the thirty explicit sector matrices, its thirty
Hilbert--Schmidt pairings determine it uniquely for `3 ≤ r`.  Consequently,
any span-valued map whose residual is orthogonal to every sector is forced to
be the already verified Weingarten synthesis map.
-/

/-- A literal linear combination of the thirty fourth-sector matrices. -/
def qubitFourthSectorCombination
    (r : ℕ) (c : Fin 30 → ℂ) :
    Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ :=
  ∑ i : Fin 30, c i • qubitFourthSectorR r i

/-- Pairing a sector matrix against a literal sector combination is matrix
multiplication by the intrinsic Gram matrix. -/
theorem qubitFourthSector_hilbertSchmidt_combination
    (r : ℕ) (c : Fin 30 → ℂ) (l : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (qubitFourthSectorCombination r c) =
      (qubitFourthSectorRGramMatrix r *ᵥ c) l := by
  unfold qubitFourthSectorCombination
  rw [qubitFourthComplexHilbertSchmidt_sum_right]
  simp_rw [qubitFourthComplexHilbertSchmidt_smul_right]
  change
    (∑ i : Fin 30,
      c i * qubitFourthComplexHilbertSchmidt
        (qubitFourthSectorR r l) (qubitFourthSectorR r i)) =
      ∑ i : Fin 30,
        qubitFourthComplexHilbertSchmidt
          (qubitFourthSectorR r l) (qubitFourthSectorR r i) * c i
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- In the nonsingular block regime, no nonzero sector combination can be
orthogonal to all thirty sectors. -/
theorem qubitFourthSectorCombination_eq_zero_of_pairings
    {r : ℕ} (hr : 3 ≤ r) (c : Fin 30 → ℂ)
    (hpair : ∀ l : Fin 30,
      qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (qubitFourthSectorCombination r c) = 0) :
    qubitFourthSectorCombination r c = 0 := by
  have hGram : qubitFourthSectorRGramMatrix r *ᵥ c = 0 := by
    funext l
    rw [← qubitFourthSector_hilbertSchmidt_combination]
    exact hpair l
  have hleft := qubitFourthComplexWgMatrix_mul_sectorRGram hr
  have happly := congrArg
    (fun v : Fin 30 → ℂ ↦
      qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) *ᵥ v) hGram
  have hc : c = 0 := by
    simpa [Matrix.mulVec_mulVec, hleft] using happly
  simp [qubitFourthSectorCombination, hc]

/-- Sector combinations commute with subtraction of their coefficient
vectors. -/
theorem qubitFourthSectorCombination_sub
    (r : ℕ) (c d : Fin 30 → ℂ) :
    qubitFourthSectorCombination r (c - d) =
      qubitFourthSectorCombination r c -
        qubitFourthSectorCombination r d := by
  unfold qubitFourthSectorCombination
  simp_rw [Pi.sub_apply, sub_smul]
  rw [Finset.sum_sub_distrib]

/-- The explicit synthesis candidate is visibly a sector combination. -/
theorem qubitFourthSectorSynthesisCandidate_eq_combination
    (r : ℕ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ) :
    qubitFourthSectorSynthesisCandidate r X =
      qubitFourthSectorCombination r (fun i ↦
        ∑ j : Fin 30,
          qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) i j *
            qubitFourthSectorAnalysis r X j) := by
  rw [qubitFourthSectorSynthesisCandidate_apply]
  unfold qubitFourthSectorCombination
  apply Finset.sum_congr rfl
  intro i _hi
  rw [Finset.sum_smul]

/-- Elementary uniqueness principle for an orthogonal projection onto the
explicit sector span.  This theorem contains the complete deterministic
reduction needed by the physical fourth-average bridge: representation theory
only has to supply `hspan` and `hresidual`. -/
theorem qubitFourthSectorProjection_unique
    {r : ℕ} (hr : 3 ≤ r)
    (X Y : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (c : Fin 30 → ℂ)
    (hspan : Y = qubitFourthSectorCombination r c)
    (hresidual : ∀ l : Fin 30,
      qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (X - Y) = 0) :
    Y = qubitFourthSectorSynthesisCandidate r X := by
  let d : Fin 30 → ℂ := fun i ↦
    ∑ j : Fin 30,
      qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) i j *
        qubitFourthSectorAnalysis r X j
  have hcandidate : qubitFourthSectorSynthesisCandidate r X =
      qubitFourthSectorCombination r d := by
    exact qubitFourthSectorSynthesisCandidate_eq_combination r X
  have hpairDifference : ∀ l : Fin 30,
      qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (Y - qubitFourthSectorSynthesisCandidate r X) = 0 := by
    intro l
    have hy := hresidual l
    have hs := qubitFourthSectorSynthesisCandidate_residual_orthogonal hr X l
    rw [qubitFourthComplexHilbertSchmidt_sub_right] at hy hs ⊢
    exact sub_eq_zero.mpr
      ((sub_eq_zero.mp hy).symm.trans (sub_eq_zero.mp hs))
  have hcombinationZero :
      qubitFourthSectorCombination r (c - d) = 0 := by
    apply qubitFourthSectorCombination_eq_zero_of_pairings hr
    intro l
    rw [qubitFourthSectorCombination_sub, ← hspan, ← hcandidate]
    exact hpairDifference l
  have hzero : Y - qubitFourthSectorSynthesisCandidate r X = 0 := by
    rw [hspan, hcandidate, ← qubitFourthSectorCombination_sub]
    exact hcombinationZero
  exact sub_eq_zero.mp hzero

end

end TomographyOracleCore
