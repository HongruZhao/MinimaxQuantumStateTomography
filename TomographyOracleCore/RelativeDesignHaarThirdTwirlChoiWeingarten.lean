import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceB23
import TomographyOracleCore.RelativeDesignFiniteUnitaryThirdTwirlCP
import TomographyOracleCore.RelativeDesignThreeMomentApproximateHaar

namespace TomographyOracleCore

open scoped CStarAlgebra Matrix.Norms.L2Operator BigOperators

noncomputable section

local instance haarChoiWeingartenSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance haarChoiWeingartenStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-!
# The order-three Haar Choi matrix as a Weingarten sum

This module identifies the literal Choi matrix of the concrete exact Haar
third twirl with the normalized order-three Weingarten permutation sum.  It
uses the exact finite Clifford third-design theorem only to establish the
range of the twirl; the coefficient computation is finite-dimensional
linear algebra on the six permutations of three replica slots.
-/

/-- The usual action of `S₃` on a right-associated triple index. -/
def tripleIndexSlotPermutation (I : Type*)
    (sigma : Equiv.Perm (Fin 3)) : Equiv.Perm (TripleIndex I) :=
  (threeReplicaEquivTriple I).symm.trans <|
    (threeReplicaSlotPermutation I sigma).trans (threeReplicaEquivTriple I)

@[simp] theorem tripleIndexSlotPermutation_apply
    (I : Type*) (sigma : Equiv.Perm (Fin 3)) (x : TripleIndex I) :
    tripleIndexSlotPermutation I sigma x =
      let xCoord := fun i : Fin 3 => if i = 0 then x.1
        else if i = 1 then x.2.1 else x.2.2
      (xCoord (sigma⁻¹ 0), xCoord (sigma⁻¹ 1), xCoord (sigma⁻¹ 2)) := by
  rfl

/-- Permutation matrix for an order-three replica-slot permutation. -/
def tripleIndexSlotPermutationMatrix
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) :
    Matrix (TripleIndex I) (TripleIndex I) ℂ :=
  Matrix.permMatrixHom (R := ℂ) (tripleIndexSlotPermutation I sigma)

theorem tripleIndexSlotPermutation_mul
    (I : Type*) (sigma tau : Equiv.Perm (Fin 3)) :
    tripleIndexSlotPermutation I (sigma * tau) =
      tripleIndexSlotPermutation I sigma *
        tripleIndexSlotPermutation I tau := by
  apply Equiv.ext
  intro x
  apply (threeReplicaEquivTriple I).symm.injective
  simp [tripleIndexSlotPermutation, threeReplicaSlotPermutation_mul]

theorem tripleIndexSlotPermutation_inv
    (I : Type*) (sigma : Equiv.Perm (Fin 3)) :
    tripleIndexSlotPermutation I sigma⁻¹ =
      (tripleIndexSlotPermutation I sigma)⁻¹ := by
  ext x <;> rfl

@[simp] theorem tripleIndexSlotPermutationMatrix_apply
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) (x y : TripleIndex I) :
    tripleIndexSlotPermutationMatrix I sigma x y =
      if y = (tripleIndexSlotPermutation I sigma)⁻¹ x then 1 else 0 := by
  change ((tripleIndexSlotPermutation I sigma)⁻¹.permMatrix ℂ) x y = _
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

@[simp] theorem tripleIndexSlotPermutationMatrix_one
    (I : Type*) [Fintype I] [DecidableEq I] :
    tripleIndexSlotPermutationMatrix I 1 = 1 := by
  ext x y
  simp [tripleIndexSlotPermutationMatrix, tripleIndexSlotPermutation,
    threeReplicaSlotPermutation, threeReplicaEquivTriple, Matrix.one_apply]

theorem tripleIndexSlotPermutationMatrix_mul
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma tau : Equiv.Perm (Fin 3)) :
    tripleIndexSlotPermutationMatrix I sigma *
        tripleIndexSlotPermutationMatrix I tau =
      tripleIndexSlotPermutationMatrix I (sigma * tau) := by
  unfold tripleIndexSlotPermutationMatrix
  rw [← map_mul, tripleIndexSlotPermutation_mul]

theorem tripleIndexSlotPermutationMatrix_transpose
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) :
    (tripleIndexSlotPermutationMatrix I sigma).transpose =
      tripleIndexSlotPermutationMatrix I sigma⁻¹ := by
  classical
  unfold tripleIndexSlotPermutationMatrix
  change (((tripleIndexSlotPermutation I sigma)⁻¹).permMatrix ℂ).transpose =
    ((tripleIndexSlotPermutation I sigma⁻¹)⁻¹).permMatrix ℂ
  rw [Matrix.transpose_permMatrix, tripleIndexSlotPermutation_inv]

/-- Entrywise bilinear pairing with a replica permutation matrix.  The
absence of conjugation is intentional: replica permutation entries are real
zero-one values, and this is the pairing appearing in Choi coordinates. -/
def triplePermutationPairing
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3))
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) : ℂ :=
  ∑ i : TripleIndex I, ∑ j : TripleIndex I,
    tripleIndexSlotPermutationMatrix I sigma i j * X i j

theorem triplePermutationPairing_eq_trace
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3))
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    triplePermutationPairing I sigma X =
      ((tripleIndexSlotPermutationMatrix I sigma).transpose * X).trace := by
  classical
  change (∑ i : TripleIndex I, ∑ j : TripleIndex I,
      tripleIndexSlotPermutationMatrix I sigma i j * X i j) =
    ∑ i : TripleIndex I, ∑ j : TripleIndex I,
      tripleIndexSlotPermutationMatrix I sigma j i * X j i
  rw [Finset.sum_comm]

/-- A replica-slot permutation has one fixed basis assignment for each of
its cycles. -/
theorem trace_tripleIndexSlotPermutationMatrix
    (I : Type*) [Fintype I] [DecidableEq I]
    (pi : Equiv.Perm (Fin 3)) :
    (tripleIndexSlotPermutationMatrix I pi).trace =
      (Fintype.card I : ℂ) ^ finThreeFullCycleCount pi := by
  classical
  rw [Matrix.trace]
  simp_rw [Matrix.diag_apply, tripleIndexSlotPermutationMatrix_apply]
  calc
    (∑ x : TripleIndex I,
        if x = (tripleIndexSlotPermutation I pi)⁻¹ x then (1 : ℂ) else 0) =
        ∑ x : ThreeReplica I,
          if threeReplicaSlotPermutation I pi⁻¹ x = x then (1 : ℂ) else 0 := by
      rw [← (threeReplicaEquivTriple I).sum_comp]
      apply Fintype.sum_congr
      intro x
      change (if (threeReplicaEquivTriple I) x =
          (tripleIndexSlotPermutation I pi)⁻¹
            ((threeReplicaEquivTriple I) x) then (1 : ℂ) else 0) =
        if threeReplicaSlotPermutation I pi⁻¹ x = x then 1 else 0
      rw [← tripleIndexSlotPermutation_inv]
      simp [tripleIndexSlotPermutation, eq_comm]
    _ = (Fintype.card I : ℂ) ^ finThreeFullCycleCount pi⁻¹ :=
      sum_threeReplicaSlotPermutation_fixed_indicator I pi⁻¹
    _ = (Fintype.card I : ℂ) ^ finThreeFullCycleCount pi := by
      rw [finThreeFullCycleCount_inv]

/-- The replica permutation matrices have the normalized Gram matrix used
by the order-three Weingarten inverse. -/
theorem triplePermutationPairing_matrix
    (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I]
    (sigma tau : Equiv.Perm (Fin 3)) :
    triplePermutationPairing I sigma
        (tripleIndexSlotPermutationMatrix I tau) =
      ((Fintype.card I : ℂ) ^ 3) *
        (normalizedPermutationGramThree (Fintype.card I) sigma tau : ℂ) := by
  rw [triplePermutationPairing_eq_trace,
    tripleIndexSlotPermutationMatrix_transpose,
    tripleIndexSlotPermutationMatrix_mul,
    trace_tripleIndexSlotPermutationMatrix]
  have hcycles : finThreeFullCycleCount (sigma⁻¹ * tau) =
      finThreeFullCycleCount (sigma * tau⁻¹) := by
    calc
      finThreeFullCycleCount (sigma⁻¹ * tau) =
          finThreeFullCycleCount (sigma⁻¹ * (sigma * tau⁻¹)⁻¹ *
            (sigma⁻¹)⁻¹) := by
              congr 1
              group
      _ = finThreeFullCycleCount (sigma * tau⁻¹)⁻¹ :=
        finThreeFullCycleCount_conj _ _
      _ = finThreeFullCycleCount (sigma * tau⁻¹) :=
        finThreeFullCycleCount_inv _
  rw [hcycles]
  unfold normalizedPermutationGramThree
  have hcard : (Fintype.card I : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  norm_cast
  field_simp

set_option maxHeartbeats 1200000 in
/-- The explicit normalized Weingarten matrix is also a left inverse of the
normalized permutation Gram matrix. -/
theorem normalizedWeingartenThree_mul_normalizedPermutationGramThree
    (D : ℕ) (hD : 3 ≤ D)
    (rho tau : Equiv.Perm (Fin 3)) :
    (∑ sigma : Equiv.Perm (Fin 3),
      normalizedWeingartenThree D rho sigma *
        normalizedPermutationGramThree D sigma tau) =
      if rho = tau then 1 else 0 := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hD1 : (D : ℝ) ^ 2 - 1 ≠ 0 := by
    have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  have hD4 : (D : ℝ) ^ 2 - 4 ≠ 0 := by
    have hDr : (3 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  rcases finThreePerm_eq_six rho with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases finThreePerm_eq_six tau with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [finThreePerm_univ_explicit,
      normalizedPermutationGramThree, normalizedWeingartenThree,
      weingartenThreeDenominator, finThreeFullCycleCount,
      finThreeCycleForward, finThreeCycleBackward, Equiv.swap_apply_def] <;>
    field_simp <;> ring

set_option maxHeartbeats 1200000 in
/-- Symmetry of the order-three normalized permutation Gram matrix. -/
theorem normalizedPermutationGramThree_comm
    (D : ℕ) (sigma tau : Equiv.Perm (Fin 3)) :
    normalizedPermutationGramThree D sigma tau =
      normalizedPermutationGramThree D tau sigma := by
  rcases finThreePerm_eq_six sigma with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases finThreePerm_eq_six tau with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp +decide [normalizedPermutationGramThree, finThreeFullCycleCount,
      finThreeCycleForward, finThreeCycleBackward]

/-- Applying the inverse Gram matrix to arbitrary coefficients recovers the
original coefficient. -/
theorem sum_normalizedWeingartenThree_gram_coeff
    (D : ℕ) (hD : 3 ≤ D)
    (rho : Equiv.Perm (Fin 3))
    (c : Equiv.Perm (Fin 3) → ℂ) :
    (∑ tau : Equiv.Perm (Fin 3),
      ∑ sigma : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree D sigma tau : ℂ) * c sigma *
          (normalizedPermutationGramThree D rho tau : ℂ)) =
      c rho := by
  have hinv : ∀ sigma : Equiv.Perm (Fin 3),
      (∑ tau : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree D sigma tau : ℂ) *
          (normalizedPermutationGramThree D tau rho : ℂ)) =
        if sigma = rho then 1 else 0 := by
    intro sigma
    have h := congrArg (fun x : ℝ ↦ (x : ℂ))
      (normalizedWeingartenThree_mul_normalizedPermutationGramThree
        D hD sigma rho)
    push_cast at h
    by_cases hsr : sigma = rho
    · simp [hsr] at h ⊢
      exact h
    · simp [hsr] at h ⊢
      exact h
  calc
    (∑ tau : Equiv.Perm (Fin 3),
      ∑ sigma : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree D sigma tau : ℂ) * c sigma *
          (normalizedPermutationGramThree D rho tau : ℂ)) =
        ∑ sigma : Equiv.Perm (Fin 3),
          ∑ tau : Equiv.Perm (Fin 3),
            (normalizedWeingartenThree D sigma tau : ℂ) * c sigma *
              (normalizedPermutationGramThree D rho tau : ℂ) := by
      rw [Finset.sum_comm]
    _ = ∑ sigma : Equiv.Perm (Fin 3), c sigma *
          (∑ tau : Equiv.Perm (Fin 3),
            (normalizedWeingartenThree D sigma tau : ℂ) *
              (normalizedPermutationGramThree D tau rho : ℂ)) := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tau htau
      rw [normalizedPermutationGramThree_comm D rho tau]
      ring
    _ = ∑ sigma : Equiv.Perm (Fin 3), c sigma *
          (if sigma = rho then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      rw [hinv sigma]
    _ = c rho := by simp

/-- Linear-functional form of `triplePermutationPairing`. -/
def triplePermutationPairingLinearMap
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) :
    Matrix (TripleIndex I) (TripleIndex I) ℂ →ₗ[ℂ] ℂ where
  toFun := triplePermutationPairing I sigma
  map_add' X Y := by
    unfold triplePermutationPairing
    simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c X := by
    unfold triplePermutationPairing
    simp only [RingHom.id_apply, Matrix.smul_apply, smul_eq_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring

@[simp] theorem triplePermutationPairingLinearMap_apply
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3))
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    (triplePermutationPairingLinearMap I sigma) X =
      triplePermutationPairing I sigma X := rfl

@[simp] theorem triplePermutationPairing_add
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3))
    (X Y : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    triplePermutationPairing I sigma (X + Y) =
      triplePermutationPairing I sigma X +
        triplePermutationPairing I sigma Y :=
  map_add (triplePermutationPairingLinearMap I sigma) X Y

@[simp] theorem triplePermutationPairing_smul
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) (c : ℂ)
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    triplePermutationPairing I sigma (c • X) =
      c * triplePermutationPairing I sigma X := by
  exact map_smul (triplePermutationPairingLinearMap I sigma) c X

/-- Matrix-space Weingarten projection at moment order three. -/
def weingartenThirdTwirlMatrixLinearMap
    (I : Type*) [Fintype I] [DecidableEq I] :
    Matrix (TripleIndex I) (TripleIndex I) ℂ →ₗ[ℂ]
      Matrix (TripleIndex I) (TripleIndex I) ℂ :=
  ((((Fintype.card I : ℝ) ^ 3)⁻¹ : ℂ)) •
    ∑ tau : Equiv.Perm (Fin 3),
      ∑ sigma : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) •
          (triplePermutationPairingLinearMap I sigma).smulRight
            (tripleIndexSlotPermutationMatrix I tau)

@[simp] theorem weingartenThirdTwirlMatrixLinearMap_apply
    (I : Type*) [Fintype I] [DecidableEq I]
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    weingartenThirdTwirlMatrixLinearMap I X =
      ((((Fintype.card I : ℝ) ^ 3)⁻¹ : ℂ)) •
        ∑ tau : Equiv.Perm (Fin 3),
          ∑ sigma : Equiv.Perm (Fin 3),
            ((normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
              triplePermutationPairing I sigma X) •
                tripleIndexSlotPermutationMatrix I tau := by
  simp [weingartenThirdTwirlMatrixLinearMap, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.smulRight_apply,
    triplePermutationPairingLinearMap, smul_smul]

/-- The Weingarten projection preserves all six replica-permutation
pairings. -/
theorem triplePermutationPairing_weingartenThirdTwirl
    (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I)
    (rho : Equiv.Perm (Fin 3))
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    triplePermutationPairing I rho
        (weingartenThirdTwirlMatrixLinearMap I X) =
      triplePermutationPairing I rho X := by
  rw [weingartenThirdTwirlMatrixLinearMap_apply]
  change (triplePermutationPairingLinearMap I rho)
      (((((Fintype.card I : ℝ) ^ 3)⁻¹ : ℂ)) •
        ∑ tau : Equiv.Perm (Fin 3),
          ∑ sigma : Equiv.Perm (Fin 3),
            ((normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
              triplePermutationPairing I sigma X) •
                tripleIndexSlotPermutationMatrix I tau) = _
  rw [map_smul, map_sum]
  simp_rw [map_sum, map_smul,
    triplePermutationPairingLinearMap_apply]
  simp_rw [triplePermutationPairing_matrix]
  simp only [smul_eq_mul]
  have hconv := sum_normalizedWeingartenThree_gram_coeff
    (Fintype.card I) hcard rho
    (fun sigma ↦ triplePermutationPairing I sigma X)
  have hdouble :
      (∑ tau : Equiv.Perm (Fin 3),
        ∑ sigma : Equiv.Perm (Fin 3),
          ((normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
              triplePermutationPairing I sigma X) *
            (((Fintype.card I : ℂ) ^ 3) *
              (normalizedPermutationGramThree (Fintype.card I) rho tau : ℂ))) =
        ((Fintype.card I : ℂ) ^ 3) *
          triplePermutationPairing I rho X := by
    calc
      _ = ((Fintype.card I : ℂ) ^ 3) *
          (∑ tau : Equiv.Perm (Fin 3),
            ∑ sigma : Equiv.Perm (Fin 3),
              (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
                triplePermutationPairing I sigma X *
                (normalizedPermutationGramThree (Fintype.card I) rho tau : ℂ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro tau htau
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro sigma hsigma
          ring
      _ = _ := by rw [hconv]
  rw [hdouble]
  have hD : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have hscale : ((((Fintype.card I : ℝ) ^ 3)⁻¹ : ℂ)) *
      ((Fintype.card I : ℂ) ^ 3) = 1 := by
    push_cast
    field_simp
  rw [← mul_assoc, hscale, one_mul]

/-- The Weingarten projection fixes each replica permutation matrix. -/
theorem weingartenThirdTwirlMatrixLinearMap_permutation
    (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I)
    (rho : Equiv.Perm (Fin 3)) :
    weingartenThirdTwirlMatrixLinearMap I
        (tripleIndexSlotPermutationMatrix I rho) =
      tripleIndexSlotPermutationMatrix I rho := by
  rw [weingartenThirdTwirlMatrixLinearMap_apply]
  simp_rw [triplePermutationPairing_matrix]
  have hinv : ∀ tau : Equiv.Perm (Fin 3),
      (∑ sigma : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
          (normalizedPermutationGramThree (Fintype.card I) sigma rho : ℂ)) =
        if rho = tau then 1 else 0 := by
    intro tau
    have hreal :=
      normalizedPermutationGramThree_mul_normalizedWeingartenThree
        (Fintype.card I) hcard rho tau
    have h := congrArg (fun x : ℝ ↦ (x : ℂ)) hreal
    push_cast at h
    have hreorder :
        (∑ sigma : Equiv.Perm (Fin 3),
          (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
            (normalizedPermutationGramThree (Fintype.card I) sigma rho : ℂ)) =
          ∑ sigma : Equiv.Perm (Fin 3),
            (normalizedPermutationGramThree (Fintype.card I) rho sigma : ℂ) *
              (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) := by
      apply Finset.sum_congr rfl
      intro sigma hsigma
      rw [normalizedPermutationGramThree_comm _ sigma rho]
      ring
    rw [hreorder]
    by_cases hrt : rho = tau
    · simp [hrt] at h ⊢
      exact h
    · simp [hrt] at h ⊢
      exact h
  have hsum :
      (∑ tau : Equiv.Perm (Fin 3),
        ∑ sigma : Equiv.Perm (Fin 3),
          ((normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
              (((Fintype.card I : ℂ) ^ 3) *
                (normalizedPermutationGramThree (Fintype.card I) sigma rho : ℂ))) •
            tripleIndexSlotPermutationMatrix I tau) =
        ((Fintype.card I : ℂ) ^ 3) •
          tripleIndexSlotPermutationMatrix I rho := by
    calc
      _ = ∑ tau : Equiv.Perm (Fin 3),
          (((Fintype.card I : ℂ) ^ 3) *
            (∑ sigma : Equiv.Perm (Fin 3),
              (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) *
                (normalizedPermutationGramThree (Fintype.card I) sigma rho : ℂ))) •
            tripleIndexSlotPermutationMatrix I tau := by
          apply Finset.sum_congr rfl
          intro tau htau
          rw [← Finset.sum_smul]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro sigma hsigma
          ring
      _ = ∑ tau : Equiv.Perm (Fin 3),
          (((Fintype.card I : ℂ) ^ 3) *
            (if rho = tau then 1 else 0)) •
              tripleIndexSlotPermutationMatrix I tau := by
          apply Finset.sum_congr rfl
          intro tau htau
          rw [hinv tau]
      _ = ((Fintype.card I : ℂ) ^ 3) •
          tripleIndexSlotPermutationMatrix I rho := by simp
  rw [hsum]
  have hD : (Fintype.card I : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card I ≠ 0)
  have hscale : ((((Fintype.card I : ℝ) ^ 3)⁻¹ : ℂ)) *
      ((Fintype.card I : ℂ) ^ 3) = 1 := by
    push_cast
    field_simp
  rw [smul_smul, hscale, one_smul]

/-- The span of the six replica-slot permutation matrices. -/
def triplePermutationSubmodule
    (I : Type*) [Fintype I] [DecidableEq I] :
    Submodule ℂ (Matrix (TripleIndex I) (TripleIndex I) ℂ) :=
  Submodule.span ℂ (Set.range (tripleIndexSlotPermutationMatrix I))

/-- The Weingarten projection is the identity on the permutation span. -/
theorem weingartenThirdTwirlMatrixLinearMap_eq_self_of_mem
    (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I)
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ)
    (hX : X ∈ triplePermutationSubmodule I) :
    weingartenThirdTwirlMatrixLinearMap I X = X := by
  unfold triplePermutationSubmodule at hX
  refine Submodule.span_induction
    (p := fun X _ ↦ weingartenThirdTwirlMatrixLinearMap I X = X)
    ?_ ?_ ?_ ?_ hX
  · intro X hX
    rcases hX with ⟨rho, rfl⟩
    exact weingartenThirdTwirlMatrixLinearMap_permutation I hcard rho
  · exact map_zero (weingartenThirdTwirlMatrixLinearMap I)
  · intro X Y hXm hYm hXfix hYfix
    rw [map_add, hXfix, hYfix]
  · intro c X hXm hXfix
    rw [map_smul, hXfix]

/-- The six permutation pairings separate points of the permutation span. -/
theorem eq_zero_of_mem_triplePermutationSubmodule_of_pairings_zero
    (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I]
    (hcard : 3 ≤ Fintype.card I)
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ)
    (hX : X ∈ triplePermutationSubmodule I)
    (hpair : ∀ sigma : Equiv.Perm (Fin 3),
      triplePermutationPairing I sigma X = 0) :
    X = 0 := by
  have hfix := weingartenThirdTwirlMatrixLinearMap_eq_self_of_mem
    I hcard X hX
  have hzero : weingartenThirdTwirlMatrixLinearMap I X = 0 := by
    rw [weingartenThirdTwirlMatrixLinearMap_apply]
    simp_rw [hpair]
    simp
  rw [← hfix, hzero]

theorem tripleIndexSlotPermutation_swap01 (I : Type*) :
    tripleIndexSlotPermutation I (Equiv.swap 0 1) =
      tripleSwap12Equiv I := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x0, x1, x2⟩
  simp +decide [tripleIndexSlotPermutation, threeReplicaSlotPermutation,
    threeReplicaEquivTriple, tripleSwap12Equiv]

theorem tripleIndexSlotPermutation_swap12 (I : Type*) :
    tripleIndexSlotPermutation I (Equiv.swap 1 2) =
      tripleSwap23Equiv I := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x0, x1, x2⟩
  simp +decide [tripleIndexSlotPermutation, threeReplicaSlotPermutation,
    threeReplicaEquivTriple, tripleSwap23Equiv]

theorem tripleIndexSlotPermutation_swap02 (I : Type*) :
    tripleIndexSlotPermutation I (Equiv.swap 0 2) =
      tripleSwap13Equiv I := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x0, x1, x2⟩
  simp +decide [tripleIndexSlotPermutation, threeReplicaSlotPermutation,
    threeReplicaEquivTriple, tripleSwap13Equiv]

theorem tripleIndexSlotPermutation_cycleForward (I : Type*) :
    tripleIndexSlotPermutation I finThreeCycleForward =
      tripleCycle132Equiv I := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x0, x1, x2⟩
  simp +decide [tripleIndexSlotPermutation, threeReplicaSlotPermutation,
    threeReplicaEquivTriple, tripleCycle132Equiv,
    finThreeCycleForward, Equiv.swap_apply_def]

theorem tripleIndexSlotPermutation_cycleBackward (I : Type*) :
    tripleIndexSlotPermutation I finThreeCycleBackward =
      tripleCycle123Equiv I := by
  apply Equiv.ext
  intro x
  rcases x with ⟨x0, x1, x2⟩
  simp +decide [tripleIndexSlotPermutation, threeReplicaSlotPermutation,
    threeReplicaEquivTriple, tripleCycle123Equiv,
    finThreeCycleBackward, Equiv.swap_apply_def]

theorem tripleIndexSlotPermutationMatrix_eq_permutationMatrix
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) :
    tripleIndexSlotPermutationMatrix I sigma =
      permutationMatrix (tripleIndexSlotPermutation I sigma) := by
  ext x y
  simp [permutationMatrix, Equiv.eq_symm_apply, eq_comm]

/-- Every replica-slot permutation matrix belongs to Webb's concrete
six-permutation span. -/
theorem tripleIndexSlotPermutationMatrix_mem_webbPermutationSubmodule
    (K : ℕ) (sigma : Equiv.Perm (Fin 3)) :
    tripleIndexSlotPermutationMatrix (PauliBinaryWord K) sigma ∈
      webbPermutationSubmodule K := by
  rcases finThreePerm_eq_six sigma with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [tripleIndexSlotPermutationMatrix_one]
    exact one_mem_webbPermutationSubmodule K
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_swap12,
      ← registerSwap23_eq_permutationMatrix]
    exact swap23_mem_webbPermutationSubmodule K
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_swap01,
      ← registerSwap12_eq_permutationMatrix]
    exact swap12_mem_webbPermutationSubmodule K
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_cycleForward,
      ← registerCycle132_eq_permutationMatrix]
    exact cycle132_mem_webbPermutationSubmodule K
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_cycleBackward,
      ← registerCycle123_eq_permutationMatrix]
    exact cycle123_mem_webbPermutationSubmodule K
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_swap02,
      ← registerSwap13_eq_permutationMatrix]
    exact swap13_mem_webbPermutationSubmodule K

/-- Webb's named six-permutation span is contained in the uniform
`S₃`-indexed permutation span. -/
theorem webbPermutationSubmodule_le_triplePermutationSubmodule
    (K : ℕ) :
    webbPermutationSubmodule K ≤
      triplePermutationSubmodule (PauliBinaryWord K) := by
  unfold webbPermutationSubmodule
  apply Submodule.span_le.mpr
  intro X hX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [← tripleIndexSlotPermutationMatrix_one]
    exact Submodule.subset_span (Set.mem_range_self 1)
  · rw [registerSwap12_eq_permutationMatrix,
      ← tripleIndexSlotPermutation_swap01,
      ← tripleIndexSlotPermutationMatrix_eq_permutationMatrix]
    exact Submodule.subset_span (Set.mem_range_self (Equiv.swap 0 1))
  · rw [registerSwap23_eq_permutationMatrix,
      ← tripleIndexSlotPermutation_swap12,
      ← tripleIndexSlotPermutationMatrix_eq_permutationMatrix]
    exact Submodule.subset_span (Set.mem_range_self (Equiv.swap 1 2))
  · rw [registerSwap13_eq_permutationMatrix,
      ← tripleIndexSlotPermutation_swap02,
      ← tripleIndexSlotPermutationMatrix_eq_permutationMatrix]
    exact Submodule.subset_span (Set.mem_range_self (Equiv.swap 0 2))
  · rw [registerCycle123_eq_permutationMatrix,
      ← tripleIndexSlotPermutation_cycleBackward,
      ← tripleIndexSlotPermutationMatrix_eq_permutationMatrix]
    exact Submodule.subset_span (Set.mem_range_self finThreeCycleBackward)
  · rw [registerCycle132_eq_permutationMatrix,
      ← tripleIndexSlotPermutation_cycleForward,
      ← tripleIndexSlotPermutationMatrix_eq_permutationMatrix]
    exact Submodule.subset_span (Set.mem_range_self finThreeCycleForward)

/-- A tensor cube commutes with every replica-slot permutation. -/
theorem matrixTensorThree_commutes_tripleIndexSlotPermutationMatrix
    {I : Type*} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (sigma : Equiv.Perm (Fin 3)) :
    matrixTensorThree A A A * tripleIndexSlotPermutationMatrix I sigma =
      tripleIndexSlotPermutationMatrix I sigma * matrixTensorThree A A A := by
  rcases finThreePerm_eq_six sigma with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [tripleIndexSlotPermutationMatrix_one, mul_one, one_mul]
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_swap12]
    exact matrixTensorThree_commutes_tripleSwap23 A
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_swap01]
    exact matrixTensorThree_commutes_tripleSwap12 A
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_cycleForward]
    exact matrixTensorThree_commutes_tripleCycle132 A
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_cycleBackward]
    exact matrixTensorThree_commutes_tripleCycle123 A
  · rw [tripleIndexSlotPermutationMatrix_eq_permutationMatrix,
      tripleIndexSlotPermutation_swap02]
    exact matrixTensorThree_commutes_tripleSwap13 A

/-- Tensor-cube unitary conjugation preserves every replica-permutation
pairing. -/
theorem triplePermutationPairing_unitaryThirdConjugation
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (sigma : Equiv.Perm (Fin 3)) (X : ThirdM K) :
    triplePermutationPairing (PauliBinaryWord K) sigma
        (unitaryThirdConjugation K U X) =
      triplePermutationPairing (PauliBinaryWord K) sigma X := by
  let V := unitaryTensorCube K U
  let P := tripleIndexSlotPermutationMatrix (PauliBinaryWord K) sigma
  have hVV : V.conjTranspose * V = 1 := by
    unfold V unitaryTensorCube
    rw [← matrixTensorThree_conjTranspose,
      ← matrixTensorThree_mul]
    have hU : U.1.conjTranspose * U.1 = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        (Matrix.mem_unitaryGroup_iff'.mp U.2)
    rw [hU, matrixTensorThree_one]
  have hcomm : V * P.transpose = P.transpose * V := by
    rw [tripleIndexSlotPermutationMatrix_transpose]
    exact matrixTensorThree_commutes_tripleIndexSlotPermutationMatrix
      U.1 sigma⁻¹
  have hconj : V.conjTranspose * P.transpose * V = P.transpose := by
    calc
      V.conjTranspose * P.transpose * V =
          V.conjTranspose * (P.transpose * V) := by noncomm_ring
      _ = V.conjTranspose * (V * P.transpose) := by rw [← hcomm]
      _ = (V.conjTranspose * V) * P.transpose := by noncomm_ring
      _ = P.transpose := by rw [hVV, one_mul]
  rw [triplePermutationPairing_eq_trace,
    triplePermutationPairing_eq_trace]
  unfold unitaryThirdConjugation
  change (P.transpose * ((V * X) * V.conjTranspose)).trace =
    (P.transpose * X).trace
  calc
    (P.transpose * ((V * X) * V.conjTranspose)).trace =
        ((P.transpose * V) * (X * V.conjTranspose)).trace := by
          congr 1
          noncomm_ring
    _ = ((X * V.conjTranspose) * (P.transpose * V)).trace :=
      Matrix.trace_mul_comm _ _
    _ = (X * (V.conjTranspose * P.transpose * V)).trace := by
      congr 1
      noncomm_ring
    _ = (X * P.transpose).trace := by rw [hconj]
    _ = (P.transpose * X).trace := Matrix.trace_mul_comm _ _

/-- The literal normalized Haar third twirl preserves every
replica-permutation pairing. -/
theorem triplePermutationPairing_pauliHaarThirdTwirl
    (K : ℕ) (sigma : Equiv.Perm (Fin 3)) (X : ThirdM K) :
    triplePermutationPairing (PauliBinaryWord K) sigma
        (pauliHaarThirdTwirl K X) =
      triplePermutationPairing (PauliBinaryWord K) sigma X := by
  rw [← finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl K X]
  change (triplePermutationPairingLinearMap
      (PauliBinaryWord K) sigma)
      (((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
        ∑ e : PauliCosetCliffordEnsemble K,
          unitaryThirdConjugation K (pauliCosetCliffordUnitary K e) X) = _
  rw [map_smul, map_sum]
  simp_rw [triplePermutationPairingLinearMap_apply,
    triplePermutationPairing_unitaryThirdConjugation]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard :
      (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (PauliCosetCliffordEnsemble K) ≠ 0)
  rw [inv_mul_cancel₀ hcard, one_smul]

/-- The explicit Weingarten projection always lands in the permutation
span. -/
theorem weingartenThirdTwirlMatrixLinearMap_mem_triplePermutationSubmodule
    (I : Type*) [Fintype I] [DecidableEq I]
    (X : Matrix (TripleIndex I) (TripleIndex I) ℂ) :
    weingartenThirdTwirlMatrixLinearMap I X ∈
      triplePermutationSubmodule I := by
  rw [weingartenThirdTwirlMatrixLinearMap_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro tau htau
  apply Submodule.sum_mem
  intro sigma hsigma
  apply Submodule.smul_mem
  exact Submodule.subset_span (Set.mem_range_self tau)

/-- The exact Haar image of each Hermitian Pauli tensor lies in the uniform
`S₃`-indexed permutation span. -/
theorem pauliHaarThirdTwirl_hermitianPauliTensorThree_mem
    (K : ℕ) (p q r : PauliLabel K) :
    pauliHaarThirdTwirl K (hermitianPauliTensorThree K p q r) ∈
      triplePermutationSubmodule (PauliBinaryWord K) := by
  apply webbPermutationSubmodule_le_triplePermutationSubmodule K
  rw [← finitePauliCosetThirdTwirl_eq_pauliHaarThirdTwirl_on_pauliTensor]
  rw [finitePauliCosetThirdTwirl_hermitianPauliTensorThree]
  exact averagedHermitianPauliThirdMoment_mem_webbPermutationSubmodule K p q r

/-- The explicit Weingarten projection and the literal Haar twirl agree on
every Hermitian Pauli tensor. -/
theorem weingartenThirdTwirl_eq_pauliHaar_on_hermitianPauliTensorThree
    (K : ℕ) (hcard : 3 ≤ Fintype.card (PauliBinaryWord K))
    (p q r : PauliLabel K) :
    weingartenThirdTwirlMatrixLinearMap (PauliBinaryWord K)
        (hermitianPauliTensorThree K p q r) =
      pauliHaarThirdTwirl K (hermitianPauliTensorThree K p q r) := by
  let B := hermitianPauliTensorThree K p q r
  let H := pauliHaarThirdTwirl K B
  let W := weingartenThirdTwirlMatrixLinearMap (PauliBinaryWord K) B
  have hH : H ∈ triplePermutationSubmodule (PauliBinaryWord K) := by
    exact pauliHaarThirdTwirl_hermitianPauliTensorThree_mem K p q r
  have hW : W ∈ triplePermutationSubmodule (PauliBinaryWord K) := by
    exact weingartenThirdTwirlMatrixLinearMap_mem_triplePermutationSubmodule
      (PauliBinaryWord K) B
  have hpair : ∀ sigma : Equiv.Perm (Fin 3),
      triplePermutationPairing (PauliBinaryWord K) sigma (H - W) = 0 := by
    intro sigma
    change (triplePermutationPairingLinearMap
      (PauliBinaryWord K) sigma) (H - W) = 0
    rw [map_sub, triplePermutationPairingLinearMap_apply,
      triplePermutationPairingLinearMap_apply]
    change triplePermutationPairing (PauliBinaryWord K) sigma
        (pauliHaarThirdTwirl K B) -
      triplePermutationPairing (PauliBinaryWord K) sigma
        (weingartenThirdTwirlMatrixLinearMap (PauliBinaryWord K) B) = 0
    rw [triplePermutationPairing_pauliHaarThirdTwirl,
      triplePermutationPairing_weingartenThirdTwirl
        (PauliBinaryWord K) hcard]
    simp
  have hzero :=
    eq_zero_of_mem_triplePermutationSubmodule_of_pairings_zero
      (PauliBinaryWord K) hcard (H - W) (Submodule.sub_mem _ hH hW) hpair
  have hHW : H = W := sub_eq_zero.mp hzero
  exact hHW.symm

/-- Linear-map form of the exact order-three unitary Weingarten formula for
the concrete Haar twirl on `K` qubits. -/
theorem weingartenThirdTwirlMatrixLinearMap_eq_pauliHaarThirdTwirlLinearMap
    (K : ℕ) (hcard : 3 ≤ Fintype.card (PauliBinaryWord K)) :
    weingartenThirdTwirlMatrixLinearMap (PauliBinaryWord K) =
      pauliHaarThirdTwirlLinearMap K := by
  apply LinearMap.ext
  intro X
  rw [hermitianPauliTensorThree_reconstruction K X]
  simp only [map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  exact weingartenThirdTwirl_eq_pauliHaar_on_hermitianPauliTensorThree
    K hcard p q r

/-- The two-copy permutation tensor used in the Haar Choi formula. -/
def haarThirdTwirlPermutationQ
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma tau : Equiv.Perm (Fin 3)) :
    CStarMatrix ((TripleIndex I) × (TripleIndex I))
      ((TripleIndex I) × (TripleIndex I)) ℂ :=
  finiteThreeMomentPairQ (tripleIndexSlotPermutation I) sigma tau

@[simp] theorem haarThirdTwirlPermutationQ_apply
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : TripleIndex I) :
    haarThirdTwirlPermutationQ I sigma tau (i, a) (j, b) =
      tripleIndexSlotPermutationMatrix I sigma i j *
        tripleIndexSlotPermutationMatrix I tau a b := by
  rw [haarThirdTwirlPermutationQ, finiteThreeMomentPairQ_apply]
  change (if (j, b) =
      ((tripleIndexSlotPermutation I sigma)⁻¹ i,
        (tripleIndexSlotPermutation I tau)⁻¹ a) then 1 else 0) = _
  rw [tripleIndexSlotPermutationMatrix_apply,
    tripleIndexSlotPermutationMatrix_apply]
  split_ifs <;> simp_all

@[simp] theorem triplePermutationPairing_finiteMatrixUnit
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm (Fin 3)) (i j : TripleIndex I) :
    triplePermutationPairing I sigma
        (CStarMatrix.ofMatrix.symm (finiteCStarMatrixUnit i j)) =
      tripleIndexSlotPermutationMatrix I sigma i j := by
  classical
  unfold triplePermutationPairing
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [finiteCStarMatrixUnit]
    · intro y hy hyj
      simp [finiteCStarMatrixUnit, hyj]
    · simp
  · intro x hx hxi
    simp [finiteCStarMatrixUnit, hxi]
  · simp

/-- The raw (unnormalized-EPR convention) order-three Weingarten Choi sum. -/
def haarThirdTwirlWeingartenChoi
    (I : Type*) [Fintype I] [DecidableEq I] :
    CStarMatrix ((TripleIndex I) × (TripleIndex I))
      ((TripleIndex I) × (TripleIndex I)) ℂ :=
  ((((Fintype.card I : ℝ) ^ 3)⁻¹ : ℂ)) •
    ∑ sigma : Equiv.Perm (Fin 3),
      ∑ tau : Equiv.Perm (Fin 3),
        (normalizedWeingartenThree (Fintype.card I) sigma tau : ℂ) •
          haarThirdTwirlPermutationQ I sigma tau

/-- Exact Choi matrix of the explicit matrix-space Weingarten projection. -/
theorem finiteChoiMatrix_weingartenThirdTwirlMatrixLinearMap
    (I : Type*) [Fintype I] [DecidableEq I] :
    finiteChoiMatrix
        (cstarLinearMapOfMatrixLinearMap
          (weingartenThirdTwirlMatrixLinearMap I)) =
      finiteThreeMomentWeingartenRawChoi (Fintype.card I)
        (haarThirdTwirlPermutationQ I) := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  rw [finiteChoiMatrix_apply, cstarLinearMapOfMatrixLinearMap_apply]
  change weingartenThirdTwirlMatrixLinearMap I
      (CStarMatrix.ofMatrix.symm (finiteCStarMatrixUnit i j)) a b = _
  rw [weingartenThirdTwirlMatrixLinearMap_apply]
  unfold finiteThreeMomentWeingartenRawChoi
  simp only [Matrix.smul_apply, Matrix.sum_apply,
    CStarMatrix.smul_apply, cstarMatrix_fintypeSum_apply,
    triplePermutationPairing_finiteMatrixUnit,
    haarThirdTwirlPermutationQ_apply, smul_eq_mul]
  congr 1
  · simpa using Complex.ofReal_inv ((Fintype.card I : ℝ) ^ 3)
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sigma hsigma
    apply Finset.sum_congr rfl
    intro tau htau
    ring

/-- The local name for the raw Weingarten Choi sum agrees definitionally
with the reusable B.23 constructor. -/
theorem haarThirdTwirlWeingartenChoi_eq
    (I : Type*) [Fintype I] [DecidableEq I] :
    haarThirdTwirlWeingartenChoi I =
      finiteThreeMomentWeingartenRawChoi (Fintype.card I)
        (haarThirdTwirlPermutationQ I) := by
  unfold haarThirdTwirlWeingartenChoi
    finiteThreeMomentWeingartenRawChoi
  congr 1
  simpa using Complex.ofReal_inv ((Fintype.card I : ℝ) ^ 3)

/-- Multiplication law for the concrete two-copy permutation tensors. -/
theorem haarThirdTwirlPermutationQ_mul
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma tau sigma' tau' : Equiv.Perm (Fin 3)) :
    haarThirdTwirlPermutationQ I sigma tau *
        haarThirdTwirlPermutationQ I sigma' tau' =
      haarThirdTwirlPermutationQ I (sigma * sigma') (tau * tau') := by
  exact finiteThreeMomentPairQ_mul
    (tripleIndexSlotPermutation I)
    (tripleIndexSlotPermutation_mul I) sigma tau sigma' tau'

/-- Adjoint law for the concrete two-copy permutation tensors. -/
theorem haarThirdTwirlPermutationQ_star
    (I : Type*) [Fintype I] [DecidableEq I]
    (sigma tau : Equiv.Perm (Fin 3)) :
    star (haarThirdTwirlPermutationQ I sigma tau) =
      haarThirdTwirlPermutationQ I sigma⁻¹ tau⁻¹ := by
  exact finiteThreeMomentPairQ_star
    (tripleIndexSlotPermutation I)
    (tripleIndexSlotPermutation_inv I) sigma tau

/-- The concrete two-copy permutation tensors have operator norm at most
one. -/
theorem haarThirdTwirlPermutationQ_norm_le_one
    (I : Type*) [Fintype I] [Nonempty I] [DecidableEq I]
    (sigma tau : Equiv.Perm (Fin 3)) :
    ‖haarThirdTwirlPermutationQ I sigma tau‖ ≤ 1 := by
  classical
  have hunit : haarThirdTwirlPermutationQ I sigma tau ∈
      unitary (CStarMatrix
        ((TripleIndex I) × (TripleIndex I))
        ((TripleIndex I) × (TripleIndex I)) ℂ) := by
    constructor
    · change star (((finiteThreeMomentPairPermutation
          (tripleIndexSlotPermutation I) sigma tau)⁻¹).permMatrix ℂ) *
          ((finiteThreeMomentPairPermutation
            (tripleIndexSlotPermutation I) sigma tau)⁻¹).permMatrix ℂ =
        (1 : Matrix
          ((TripleIndex I) × (TripleIndex I))
          ((TripleIndex I) × (TripleIndex I)) ℂ)
      simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
    · change ((finiteThreeMomentPairPermutation
          (tripleIndexSlotPermutation I) sigma tau)⁻¹).permMatrix ℂ *
          star (((finiteThreeMomentPairPermutation
            (tripleIndexSlotPermutation I) sigma tau)⁻¹).permMatrix ℂ) =
        (1 : Matrix
          ((TripleIndex I) × (TripleIndex I))
          ((TripleIndex I) × (TripleIndex I)) ℂ)
      simp [Matrix.star_eq_conjTranspose, ← Matrix.permMatrix_mul]
  exact le_of_eq (CStarRing.norm_of_mem_unitary hunit)

/-- Literal B.23 Haar-Choi identity for the concrete exact Haar third twirl
on `K` qubits. -/
theorem finiteChoiMatrix_pauliHaarThirdTwirlCP_eq_weingarten
    (K : ℕ) (hD : 3 ≤ 2 ^ K) :
    finiteChoiMatrix (pauliHaarThirdTwirlCP K).toLinearMap =
      finiteThreeMomentWeingartenRawChoi (2 ^ K)
        (haarThirdTwirlPermutationQ (PauliBinaryWord K)) := by
  have hcard : 3 ≤ Fintype.card (PauliBinaryWord K) := by
    simpa [PauliBinaryWord] using hD
  rw [pauliHaarThirdTwirlCP_toLinearMap,
    ← weingartenThirdTwirlMatrixLinearMap_eq_pauliHaarThirdTwirlLinearMap
      K hcard,
    finiteChoiMatrix_weingartenThirdTwirlMatrixLinearMap]
  congr 1
  simp [PauliBinaryWord]

end

end TomographyOracleCore
