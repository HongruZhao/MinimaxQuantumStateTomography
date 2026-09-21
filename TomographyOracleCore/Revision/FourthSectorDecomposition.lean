import TomographyOracleCore.Revision.FourthReplicaPermutations
import TomographyOracleCore.Revision.CliffordFourthOmega
import TomographyOracleCore.BinaryCliffordFourthReplicaReindex

/-!
# The thirty explicit sectors are permutations and Omega-permutations

The finite one-qubit identities are kernel-checked. The arbitrary-block
identification follows from their literal coordinate products and the proved
zero-one formula for the physical Pauli sum Omega.
-/

namespace TomographyOracleCore.Revision.FourthSectorDecomposition

open FourthReplicaPermutations CliffordFourthOmega BinaryCliffordNeutralFourth
open scoped BigOperators

noncomputable section

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofEquiv (Fin 16) (BitVec.equivFin (m := 4)).toEquiv.symm

def fourthTupleAtSite {K : ℕ} (x : FourthIndex (PauliBinaryWord K)) (a : Fin K) :
    FourthIndex (ZMod 2) := (x.1 a, x.2.1 a, x.2.2.1 a, x.2.2.2 a)

@[simp]
theorem coordinates_fourthTupleAtSite
    {K : ℕ} (x : FourthIndex (PauliBinaryWord K)) (a : Fin K) (i : Fin 4) :
    fourthTupleCoordinatesEquiv (ZMod 2) (fourthTupleAtSite x a) i =
      fourthTupleCoordinatesEquiv (PauliBinaryWord K) x i a := by
  fin_cases i <;> rfl

theorem fourthTupleAtSite_permute
    {K : ℕ} (x : FourthIndex (PauliBinaryWord K)) (a : Fin K)
    (pi : Equiv.Perm (Fin 4)) :
    fourthTupleAtSite (permuteFourthTuple pi x) a =
      permuteFourthTuple pi (fourthTupleAtSite x a) := by
  apply (fourthTupleCoordinatesEquiv (ZMod 2)).injective
  funext i
  simp only [coordinates_fourthTupleAtSite, coordinates_permuteFourthTuple]

def localOmegaSupport (x y : FourthIndex (ZMod 2)) : Prop :=
  y.1 + y.2.1 + y.2.2.1 + y.2.2.2 = 0 ∧
    x.1 = y.1 + (x.1 + y.1) ∧ x.2.1 = y.2.1 + (x.1 + y.1) ∧
    x.2.2.1 = y.2.2.1 + (x.1 + y.1) ∧ x.2.2.2 = y.2.2.2 + (x.1 + y.1)

def bitOmegaSupport (x y : QubitFourthReplicaIndex) : Prop :=
  y.cpop.toNat % 2 = 0 ∧ (x = y ∨ x = y ^^^ 15#4)

instance (x y : FourthIndex (ZMod 2)) : Decidable (localOmegaSupport x y) := by
  unfold localOmegaSupport; infer_instance

instance (x y : QubitFourthReplicaIndex) : Decidable (bitOmegaSupport x y) := by
  unfold bitOmegaSupport; infer_instance

theorem localOmegaSupport_iff_bit : ∀ x y : FourthIndex (ZMod 2),
    localOmegaSupport x y ↔
      bitOmegaSupport (zmodTwoFourthEquivBitVecFour x) (zmodTwoFourthEquivBitVecFour y) := by
  decide

theorem fourthOmegaSupport_iff_local
    {K : ℕ} (x y : FourthIndex (PauliBinaryWord K)) :
    fourthOmegaSupport x y ↔ ∀ a : Fin K, localOmegaSupport (fourthTupleAtSite x a)
      (fourthTupleAtSite y a) := by
  simp only [fourthOmegaSupport, fourthWordSum, fourthPauliShiftMatches,
    localOmegaSupport, fourthTupleAtSite, funext_iff, Pi.add_apply, Pi.zero_apply,
    forall_and]

theorem fourthOmegaSupport_iff_bits
    {K : ℕ} (x y : FourthIndex (PauliBinaryWord K)) :
    fourthOmegaSupport x y ↔ ∀ a : Fin K,
      bitOmegaSupport (fourthIndexPauliBinaryWordEquiv K x a)
        (fourthIndexPauliBinaryWordEquiv K y a) := by
  rw [fourthOmegaSupport_iff_local]
  simp only [localOmegaSupport_iff_bit]
  rfl

def bitReplicaPermutation (pi : Equiv.Perm (Fin 4)) (v : QubitFourthReplicaIndex) :
    QubitFourthReplicaIndex :=
  zmodTwoFourthEquivBitVecFour (permuteFourthTuple pi (zmodTwoFourthEquivBitVecFour.symm v))

theorem bitReplicaPermutation_word
    {K : ℕ} (pi : Equiv.Perm (Fin 4)) (x : FourthIndex (PauliBinaryWord K)) (a : Fin K) :
    bitReplicaPermutation pi (fourthIndexPauliBinaryWordEquiv K x a) =
      fourthIndexPauliBinaryWordEquiv K (permuteFourthTuple pi x) a := by
  change zmodTwoFourthEquivBitVecFour
      (permuteFourthTuple pi (zmodTwoFourthEquivBitVecFour.symm
        (zmodTwoFourthEquivBitVecFour (fourthTupleAtSite x a)))) =
    zmodTwoFourthEquivBitVecFour (fourthTupleAtSite (permuteFourthTuple pi x) a)
  rw [Equiv.symm_apply_apply, fourthTupleAtSite_permute]

def sectorPermutationCoordinates : Vector (Vector (Fin 4) 4) 30 := #v[
  #v[0,1,2,3], #v[0,1,3,2], #v[0,2,1,3], #v[0,3,1,2], #v[0,2,3,1], #v[0,3,2,1],
  #v[0,1,2,3], #v[0,1,3,2], #v[0,2,1,3], #v[0,3,1,2], #v[0,2,3,1], #v[0,3,2,1],
  #v[1,0,2,3], #v[1,0,3,2], #v[2,0,1,3], #v[3,0,1,2], #v[2,0,3,1], #v[3,0,2,1],
  #v[1,2,0,3], #v[1,3,0,2], #v[2,1,0,3], #v[3,1,0,2], #v[2,3,0,1], #v[3,2,0,1],
  #v[1,2,3,0], #v[1,3,2,0], #v[2,1,3,0], #v[3,1,2,0], #v[2,3,1,0], #v[3,2,1,0]
]

theorem sectorPermutationCoordinates_bijective : ∀ i : Fin 30,
    Function.Bijective (fun j : Fin 4 => sectorPermutationCoordinates[i][j]) := by
  decide

def sectorPermutation (i : Fin 30) : Equiv.Perm (Fin 4) :=
  Equiv.ofBijective (fun j : Fin 4 => sectorPermutationCoordinates[i][j])
    (sectorPermutationCoordinates_bijective i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Exact certificate for every entry of all thirty one-qubit sectors. -/
theorem sector_membership_permutation_omega : ∀ i : Fin 30,
    ∀ x y : QubitFourthReplicaIndex,
      x ++ y ∈ qubitFourthSector i ↔
        if i.val < 6 then bitOmegaSupport (bitReplicaPermutation (sectorPermutation i) x) y
        else bitReplicaPermutation (sectorPermutation i) x = y := by
  decide

theorem prod_indicator_eq_ite_forall
    {ι : Type*} [Fintype ι] (P : ι → Prop) [DecidablePred P] :
    (∏ i, if P i then (1 : ℂ) else 0) = if ∀ i, P i then 1 else 0 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

def wordSector (K : ℕ) (i : Fin 30) : FourthPauliMatrix K :=
  (fourthCopyBlockReplicaMatrixEquiv K ℂ).symm (qubitFourthSectorR K i)

theorem wordSector_apply (K : ℕ) (i : Fin 30) (x y : FourthIndex (PauliBinaryWord K)) :
    wordSector K i x y =
      if ∀ a : Fin K, fourthIndexPauliBinaryWordEquiv K x a ++
        fourthIndexPauliBinaryWordEquiv K y a ∈ qubitFourthSector i then 1 else 0 := by
  unfold wordSector
  rw [fourthCopyBlockReplicaMatrixEquiv_symm_apply, qubitFourthSectorR_apply_indicator,
    prod_indicator_eq_ite_forall]
  split_ifs <;> rfl

/-- The arbitrary-block sector identification, for the exact matrices used
in the verified Gram table. -/
theorem wordSector_eq_permutation_omega (K : ℕ) (i : Fin 30) :
    wordSector K i =
      if i.val < 6 then fourthReplicaPermutationMatrix (sectorPermutation i) * pauliFourthOmega K
      else fourthReplicaPermutationMatrix (sectorPermutation i) := by
  ext x y
  rw [wordSector_apply]
  simp_rw [sector_membership_permutation_omega]
  by_cases hi : i.val < 6
  · rw [if_pos hi, fourthReplicaPermutationMatrix_mul, pauliFourthOmega_apply]
    simp only [hi, if_true, fourthOmegaSupport_iff_bits, bitReplicaPermutation_word]
  · rw [if_neg hi]
    simp only [hi, if_false, fourthReplicaPermutationMatrix]
    congr 1
    apply propext
    constructor
    · intro h
      have heq : fourthIndexPauliBinaryWordEquiv K (permuteFourthTuple (sectorPermutation i) x) =
          fourthIndexPauliBinaryWordEquiv K y := by
        funext a
        rw [← bitReplicaPermutation_word]
        exact h a
      exact ((fourthIndexPauliBinaryWordEquiv K).injective heq).symm
    · intro h
      subst y
      intro a
      exact bitReplicaPermutation_word _ _ _

/-- Every explicit sector is fixed by every physical Clifford Pauli lift. -/
theorem unitaryFourthConjugation_fixes_wordSector
    (K : ℕ) {g : binarySymplecticGroup K}
    {U : Matrix.unitaryGroup (PauliBinaryWord K) ℂ}
    (hU : IsUnitaryPauliLift K g U) (i : Fin 30) :
    unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) (wordSector K i) =
      wordSector K i := by
  rw [wordSector_eq_permutation_omega]
  split_ifs with hi
  · change ((unitaryTensorFourth U).val *
      (fourthReplicaPermutationMatrix (sectorPermutation i) * pauliFourthOmega K)) *
      (unitaryTensorFourth U).val.conjTranspose = _
    rw [unitaryConjugation_mul]
    change unitaryMatrixConjugationLinearMap (unitaryTensorFourth U)
        (fourthReplicaPermutationMatrix (sectorPermutation i)) *
      unitaryMatrixConjugationLinearMap (unitaryTensorFourth U) (pauliFourthOmega K) = _
    rw [unitaryFourthConjugation_fixes_permutation, unitaryFourthConjugation_fixes_omega K hU]
  · exact unitaryFourthConjugation_fixes_permutation U _

end

end TomographyOracleCore.Revision.FourthSectorDecomposition
