import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import TomographyOracleCore.PeriodicCliffordFourthSectorSynthesis

namespace TomographyOracleCore

noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective

local instance : Fintype QubitFourthReplicaIndex :=
  Fintype.ofFinite _

/-!
# Exact inverse of the thirty-sector fourth-copy Gram matrix

This module turns the already certified association tables and their four
scalar Weingarten identities into a literal matrix inverse.  The proof is a
finite-fiber reindexing: the middle sector is grouped by the two intersection
classes it makes with the left and right sectors.

For an `r`-qubit block the valid nonsingular regime is `3 ≤ r`, because then
the local dimension `2^r` is strictly larger than four.  No Clifford-twirl or
commutant-identification statement is used here.
-/

/-- Pair of intersection classes used to group the middle-sector sum. -/
def qubitFourthAssociationClassPair
    (left right middle : Fin 30) : Fin 5 × Fin 5 :=
  (qubitFourthIntersectionClass left middle,
    qubitFourthIntersectionClass middle right)

/-- The finite fiber of middle sectors with prescribed left and right
intersection classes. -/
def qubitFourthAssociationFiber
    (left right : Fin 30) (a b : Fin 5) : Finset (Fin 30) :=
  Finset.univ.filter fun middle ↦
    qubitFourthAssociationClassPair left right middle = (a, b)

/-- The cardinality of the class-pair fiber is exactly the association count
certified in `PeriodicCliffordFourthSectors`. -/
theorem qubitFourthAssociationFiber_card
    (left right : Fin 30) (a b : Fin 5) :
    (qubitFourthAssociationFiber left right a b).card =
      qubitFourthAssociationCount left right a b := by
  classical
  unfold qubitFourthAssociationFiber qubitFourthAssociationCount
  have hcount := (List.nodup_finRange 30).card_eq_countP
    (P := fun middle : Fin 30 ↦
      qubitFourthAssociationClassPair left right middle = (a, b))
  rw [← List.toFinset_finRange 30, hcount]
  apply List.countP_congr
  intro middle _hmiddle
  simp [qubitFourthAssociationClassPair,
    qubitFourthIntersectionClass, Fin.ext_iff]

/-- Fintype-sum form of the association-table weighted sum. -/
theorem qubitFourthAssociationWeightedSum_eq_fintype
    (h : Nat) (x : ℝ) :
    qubitFourthAssociationWeightedSum h x =
      ∑ a : Fin 5, ∑ b : Fin 5,
        (qubitFourthAssociationNumber h a b : ℝ) *
          qubitFourthWgCoefficient a x * x ^ b.val := by
  unfold qubitFourthAssociationWeightedSum
  simp_rw [Fin.sum_univ_def]

/-- The raw middle-sector convolution is the scalar association weighted sum
in the intersection class of the two endpoints. -/
theorem qubitFourthRawConvolution_eq_associationWeightedSum
    (left right : Fin 30) (x : ℝ) :
    (∑ middle : Fin 30,
        qubitFourthWgCoefficient
            (qubitFourthIntersectionClass left middle) x *
          x ^ qubitFourthIntersectionEntry middle right) =
      qubitFourthAssociationWeightedSum
        (qubitFourthIntersectionEntry left right) x := by
  classical
  let weight : Fin 5 × Fin 5 → ℝ := fun p ↦
    qubitFourthWgCoefficient p.1 x * x ^ p.2.val
  have hfiber := Finset.sum_fiberwise'
    (Finset.univ : Finset (Fin 30))
    (qubitFourthAssociationClassPair left right) weight
  calc
    (∑ middle : Fin 30,
        qubitFourthWgCoefficient
            (qubitFourthIntersectionClass left middle) x *
          x ^ qubitFourthIntersectionEntry middle right) =
        ∑ p : Fin 5 × Fin 5,
          ∑ middle ∈ (Finset.univ : Finset (Fin 30)) with
              qubitFourthAssociationClassPair left right middle = p,
            weight p := by
      symm
      simpa [weight, qubitFourthAssociationClassPair] using hfiber
    _ = ∑ p : Fin 5 × Fin 5,
        (qubitFourthAssociationCount left right p.1 p.2 : ℝ) *
          qubitFourthWgCoefficient p.1 x * x ^ p.2.val := by
      apply Finset.sum_congr rfl
      intro p _hp
      rcases p with ⟨a, b⟩
      change (∑ _middle ∈
          qubitFourthAssociationFiber left right a b,
            weight (a, b)) = _
      rw [Finset.sum_const, nsmul_eq_mul,
        qubitFourthAssociationFiber_card]
      unfold weight
      ring
    _ = ∑ a : Fin 5, ∑ b : Fin 5,
        (qubitFourthAssociationCount left right a b : ℝ) *
          qubitFourthWgCoefficient a x * x ^ b.val := by
      rw [Fintype.sum_prod_type]
    _ = ∑ a : Fin 5, ∑ b : Fin 5,
        (qubitFourthAssociationNumber
            (qubitFourthIntersectionEntry left right) a b : ℝ) *
          qubitFourthWgCoefficient a x * x ^ b.val := by
      apply Finset.sum_congr rfl
      intro a _ha
      apply Finset.sum_congr rfl
      intro b _hb
      rw [qubitFourthAssociationTables_exact left right a b]
    _ = qubitFourthAssociationWeightedSum
        (qubitFourthIntersectionEntry left right) x :=
      (qubitFourthAssociationWeightedSum_eq_fintype
        (qubitFourthIntersectionEntry left right) x).symm

/-- In the literal intersection table, class four occurs exactly on the
diagonal. -/
theorem qubitFourthIntersectionEntry_eq_four_iff : ∀ i j : Fin 30,
    qubitFourthIntersectionEntry i j = 4 ↔ i = j := by
  decide

/-- The scalar convolution is the Kronecker delta for every nonsingular
dimension `x > 4`. -/
theorem qubitFourthAssociationWeightedSum_entry_eq_ite
    {x : ℝ} (hx : 4 < x) (left right : Fin 30) :
    qubitFourthAssociationWeightedSum
        (qubitFourthIntersectionEntry left right) x =
      if left = right then 1 else 0 := by
  obtain ⟨hone, htwo, hthree, hfour⟩ :=
    qubitFourthAssociationWg_inverse hx
  have hb := qubitFourthIntersectionEntry_bounds left right
  have hcases :
      qubitFourthIntersectionEntry left right = 1 ∨
      qubitFourthIntersectionEntry left right = 2 ∨
      qubitFourthIntersectionEntry left right = 3 ∨
      qubitFourthIntersectionEntry left right = 4 := by
    omega
  rcases hcases with hclass | hclass | hclass | hclass
  · rw [hclass, hone]
    have hne : left ≠ right := by
      intro heq
      have := (qubitFourthIntersectionEntry_eq_four_iff left right).2 heq
      omega
    simp [hne]
  · rw [hclass, htwo]
    have hne : left ≠ right := by
      intro heq
      have := (qubitFourthIntersectionEntry_eq_four_iff left right).2 heq
      omega
    simp [hne]
  · rw [hclass, hthree]
    have hne : left ≠ right := by
      intro heq
      have := (qubitFourthIntersectionEntry_eq_four_iff left right).2 heq
      omega
    simp [hne]
  · rw [hclass, hfour]
    have heq : left = right :=
      (qubitFourthIntersectionEntry_eq_four_iff left right).1 hclass
    simp [heq]

/-- Literal real Weingarten matrix before entrywise complex embedding. -/
def qubitFourthRealWgMatrix
    (x : ℝ) : Matrix (Fin 30) (Fin 30) ℝ :=
  fun i j ↦ qubitFourthWgCoefficient
    (qubitFourthIntersectionClass i j) x

@[simp] theorem qubitFourthRealWgMatrix_apply
    (x : ℝ) (i j : Fin 30) :
    qubitFourthRealWgMatrix x i j =
      qubitFourthWgCoefficient
        (qubitFourthIntersectionClass i j) x := rfl

/-- The real Weingarten matrix is symmetric. -/
theorem qubitFourthRealWgMatrix_comm
    (x : ℝ) (i j : Fin 30) :
    qubitFourthRealWgMatrix x i j =
      qubitFourthRealWgMatrix x j i := by
  rw [qubitFourthRealWgMatrix_apply,
    qubitFourthRealWgMatrix_apply,
    qubitFourthIntersectionClass_comm i j]

/-- The association-table certificates give the literal left inverse of the
real Gram matrix. -/
theorem qubitFourthRealWgMatrix_mul_gram
    {x : ℝ} (hx : 4 < x) :
    qubitFourthRealWgMatrix x * qubitFourthGramMatrix x = 1 := by
  ext left right
  simp only [Matrix.mul_apply, qubitFourthRealWgMatrix_apply,
    qubitFourthGramMatrix_apply]
  rw [qubitFourthRawConvolution_eq_associationWeightedSum,
    qubitFourthAssociationWeightedSum_entry_eq_ite hx]
  simp [Matrix.one_apply]

/-- Symmetry upgrades the literal left inverse to a right inverse. -/
theorem qubitFourthGramMatrix_mul_realWg
    {x : ℝ} (hx : 4 < x) :
    qubitFourthGramMatrix x * qubitFourthRealWgMatrix x = 1 := by
  have hleft := qubitFourthRealWgMatrix_mul_gram hx
  ext left right
  calc
    (qubitFourthGramMatrix x * qubitFourthRealWgMatrix x) left right =
        (qubitFourthRealWgMatrix x * qubitFourthGramMatrix x) right left := by
      simp only [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro middle _hmiddle
      rw [qubitFourthGramMatrix_comm x left middle,
        qubitFourthRealWgMatrix_comm x middle right]
      ring
    _ = (1 : Matrix (Fin 30) (Fin 30) ℝ) right left := by
      rw [hleft]
    _ = (1 : Matrix (Fin 30) (Fin 30) ℝ) left right := by
      by_cases h : left = right
      · subst right
        rfl
      · have h' : right ≠ left := fun hrl ↦ h hrl.symm
        simp [h, h']

/-! ## Entrywise complex embedding -/

/-- Entrywise real-to-complex embedding preserves matrix multiplication. -/
theorem qubitFourthComplexOfRealMatrix_mul
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℝ) :
    qubitFourthComplexOfRealMatrix (A * B) =
      qubitFourthComplexOfRealMatrix A *
        qubitFourthComplexOfRealMatrix B := by
  ext i j
  simp [qubitFourthComplexOfRealMatrix, Matrix.mul_apply,
    Complex.ofReal_sum]

/-- Entrywise real-to-complex embedding preserves the identity matrix. -/
theorem qubitFourthComplexOfRealMatrix_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    qubitFourthComplexOfRealMatrix
        (1 : Matrix ι ι ℝ) =
      (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases h : i = j <;>
    simp [qubitFourthComplexOfRealMatrix, Matrix.one_apply, h]

/-- The complex Weingarten matrix is the entrywise embedding of its real
counterpart. -/
theorem qubitFourthComplexWgMatrix_eq_ofReal
    (x : ℝ) :
    qubitFourthComplexWgMatrix x =
      qubitFourthComplexOfRealMatrix
        (qubitFourthRealWgMatrix x) := rfl

/-- The intrinsic sector Gram matrix is the entrywise embedding of the
certified real Gram matrix at `x = 2^r`. -/
theorem qubitFourthSectorRGramMatrix_eq_ofReal
    (r : ℕ) :
    qubitFourthSectorRGramMatrix r =
      qubitFourthComplexOfRealMatrix
        (qubitFourthGramMatrix ((2 : ℝ) ^ r)) := by
  rw [qubitFourthSectorRGramMatrix_eq]
  rfl

/-- Three qubits are exactly enough to put the local dimension strictly
above the singular threshold four. -/
theorem four_lt_two_pow_real_of_three_le
    {r : ℕ} (hr : 3 ≤ r) :
    (4 : ℝ) < (2 : ℝ) ^ r := by
  have hpow : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ r :=
    pow_le_pow_right₀ (by norm_num) hr
  exact (show (4 : ℝ) < (2 : ℝ) ^ 3 by norm_num).trans_le hpow

/-- Literal complex left inverse in the valid block regime. -/
theorem qubitFourthComplexWgMatrix_mul_sectorRGram
    {r : ℕ} (hr : 3 ≤ r) :
    qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) *
        qubitFourthSectorRGramMatrix r = 1 := by
  have hx := four_lt_two_pow_real_of_three_le hr
  rw [qubitFourthComplexWgMatrix_eq_ofReal,
    qubitFourthSectorRGramMatrix_eq_ofReal,
    ← qubitFourthComplexOfRealMatrix_mul,
    qubitFourthRealWgMatrix_mul_gram hx,
    qubitFourthComplexOfRealMatrix_one]

/-- Literal complex right inverse in the valid block regime. -/
theorem qubitFourthSectorRGramMatrix_mul_complexWg
    {r : ℕ} (hr : 3 ≤ r) :
    qubitFourthSectorRGramMatrix r *
        qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) = 1 := by
  have hx := four_lt_two_pow_real_of_three_le hr
  rw [qubitFourthComplexWgMatrix_eq_ofReal,
    qubitFourthSectorRGramMatrix_eq_ofReal,
    ← qubitFourthComplexOfRealMatrix_mul,
    qubitFourthGramMatrix_mul_realWg hx,
    qubitFourthComplexOfRealMatrix_one]

/-- The previously named inverse proposition is now proved from the finite
association-table certificates, with no inverse premise. -/
theorem qubitFourthComplexWgInverseStatement_of_three_le
    {r : ℕ} (hr : 3 ≤ r) :
    QubitFourthComplexWgInverseStatement r := by
  exact ⟨qubitFourthComplexWgMatrix_mul_sectorRGram hr,
    qubitFourthSectorRGramMatrix_mul_complexWg hr⟩

/-- Pointwise formula for the explicit Weingarten synthesis candidate. -/
@[simp] theorem qubitFourthSectorSynthesisCandidate_apply
    (r : ℕ)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ) :
    qubitFourthSectorSynthesisCandidate r X =
      ∑ i : Fin 30, ∑ j : Fin 30,
        (qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) i j *
            qubitFourthSectorAnalysis r X j) •
          qubitFourthSectorR r i := by
  simpa [qubitFourthSectorSynthesisCandidate] using
    qubitFourthSectorSynthesisLinearMap_apply r
      (qubitFourthComplexWgMatrix ((2 : ℝ) ^ r)) X

/-- The explicit synthesis fixes every one of the thirty sector matrices. -/
theorem qubitFourthSectorSynthesisCandidate_on_sector
    {r : ℕ} (hr : 3 ≤ r) (k : Fin 30) :
    qubitFourthSectorSynthesisCandidate r
        (qubitFourthSectorR r k) =
      qubitFourthSectorR r k := by
  unfold qubitFourthSectorSynthesisCandidate
  rw [qubitFourthSectorSynthesisLinearMap_on_sector,
    qubitFourthComplexWgMatrix_mul_sectorRGram hr]
  simp [Matrix.one_apply]

/-- In the valid block regime, the explicit synthesis is an idempotent
projector onto the span of the thirty sector matrices. -/
theorem qubitFourthSectorSynthesisCandidate_idempotent
    {r : ℕ} (hr : 3 ≤ r)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ) :
    qubitFourthSectorSynthesisCandidate r
        (qubitFourthSectorSynthesisCandidate r X) =
      qubitFourthSectorSynthesisCandidate r X := by
  calc
    qubitFourthSectorSynthesisCandidate r
        (qubitFourthSectorSynthesisCandidate r X) =
        qubitFourthSectorSynthesisCandidate r
          (∑ i : Fin 30, ∑ j : Fin 30,
            (qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) i j *
                qubitFourthSectorAnalysis r X j) •
              qubitFourthSectorR r i) := by
      rw [qubitFourthSectorSynthesisCandidate_apply r X]
    _ = ∑ i : Fin 30, ∑ j : Fin 30,
        (qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) i j *
            qubitFourthSectorAnalysis r X j) •
          qubitFourthSectorSynthesisCandidate r
            (qubitFourthSectorR r i) := by
      rw [map_sum]
      simp_rw [map_sum, map_smul]
    _ = ∑ i : Fin 30, ∑ j : Fin 30,
        (qubitFourthComplexWgMatrix ((2 : ℝ) ^ r) i j *
            qubitFourthSectorAnalysis r X j) •
          qubitFourthSectorR r i := by
      simp_rw [qubitFourthSectorSynthesisCandidate_on_sector hr]
    _ = qubitFourthSectorSynthesisCandidate r X :=
      (qubitFourthSectorSynthesisCandidate_apply r X).symm

/-- The residual from the explicit synthesis is Hilbert--Schmidt orthogonal
to every one of the thirty sector matrices. -/
theorem qubitFourthSectorSynthesisCandidate_residual_orthogonal
    {r : ℕ} (hr : 3 ≤ r)
    (X : Matrix (QubitFourthBlockReplicaIndex r)
      (QubitFourthBlockReplicaIndex r) ℂ)
    (l : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR r l)
        (X - qubitFourthSectorSynthesisCandidate r X) = 0 := by
  unfold qubitFourthSectorSynthesisCandidate
  rw [qubitFourthSectorSynthesis_residual_pairing,
    qubitFourthSectorRGramMatrix_mul_complexWg hr]
  simp [Matrix.one_apply]

end

end TomographyOracleCore
