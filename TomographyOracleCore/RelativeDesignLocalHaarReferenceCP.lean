import TomographyOracleCore.FiniteUnitaryThirdTwirlFactorCP
import TomographyOracleCore.FiniteUnitaryThirdTwirlReindex
import TomographyOracleCore.RelativeDesignPauliHaarThirdReference
import TomographyOracleCore.RelativeDesignThreeMomentHaarReferenceScaledCP
import TomographyOracleCore.RelativeDesignThreeMomentLocalEPRRepresentation

namespace TomographyOracleCore

universe u v w

open scoped CStarAlgebra BigOperators Matrix.Norms.L2Operator Kronecker

noncomputable section

local instance localHaarReferenceSpectralOrder : PartialOrder ℂ :=
  CStarAlgebra.spectralOrder ℂ
local instance localHaarReferenceStarOrderedRing : StarOrderedRing ℂ :=
  CStarAlgebra.spectralOrderedRing ℂ

/-! # Local Haar/reference relative-CP estimates

This file supplies the reusable Choi-coordinate bridge from an exact local
third twirl tensored with an untouched identity register to the normalized
local permutation representation used in B.23 and B.26.
-/

/-- Choi coordinates commute with conjugating a CP map by a basis
equivalence. -/
@[simp] theorem finiteChoiMatrix_reindexEquiv_apply
    {I : Type u} {J : Type v} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (e : I ≃ J)
    (Phi : CStarMatrix I I ℂ →CP CStarMatrix I I ℂ)
    (i a j b : J) :
    finiteChoiMatrix
        (CompletelyPositiveMap.reindexEquiv e Phi).toLinearMap
        (i, a) (j, b) =
      finiteChoiMatrix Phi.toLinearMap
        (e.symm i, e.symm a) (e.symm j, e.symm b) := by
  rw [finiteChoiMatrix_apply,
    CompletelyPositiveMap.reindexEquiv_apply]
  have hunit : CStarMatrix.reindexₐ ℂ ℂ e.symm
      (finiteCStarMatrixUnit i j) =
        finiteCStarMatrixUnit (e.symm i) (e.symm j) := by
    apply CStarMatrix.ext
    intro x y
    change (if e x = i ∧ e y = j then 1 else 0) =
      if x = e.symm i ∧ y = e.symm j then 1 else 0
    congr 1
    apply propext
    constructor
    · rintro ⟨hx, hy⟩
      exact ⟨by simpa using congrArg e.symm hx,
        by simpa using congrArg e.symm hy⟩
    · rintro ⟨hx, hy⟩
      exact ⟨by simpa [hx], by simpa [hy]⟩
  rw [hunit]
  rfl

/-- Three replicas of a product, in the subsystem-major representation used
by the B.26 calculation. -/
def tripleIndexABEquiv (A : Type u) (B : Type v) :
    TripleIndex (A × B) ≃ ThreeReplicaAB A B :=
  (tripleIndexProdEquiv A B).trans <|
    (tripleIndexEquivThreeReplica A).prodCongr
      (tripleIndexEquivThreeReplica B)

@[simp] theorem tripleIndexABEquiv_apply
    (A : Type u) (B : Type v) (x : TripleIndex (A × B)) :
    tripleIndexABEquiv A B x =
      (![x.1.1, x.2.1.1, x.2.2.1],
        ![x.1.2, x.2.1.2, x.2.2.2]) := rfl

/-- The two independently introduced tuple/function equivalences are
literally inverse coordinate presentations. -/
theorem tripleIndexEquivThreeReplica_eq_threeReplicaEquivTriple_symm
    (X : Type u) :
    tripleIndexEquivThreeReplica X = (threeReplicaEquivTriple X).symm := by
  apply Equiv.ext
  intro x
  funext q
  fin_cases q <;> rfl

@[simp] theorem tripleIndexEquivThreeReplica_slotPermutation_apply
    (X : Type u) (sigma : Equiv.Perm (Fin 3))
    (x : TripleIndex X) (q : Fin 3) :
    tripleIndexEquivThreeReplica X
        (tripleIndexSlotPermutation X sigma x) q =
      tripleIndexEquivThreeReplica X x (sigma⁻¹ q) := by
  rw [tripleIndexEquivThreeReplica_eq_threeReplicaEquivTriple_symm]
  unfold tripleIndexSlotPermutation
  simp

/-- Two-copy permutation Choi matrices are invariant under an equivalence
that intertwines the underlying replica representations. -/
theorem finiteThreeMomentPairQ_reindex_apply
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : S ≃ T)
    (rhoS : Equiv.Perm (Fin 3) → Equiv.Perm S)
    (rhoT : Equiv.Perm (Fin 3) → Equiv.Perm T)
    (hintertwine : ∀ sigma x, e (rhoS sigma x) = rhoT sigma (e x))
    (sigma tau : Equiv.Perm (Fin 3)) (i a j b : T) :
    finiteThreeMomentPairQ rhoS sigma tau
        (e.symm i, e.symm a) (e.symm j, e.symm b) =
      finiteThreeMomentPairQ rhoT sigma tau (i, a) (j, b) := by
  rw [finiteThreeMomentPairQ_apply, finiteThreeMomentPairQ_apply]
  let epair := e.prodCongr e
  have hinv : ∀ pi x, e ((rhoS pi)⁻¹ x) = (rhoT pi)⁻¹ (e x) := by
    intro pi x
    have hforward : e x = rhoT pi (e ((rhoS pi)⁻¹ x)) := by
      simpa using hintertwine pi ((rhoS pi)⁻¹ x)
    simpa using
      (congrArg (fun y => (rhoT pi)⁻¹ y) hforward).symm
  have hpairInv : epair
      ((finiteThreeMomentPairPermutation rhoS sigma tau)⁻¹
        (e.symm i, e.symm a)) =
      (finiteThreeMomentPairPermutation rhoT sigma tau)⁻¹ (i, a) := by
    change (e ((rhoS sigma)⁻¹ (e.symm i)),
      e ((rhoS tau)⁻¹ (e.symm a))) =
        ((rhoT sigma)⁻¹ i, (rhoT tau)⁻¹ a)
    rw [hinv, hinv]
    simp
  congr 1
  apply propext
  constructor
  · intro h
    calc
      (j, b) = epair (e.symm j, e.symm b) := by simp [epair]
      _ = epair
          ((finiteThreeMomentPairPermutation rhoS sigma tau)⁻¹
            (e.symm i, e.symm a)) := congrArg epair h
      _ = (finiteThreeMomentPairPermutation rhoT sigma tau)⁻¹
          (i, a) := hpairInv
  · intro h
    apply epair.injective
    calc
      epair (e.symm j, e.symm b) = (j, b) := by simp [epair]
      _ = (finiteThreeMomentPairPermutation rhoT sigma tau)⁻¹
          (i, a) := h
      _ = epair
          ((finiteThreeMomentPairPermutation rhoS sigma tau)⁻¹
            (e.symm i, e.symm a)) := hpairInv.symm

/-- Entrywise Choi formula for one tensor-cube conjugation. -/
@[simp] theorem finiteChoiMatrix_finiteUnitaryThirdConjugationCP_apply
    {I : Type u} [Fintype I] [DecidableEq I]
    (U : Matrix.unitaryGroup I ℂ)
    (x a y b : TripleIndex I) :
    finiteChoiMatrix (finiteUnitaryThirdConjugationCP U).toLinearMap
        (x, a) (y, b) =
      finiteUnitaryTensorCube U a x *
        star (finiteUnitaryTensorCube U b y) := by
  let V := finiteUnitaryTensorCube U
  rw [finiteChoiMatrix_apply,
    finiteUnitaryThirdConjugationCP_apply]
  change (V * finiteCStarMatrixUnit x y * star V) a b =
    V a x * star (V b y)
  have hdelta := finite_delta_conjugation_sum
    (fun p q : TripleIndex I ↦ (star V) p q) x a y b
  simpa [CStarMatrix.mul_apply, CStarMatrix.star_apply,
    finiteCStarMatrixUnit_apply] using hdelta

/-- A tensor-cube unitary extended by identity factors entrywise after the
canonical replica-product reassociation. -/
theorem finiteUnitaryTensorCube_tensorId_apply
    {I : Type u} {J : Type v}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (U : Matrix.unitaryGroup I ℂ)
    (x y : TripleIndex (I × J)) :
    finiteUnitaryTensorCube (finiteUnitaryTensorId (J := J) U) x y =
      finiteUnitaryTensorCube U
          ((tripleIndexProdEquiv I J) x).1
          ((tripleIndexProdEquiv I J) y).1 *
        (if ((tripleIndexProdEquiv I J) x).2 =
            ((tripleIndexProdEquiv I J) y).2 then 1 else 0) := by
  rcases x with ⟨⟨x₀, x₀'⟩, ⟨⟨x₁, x₁'⟩, ⟨x₂, x₂'⟩⟩⟩
  rcases y with ⟨⟨y₀, y₀'⟩, ⟨⟨y₁, y₁'⟩, ⟨y₂, y₂'⟩⟩⟩
  unfold finiteUnitaryTensorCube finiteUnitaryTensorId
    matrixTensorThree tripleIndexProdEquiv
  change
    (U.1 x₀ y₀ * (if x₀' = y₀' then 1 else 0)) *
          (U.1 x₁ y₁ * (if x₁' = y₁' then 1 else 0)) *
          (U.1 x₂ y₂ * (if x₂' = y₂' then 1 else 0)) =
      (U.1 x₀ y₀ * U.1 x₁ y₁ * U.1 x₂ y₂) *
        (if (x₀', x₁', x₂') = (y₀', y₁', y₂') then 1 else 0)
  by_cases h₀ : x₀' = y₀' <;>
    by_cases h₁ : x₁' = y₁' <;>
    by_cases h₂ : x₂' = y₂' <;>
    simp [h₀, h₁, h₂, Prod.ext_iff]

/-- Entrywise Choi formula for a normalized finite third-twirl average. -/
theorem finiteChoiMatrix_finiteUnitaryThirdTwirlCP_apply_explicit
    {I : Type u} {E : Type*}
    [Fintype I] [DecidableEq I] [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ)
    (x a y b : TripleIndex I) :
    finiteChoiMatrix (finiteUnitaryThirdTwirlCP U).toLinearMap
        (x, a) (y, b) =
      (((Fintype.card E : ℝ)⁻¹ : ℝ) : ℂ) •
        ∑ e : E, finiteUnitaryTensorCube (U e) a x *
          star (finiteUnitaryTensorCube (U e) b y) := by
  rw [finiteChoiMatrix_apply, finiteUnitaryThirdTwirlCP_apply]
  simp only [CStarMatrix.smul_apply, cstarMatrix_fintypeSum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro e he
  simpa only [finiteChoiMatrix_apply,
    finiteUnitaryThirdConjugationCP_apply] using
    finiteChoiMatrix_finiteUnitaryThirdConjugationCP_apply
      (U e) x a y b

/-- The Choi matrix of a finite local third twirl tensored with the identity
is the acted-on Choi matrix tensored with the untouched raw EPR projector. -/
theorem finiteChoiMatrix_finiteUnitaryThirdTwirlTensorIdCP
    {I : Type u} {J : Type v} {E : Type*}
    [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    [Fintype E] [Nonempty E]
    (U : E → Matrix.unitaryGroup I ℂ) :
    finiteChoiMatrix
        (finiteUnitaryThirdTwirlTensorIdCP (J := J) U).toLinearMap =
      finiteChoiKroneckerReindex (tripleIndexProdEquiv I J)
        (finiteChoiMatrix (finiteUnitaryThirdTwirlCP U).toLinearMap)
        (finiteEPRProjector (I := TripleIndex J)) := by
  classical
  apply CStarMatrix.ext
  intro xa yb
  rcases xa with ⟨x, a⟩
  rcases yb with ⟨y, b⟩
  change finiteChoiMatrix
      (finiteUnitaryThirdTwirlCP
        (fun e ↦ finiteUnitaryTensorId (J := J) (U e))).toLinearMap
        (x, a) (y, b) = _
  rw [finiteChoiMatrix_finiteUnitaryThirdTwirlCP_apply_explicit,
    finiteChoiKroneckerReindex_apply,
    finiteChoiMatrix_finiteUnitaryThirdTwirlCP_apply_explicit]
  simp only [CStarMatrix.smul_apply, finiteEPRProjector]
  simp_rw [finiteUnitaryTensorCube_tensorId_apply]
  by_cases hxa : ((tripleIndexProdEquiv I J) x).2 =
      ((tripleIndexProdEquiv I J) a).2 <;>
    by_cases hyb : ((tripleIndexProdEquiv I J) y).2 =
      ((tripleIndexProdEquiv I J) b).2
  all_goals simp [hxa, hyb, eq_comm]

/-! ## Concrete local Haar maps on a factorized three-register basis -/

/-- Replica-coordinate transport from a `K`-qubit acted register and an
untouched `C` register to the subsystem-major `A,B,C` basis. -/
def pauliHaarABReplicaEquiv
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    (idx : PauliBinaryWord K ≃ A × B) :
    TripleIndex (PauliBinaryWord K × C) ≃ ThreeReplicaABC A B C :=
  (tripleIndexCongr (idx.prodCongr (Equiv.refl C))).trans
    (tripleIndexABCEquiv A B C)

/-- Exact local Haar third twirl on `AB`, with `C` untouched, transported
to the common B.26 basis.  Its finite Clifford implementation is an exact
third design, so this is an actual Haar map rather than a supplied premise. -/
def finiteThreeMomentABHaarCP
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ A × B) :
    CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ :=
  CompletelyPositiveMap.reindexEquiv
    (pauliHaarABReplicaEquiv K A B C idx)
    (pauliHaarThirdTwirlTensorIdCP K C)

/-- Replica-coordinate transport from a `K`-qubit acted `BC` register and
an untouched `A` register to the common subsystem-major `A,B,C` basis. -/
def pauliHaarBCReplicaEquiv
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    (idx : PauliBinaryWord K ≃ B × C) :
    TripleIndex (PauliBinaryWord K × A) ≃ ThreeReplicaABC A B C :=
  (tripleIndexCongr (idx.prodCongr (Equiv.refl A))).trans
    (tripleIndexBCAEquivABC A B C)

/-- Exact local Haar third twirl on `BC`, with `A` untouched, transported
to the common B.26 basis. -/
def finiteThreeMomentBCHaarCP
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ B × C) :
    CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ →CP
      CStarMatrix (ThreeReplicaABC A B C) (ThreeReplicaABC A B C) ℂ :=
  CompletelyPositiveMap.reindexEquiv
    (pauliHaarBCReplicaEquiv K A B C idx)
    (pauliHaarThirdTwirlTensorIdCP K A)

theorem card_AB_eq_two_pow_of_pauliEquiv
    (K : ℕ) (A : Type u) (B : Type v)
    [Fintype A] [Fintype B]
    (idx : PauliBinaryWord K ≃ A × B) :
    Fintype.card A * Fintype.card B = 2 ^ K := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr idx).symm.trans (by simp [PauliBinaryWord])

theorem card_BC_eq_two_pow_of_pauliEquiv
    (K : ℕ) (B : Type v) (C : Type w)
    [Fintype B] [Fintype C]
    (idx : PauliBinaryWord K ≃ B × C) :
    Fintype.card B * Fintype.card C = 2 ^ K := by
  rw [← Fintype.card_prod]
  exact (Fintype.card_congr idx).symm.trans (by simp [PauliBinaryWord])

/-- The acted replica basis change obtained by applying the physical basis
equivalence independently in each slot and then regrouping by subsystem. -/
def pauliHaarABActedReplicaEquiv
    (K : ℕ) (A : Type u) (B : Type v)
    (idx : PauliBinaryWord K ≃ A × B) :
    TripleIndex (PauliBinaryWord K) ≃ ThreeReplicaAB A B :=
  (tripleIndexCongr idx).trans (tripleIndexABEquiv A B)

@[simp] theorem pauliHaarABActedReplicaEquiv_fst_apply
    (K : ℕ) (A : Type u) (B : Type v)
    (idx : PauliBinaryWord K ≃ A × B)
    (x : TripleIndex (PauliBinaryWord K)) (q : Fin 3) :
    (pauliHaarABActedReplicaEquiv K A B idx x).1 q =
      (idx (tripleIndexEquivThreeReplica (PauliBinaryWord K) x q)).1 := by
  fin_cases q <;> rfl

@[simp] theorem pauliHaarABActedReplicaEquiv_snd_apply
    (K : ℕ) (A : Type u) (B : Type v)
    (idx : PauliBinaryWord K ≃ A × B)
    (x : TripleIndex (PauliBinaryWord K)) (q : Fin 3) :
    (pauliHaarABActedReplicaEquiv K A B idx x).2 q =
      (idx (tripleIndexEquivThreeReplica (PauliBinaryWord K) x q)).2 := by
  fin_cases q <;> rfl

/-- The acted replica basis change intertwines the two literal
representations of replica-slot permutations. -/
theorem pauliHaarABActedReplicaEquiv_intertwine
    (K : ℕ) (A : Type u) (B : Type v)
    (idx : PauliBinaryWord K ≃ A × B)
    (sigma : Equiv.Perm (Fin 3))
    (x : TripleIndex (PauliBinaryWord K)) :
    pauliHaarABActedReplicaEquiv K A B idx
        (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x) =
      threeReplicaABSlotPermutation A B sigma
        (pauliHaarABActedReplicaEquiv K A B idx x) := by
  apply Prod.ext
  · funext q
    change
      (pauliHaarABActedReplicaEquiv K A B idx
        (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x)).1 q =
      (pauliHaarABActedReplicaEquiv K A B idx x).1 (sigma⁻¹ q)
    rw [pauliHaarABActedReplicaEquiv_fst_apply]
    rw [tripleIndexEquivThreeReplica_slotPermutation_apply]
    exact (pauliHaarABActedReplicaEquiv_fst_apply
      K A B idx x (sigma⁻¹ q)).symm
  · funext q
    change
      (pauliHaarABActedReplicaEquiv K A B idx
        (tripleIndexSlotPermutation (PauliBinaryWord K) sigma x)).2 q =
      (pauliHaarABActedReplicaEquiv K A B idx x).2 (sigma⁻¹ q)
    rw [pauliHaarABActedReplicaEquiv_snd_apply]
    rw [tripleIndexEquivThreeReplica_slotPermutation_apply]
    exact (pauliHaarABActedReplicaEquiv_snd_apply
      K A B idx x (sigma⁻¹ q)).symm

/-- Raw EPR Choi coordinates are invariant under simultaneous basis
transport on the physical and reference copies. -/
theorem finiteEPRProjector_reindex_apply
    {S : Type u} {T : Type v}
    [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]
    (e : S ≃ T) (i a j b : T) :
    finiteEPRProjector (I := S)
        (e.symm i, e.symm a) (e.symm j, e.symm b) =
      finiteEPRProjector (I := T) (i, a) (j, b) := by
  simp [finiteEPRProjector]

/-- Splitting the transported global replica basis into acted and untouched
coordinates agrees with first splitting the target subsystem-major basis. -/
theorem pauliHaarABReplicaEquiv_split_symm
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    (idx : PauliBinaryWord K ≃ A × B)
    (x : ThreeReplicaABC A B C) :
    tripleIndexProdEquiv (PauliBinaryWord K) C
        ((pauliHaarABReplicaEquiv K A B C idx).symm x) =
      ((pauliHaarABActedReplicaEquiv K A B idx).symm
          ((threeReplicaABCEquivAB_C A B C x).1),
        (tripleIndexEquivThreeReplica C).symm
          ((threeReplicaABCEquivAB_C A B C x).2)) := by
  rfl

/-- The corresponding split identity for a local `BC` acted register. -/
theorem pauliHaarBCReplicaEquiv_split_symm
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    (idx : PauliBinaryWord K ≃ B × C)
    (x : ThreeReplicaABC A B C) :
    tripleIndexProdEquiv (PauliBinaryWord K) A
        ((pauliHaarBCReplicaEquiv K A B C idx).symm x) =
      ((pauliHaarABActedReplicaEquiv K B C idx).symm
          ((threeReplicaABCEquivBC_A A B C x).1),
        (tripleIndexEquivThreeReplica A).symm
          ((threeReplicaABCEquivBC_A A B C x).2)) := by
  rfl

/-- One local Haar permutation-Choi term, after tensoring by the untouched
raw EPR factor and transporting coordinates, is the normalized local B.23
representation times the untouched three-replica dimension. -/
theorem pauliHaarABPermutationQ_EPR_reindex_apply
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ A × B)
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    finiteChoiKroneckerReindex (tripleIndexProdEquiv (PauliBinaryWord K) C)
        (haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau)
        (finiteEPRProjector (I := TripleIndex C))
        ((pauliHaarABReplicaEquiv K A B C idx).symm i,
          (pauliHaarABReplicaEquiv K A B C idx).symm a)
        ((pauliHaarABReplicaEquiv K A B C idx).symm j,
          (pauliHaarABReplicaEquiv K A B C idx).symm b) =
      ((Fintype.card (ThreeReplica C) : ℝ) •
        finiteThreeMomentABLocalChoiQ A B C sigma tau)
          (i, a) (j, b) := by
  classical
  rw [finiteChoiKroneckerReindex_apply]
  rw [CStarMatrix.smul_apply]
  change _ = (Fintype.card (ThreeReplica C) : ℂ) *
    finiteChoiKroneckerReindex (threeReplicaABCEquivAB_C A B C)
      (finiteThreeMomentPairQ (threeReplicaABSlotPermutation A B) sigma tau)
      (finiteNormalizedEPRProjector (T := ThreeReplica C))
          (i, a) (j, b)
  rw [finiteChoiKroneckerReindex_apply]
  unfold finiteNormalizedEPRProjector
  rw [CStarMatrix.smul_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [pauliHaarABReplicaEquiv_split_symm K A B C idx i,
    pauliHaarABReplicaEquiv_split_symm K A B C idx a,
    pauliHaarABReplicaEquiv_split_symm K A B C idx j,
    pauliHaarABReplicaEquiv_split_symm K A B C idx b]
  rw [haarThirdTwirlPermutationQ]
  rw [finiteThreeMomentPairQ_reindex_apply
    (pauliHaarABActedReplicaEquiv K A B idx)
    (tripleIndexSlotPermutation (PauliBinaryWord K))
    (threeReplicaABSlotPermutation A B)
    (pauliHaarABActedReplicaEquiv_intertwine K A B idx)
    sigma tau]
  rw [finiteEPRProjector_reindex_apply
    (tripleIndexEquivThreeReplica C)]
  let qval : ℂ := finiteThreeMomentPairQ
    (threeReplicaABSlotPermutation A B) sigma tau
      (((threeReplicaABCEquivAB_C A B C) i).1,
        ((threeReplicaABCEquivAB_C A B C) a).1)
      (((threeReplicaABCEquivAB_C A B C) j).1,
        ((threeReplicaABCEquivAB_C A B C) b).1)
  let eval : ℂ := finiteEPRProjector
      (((threeReplicaABCEquivAB_C A B C) i).2,
        ((threeReplicaABCEquivAB_C A B C) a).2)
      (((threeReplicaABCEquivAB_C A B C) j).2,
        ((threeReplicaABCEquivAB_C A B C) b).2)
  change qval * eval = (Fintype.card (ThreeReplica C) : ℂ) *
    (qval * ((((Fintype.card (ThreeReplica C) : ℝ)⁻¹ : ℝ) : ℂ) * eval))
  have hscale : (Fintype.card (ThreeReplica C) : ℂ) *
      ((((Fintype.card (ThreeReplica C) : ℝ)⁻¹ : ℝ) : ℂ)) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  calc
    qval * eval = 1 * (qval * eval) := by ring
    _ = ((Fintype.card (ThreeReplica C) : ℂ) *
        ((((Fintype.card (ThreeReplica C) : ℝ)⁻¹ : ℝ) : ℂ))) *
          (qval * eval) := by rw [hscale]
    _ = _ := by ring

/-- Product-form corollary of the preceding term identity, tailored for
rewriting under the finite Weingarten sums. -/
theorem pauliHaarABPermutationQ_EPR_product_apply
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ A × B)
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau
        (((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm i)).1,
         ((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm a)).1)
        (((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm j)).1,
         ((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm b)).1) *
      finiteEPRProjector
        (((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm i)).2,
         ((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm a)).2)
        (((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm j)).2,
         ((tripleIndexProdEquiv (PauliBinaryWord K) C)
          ((pauliHaarABReplicaEquiv K A B C idx).symm b)).2) =
      ((Fintype.card (ThreeReplica C) : ℝ) •
        finiteThreeMomentABLocalChoiQ A B C sigma tau)
          (i, a) (j, b) := by
  simpa only [finiteChoiKroneckerReindex_apply] using
    pauliHaarABPermutationQ_EPR_reindex_apply
      K A B C idx sigma tau i a j b

/-- Exact scaled Weingarten Choi formula for the concrete local `AB` Haar
map.  The common scalar is precisely the dimension of the untouched
three-replica register. -/
theorem finiteThreeMomentABHaarCP_choi
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ A × B)
    (hD : 3 ≤ 2 ^ K) :
    finiteChoiMatrix
        (finiteThreeMomentABHaarCP K A B C idx).toLinearMap =
      (Fintype.card (ThreeReplica C) : ℝ) •
        finiteThreeMomentWeingartenRawChoi
          (Fintype.card A * Fintype.card B)
          (finiteThreeMomentABLocalChoiQ A B C) := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  unfold finiteThreeMomentABHaarCP
  rw [finiteChoiMatrix_reindexEquiv_apply]
  unfold pauliHaarThirdTwirlTensorIdCP
  rw [finiteChoiMatrix_finiteUnitaryThirdTwirlTensorIdCP]
  rw [finiteChoiKroneckerReindex_apply]
  rw [show finiteUnitaryThirdTwirlCP (pauliCosetCliffordUnitary K) =
      pauliHaarThirdTwirlCP K by rfl]
  rw [finiteChoiMatrix_pauliHaarThirdTwirlCP_eq_weingarten K hD]
  rw [card_AB_eq_two_pow_of_pauliEquiv K A B idx]
  unfold finiteThreeMomentWeingartenRawChoi
  simp only [CStarMatrix.smul_apply, cstarMatrix_fintypeSum_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  let scale : ℂ := ((((2 ^ K : ℕ) : ℝ) ^ 3)⁻¹ : ℝ)
  let coeff (sigma tau : Equiv.Perm (Fin 3)) : ℂ :=
    normalizedWeingartenThree (2 ^ K) sigma tau
  let cardC : ℂ := ((Fintype.card (ThreeReplica C) : ℝ) : ℂ)
  let acted (sigma tau : Equiv.Perm (Fin 3)) : ℂ :=
    haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau
      (((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm i)).1,
       ((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm a)).1)
      (((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm j)).1,
       ((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm b)).1)
  let untouched : ℂ := finiteEPRProjector
      (((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm i)).2,
       ((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm a)).2)
      (((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm j)).2,
       ((tripleIndexProdEquiv (PauliBinaryWord K) C)
        ((pauliHaarABReplicaEquiv K A B C idx).symm b)).2)
  let localTerm (sigma tau : Equiv.Perm (Fin 3)) : ℂ :=
    finiteThreeMomentABLocalChoiQ A B C sigma tau (i, a) (j, b)
  change (scale * ∑ sigma, ∑ tau, coeff sigma tau * acted sigma tau) *
      untouched =
    cardC *
      (scale * ∑ sigma, ∑ tau, coeff sigma tau * localTerm sigma tau)
  have hprod (sigma tau : Equiv.Perm (Fin 3)) :
      acted sigma tau * untouched =
        cardC * localTerm sigma tau := by
    dsimp [acted, untouched, localTerm]
    simpa only [CStarMatrix.smul_apply, Complex.real_smul, smul_eq_mul] using
      pauliHaarABPermutationQ_EPR_product_apply
        K A B C idx sigma tau i a j b
  have hterm (sigma tau : Equiv.Perm (Fin 3)) :
      (coeff sigma tau * acted sigma tau) * untouched =
        coeff sigma tau *
          (cardC * localTerm sigma tau) := by
    rw [mul_assoc, hprod]
  rw [mul_assoc, Finset.sum_mul]
  simp_rw [Finset.sum_mul, hterm]
  have hfactor (sigma tau : Equiv.Perm (Fin 3)) :
      coeff sigma tau * (cardC * localTerm sigma tau) =
        cardC * (coeff sigma tau * localTerm sigma tau) := by ring
  simp_rw [hfactor, ← Finset.mul_sum]
  ring

/-! ## The mirrored local `BC` endpoint -/

/-- The transported local `BC` permutation-Choi term, including its
untouched raw `A` EPR factor. -/
theorem pauliHaarBCPermutationQ_EPR_reindex_apply
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ B × C)
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    finiteChoiKroneckerReindex (tripleIndexProdEquiv (PauliBinaryWord K) A)
        (haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau)
        (finiteEPRProjector (I := TripleIndex A))
        ((pauliHaarBCReplicaEquiv K A B C idx).symm i,
          (pauliHaarBCReplicaEquiv K A B C idx).symm a)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm j,
          (pauliHaarBCReplicaEquiv K A B C idx).symm b) =
      ((Fintype.card (ThreeReplica A) : ℝ) •
        finiteThreeMomentBCLocalChoiQ A B C sigma tau)
          (i, a) (j, b) := by
  classical
  rw [finiteChoiKroneckerReindex_apply]
  rw [CStarMatrix.smul_apply]
  change _ = (Fintype.card (ThreeReplica A) : ℂ) *
    finiteChoiKroneckerReindex (threeReplicaABCEquivBC_A A B C)
      (finiteThreeMomentPairQ (threeReplicaABSlotPermutation B C) sigma tau)
      (finiteNormalizedEPRProjector (T := ThreeReplica A))
      (i, a) (j, b)
  rw [finiteChoiKroneckerReindex_apply]
  unfold finiteNormalizedEPRProjector
  rw [CStarMatrix.smul_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  rw [pauliHaarBCReplicaEquiv_split_symm K A B C idx i,
    pauliHaarBCReplicaEquiv_split_symm K A B C idx a,
    pauliHaarBCReplicaEquiv_split_symm K A B C idx j,
    pauliHaarBCReplicaEquiv_split_symm K A B C idx b]
  rw [haarThirdTwirlPermutationQ]
  rw [finiteThreeMomentPairQ_reindex_apply
    (pauliHaarABActedReplicaEquiv K B C idx)
    (tripleIndexSlotPermutation (PauliBinaryWord K))
    (threeReplicaABSlotPermutation B C)
    (pauliHaarABActedReplicaEquiv_intertwine K B C idx)
    sigma tau]
  rw [finiteEPRProjector_reindex_apply
    (tripleIndexEquivThreeReplica A)]
  let qval : ℂ := finiteThreeMomentPairQ
    (threeReplicaABSlotPermutation B C) sigma tau
      (((threeReplicaABCEquivBC_A A B C) i).1,
        ((threeReplicaABCEquivBC_A A B C) a).1)
      (((threeReplicaABCEquivBC_A A B C) j).1,
        ((threeReplicaABCEquivBC_A A B C) b).1)
  let eval : ℂ := finiteEPRProjector
      (((threeReplicaABCEquivBC_A A B C) i).2,
        ((threeReplicaABCEquivBC_A A B C) a).2)
      (((threeReplicaABCEquivBC_A A B C) j).2,
        ((threeReplicaABCEquivBC_A A B C) b).2)
  change qval * eval = (Fintype.card (ThreeReplica A) : ℂ) *
    (qval * ((((Fintype.card (ThreeReplica A) : ℝ)⁻¹ : ℝ) : ℂ) * eval))
  have hscale : (Fintype.card (ThreeReplica A) : ℂ) *
      ((((Fintype.card (ThreeReplica A) : ℝ)⁻¹ : ℝ) : ℂ)) = 1 := by
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  calc
    qval * eval = 1 * (qval * eval) := by ring
    _ = ((Fintype.card (ThreeReplica A) : ℂ) *
        ((((Fintype.card (ThreeReplica A) : ℝ)⁻¹ : ℝ) : ℂ))) *
          (qval * eval) := by rw [hscale]
    _ = _ := by ring

/-- Product-form local `BC` transport for rewriting finite Weingarten
sums entrywise. -/
theorem pauliHaarBCPermutationQ_EPR_product_apply
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ B × C)
    (sigma tau : Equiv.Perm (Fin 3))
    (i a j b : ThreeReplicaABC A B C) :
    haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau
        (((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm i)).1,
         ((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm a)).1)
        (((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm j)).1,
         ((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm b)).1) *
      finiteEPRProjector
        (((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm i)).2,
         ((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm a)).2)
        (((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm j)).2,
         ((tripleIndexProdEquiv (PauliBinaryWord K) A)
          ((pauliHaarBCReplicaEquiv K A B C idx).symm b)).2) =
      ((Fintype.card (ThreeReplica A) : ℝ) •
        finiteThreeMomentBCLocalChoiQ A B C sigma tau)
          (i, a) (j, b) := by
  simpa only [finiteChoiKroneckerReindex_apply] using
    pauliHaarBCPermutationQ_EPR_reindex_apply
      K A B C idx sigma tau i a j b

/-- Exact scaled Weingarten Choi formula for the concrete local `BC` Haar
map, with common scalar equal to the untouched `A` replica dimension. -/
theorem finiteThreeMomentBCHaarCP_choi
    (K : ℕ) (A : Type u) (B : Type v) (C : Type w)
    [Fintype A] [Fintype B] [Fintype C] [Nonempty A]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ B × C)
    (hD : 3 ≤ 2 ^ K) :
    finiteChoiMatrix
        (finiteThreeMomentBCHaarCP K A B C idx).toLinearMap =
      (Fintype.card (ThreeReplica A) : ℝ) •
        finiteThreeMomentWeingartenRawChoi
          (Fintype.card B * Fintype.card C)
          (finiteThreeMomentBCLocalChoiQ A B C) := by
  classical
  apply CStarMatrix.ext
  intro ia jb
  rcases ia with ⟨i, a⟩
  rcases jb with ⟨j, b⟩
  unfold finiteThreeMomentBCHaarCP
  rw [finiteChoiMatrix_reindexEquiv_apply]
  unfold pauliHaarThirdTwirlTensorIdCP
  rw [finiteChoiMatrix_finiteUnitaryThirdTwirlTensorIdCP]
  rw [finiteChoiKroneckerReindex_apply]
  rw [show finiteUnitaryThirdTwirlCP (pauliCosetCliffordUnitary K) =
      pauliHaarThirdTwirlCP K by rfl]
  rw [finiteChoiMatrix_pauliHaarThirdTwirlCP_eq_weingarten K hD]
  rw [card_BC_eq_two_pow_of_pauliEquiv K B C idx]
  unfold finiteThreeMomentWeingartenRawChoi
  simp only [CStarMatrix.smul_apply, cstarMatrix_fintypeSum_apply]
  simp only [Complex.real_smul, smul_eq_mul]
  let scale : ℂ := ((((2 ^ K : ℕ) : ℝ) ^ 3)⁻¹ : ℝ)
  let coeff (sigma tau : Equiv.Perm (Fin 3)) : ℂ :=
    normalizedWeingartenThree (2 ^ K) sigma tau
  let cardC : ℂ := ((Fintype.card (ThreeReplica A) : ℝ) : ℂ)
  let acted (sigma tau : Equiv.Perm (Fin 3)) : ℂ :=
    haarThirdTwirlPermutationQ (PauliBinaryWord K) sigma tau
      (((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm i)).1,
       ((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm a)).1)
      (((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm j)).1,
       ((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm b)).1)
  let untouched : ℂ := finiteEPRProjector
      (((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm i)).2,
       ((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm a)).2)
      (((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm j)).2,
       ((tripleIndexProdEquiv (PauliBinaryWord K) A)
        ((pauliHaarBCReplicaEquiv K A B C idx).symm b)).2)
  let localTerm (sigma tau : Equiv.Perm (Fin 3)) : ℂ :=
    finiteThreeMomentBCLocalChoiQ A B C sigma tau (i, a) (j, b)
  change (scale * ∑ sigma, ∑ tau, coeff sigma tau * acted sigma tau) *
      untouched =
    cardC *
      (scale * ∑ sigma, ∑ tau, coeff sigma tau * localTerm sigma tau)
  have hprod (sigma tau : Equiv.Perm (Fin 3)) :
      acted sigma tau * untouched =
        cardC * localTerm sigma tau := by
    dsimp [acted, untouched, localTerm]
    simpa only [CStarMatrix.smul_apply, Complex.real_smul, smul_eq_mul] using
      pauliHaarBCPermutationQ_EPR_product_apply
        K A B C idx sigma tau i a j b
  have hterm (sigma tau : Equiv.Perm (Fin 3)) :
      (coeff sigma tau * acted sigma tau) * untouched =
        coeff sigma tau *
          (cardC * localTerm sigma tau) := by
    rw [mul_assoc, hprod]
  rw [mul_assoc, Finset.sum_mul]
  simp_rw [Finset.sum_mul, hterm]
  have hfactor (sigma tau : Equiv.Perm (Fin 3)) :
      coeff sigma tau * (cardC * localTerm sigma tau) =
        cardC * (coeff sigma tau * localTerm sigma tau) := by ring
  simp_rw [hfactor, ← Finset.mul_sum]
  ring

/-! ## Concrete local Haar/reference relative-CP estimates -/

/-- B.21 for the concrete local `AB` Haar twirl against its existing
approximate-Haar reference, with no supplied Choi identity. -/
theorem relativeCPApproximation_finiteThreeMomentABHaar_reference
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ A × B)
    (hK : 18 ≤ 2 ^ K) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card A * Fintype.card B : ℕ) : ℝ) - 9))
      (finiteThreeMomentABHaarCP K A B C idx).toLinearMap
      (finiteThreeMomentABReferenceCP A B C).toLinearMap := by
  have hD : 18 ≤ Fintype.card A * Fintype.card B := by
    rw [card_AB_eq_two_pow_of_pauliEquiv K A B idx]
    exact hK
  apply relativeCPApproximation_haar_of_scaled_weingartenChoi
    (Fintype.card A * Fintype.card B) hD
    (finiteThreeMomentABLocalChoiQ A B C)
    (finiteThreeMomentABLocalChoiQ_norm_le_one A B C)
    (finiteThreeMomentABLocalChoiQ_mul A B C)
    (finiteThreeMomentABLocalChoiQ_star A B C)
    (Fintype.card (ThreeReplica C) : ℝ) (by positivity)
    (finiteThreeMomentABHaarCP K A B C idx)
    (finiteThreeMomentABReferenceCP A B C)
  · calc
      finiteChoiMatrix
          (finiteThreeMomentABHaarCP K A B C idx).toLinearMap =
        (Fintype.card (ThreeReplica C) : ℝ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        finiteThreeMomentABHaarCP_choi K A B C idx (by omega)
      _ = ((Fintype.card (ThreeReplica C) : ℝ) : ℂ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _
  · rw [finiteThreeMomentABReferenceCP_choi]
    calc
      finiteThreeMomentABReferenceChoi A B C =
        (Fintype.card (ThreeReplica C) : ℝ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        finiteThreeMomentABReferenceChoi_eq_card_smul_approximateHaarRawChoi
          A B C
      _ = ((Fintype.card (ThreeReplica C) : ℝ) : ℂ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _

/-- B.22 in the reverse local `AB` reference-to-Haar orientation. -/
theorem relativeCPApproximation_finiteThreeMomentABReference_haar
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ A × B)
    (hK : 18 ≤ 2 ^ K) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card A * Fintype.card B : ℕ) : ℝ) - 18))
      (finiteThreeMomentABReferenceCP A B C).toLinearMap
      (finiteThreeMomentABHaarCP K A B C idx).toLinearMap := by
  have hD : 18 ≤ Fintype.card A * Fintype.card B := by
    rw [card_AB_eq_two_pow_of_pauliEquiv K A B idx]
    exact hK
  apply relativeCPApproximation_reference_of_scaled_weingartenChoi
    (Fintype.card A * Fintype.card B) hD
    (finiteThreeMomentABLocalChoiQ A B C)
    (finiteThreeMomentABLocalChoiQ_norm_le_one A B C)
    (finiteThreeMomentABLocalChoiQ_mul A B C)
    (finiteThreeMomentABLocalChoiQ_star A B C)
    (Fintype.card (ThreeReplica C) : ℝ) (by positivity)
    (finiteThreeMomentABHaarCP K A B C idx)
    (finiteThreeMomentABReferenceCP A B C)
  · calc
      finiteChoiMatrix
          (finiteThreeMomentABHaarCP K A B C idx).toLinearMap =
        (Fintype.card (ThreeReplica C) : ℝ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        finiteThreeMomentABHaarCP_choi K A B C idx (by omega)
      _ = ((Fintype.card (ThreeReplica C) : ℝ) : ℂ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _
  · rw [finiteThreeMomentABReferenceCP_choi]
    calc
      finiteThreeMomentABReferenceChoi A B C =
        (Fintype.card (ThreeReplica C) : ℝ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        finiteThreeMomentABReferenceChoi_eq_card_smul_approximateHaarRawChoi
          A B C
      _ = ((Fintype.card (ThreeReplica C) : ℝ) : ℂ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card A * Fintype.card B)
            (finiteThreeMomentABLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _

/-- B.21 for the concrete local `BC` Haar twirl against its reference. -/
theorem relativeCPApproximation_finiteThreeMomentBCHaar_reference
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ B × C)
    (hK : 18 ≤ 2 ^ K) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card B * Fintype.card C : ℕ) : ℝ) - 9))
      (finiteThreeMomentBCHaarCP K A B C idx).toLinearMap
      (finiteThreeMomentBCReferenceCP A B C).toLinearMap := by
  have hD : 18 ≤ Fintype.card B * Fintype.card C := by
    rw [card_BC_eq_two_pow_of_pauliEquiv K B C idx]
    exact hK
  apply relativeCPApproximation_haar_of_scaled_weingartenChoi
    (Fintype.card B * Fintype.card C) hD
    (finiteThreeMomentBCLocalChoiQ A B C)
    (finiteThreeMomentBCLocalChoiQ_norm_le_one A B C)
    (finiteThreeMomentBCLocalChoiQ_mul A B C)
    (finiteThreeMomentBCLocalChoiQ_star A B C)
    (Fintype.card (ThreeReplica A) : ℝ) (by positivity)
    (finiteThreeMomentBCHaarCP K A B C idx)
    (finiteThreeMomentBCReferenceCP A B C)
  · calc
      finiteChoiMatrix
          (finiteThreeMomentBCHaarCP K A B C idx).toLinearMap =
        (Fintype.card (ThreeReplica A) : ℝ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        finiteThreeMomentBCHaarCP_choi K A B C idx (by omega)
      _ = ((Fintype.card (ThreeReplica A) : ℝ) : ℂ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _
  · rw [finiteThreeMomentBCReferenceCP_choi]
    calc
      finiteThreeMomentBCReferenceChoi A B C =
        (Fintype.card (ThreeReplica A) : ℝ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        finiteThreeMomentBCReferenceChoi_eq_card_smul_approximateHaarRawChoi
          A B C
      _ = ((Fintype.card (ThreeReplica A) : ℝ) : ℂ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _

/-- B.22 in the reverse local `BC` reference-to-Haar orientation. -/
theorem relativeCPApproximation_finiteThreeMomentBCReference_haar
    (K : ℕ) (A B C : Type u)
    [Fintype A] [Fintype B] [Fintype C]
    [Nonempty A] [Nonempty B] [Nonempty C]
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (idx : PauliBinaryWord K ≃ B × C)
    (hK : 18 ≤ 2 ^ K) :
    RelativeCPApproximation
      (9 / (2 * ((Fintype.card B * Fintype.card C : ℕ) : ℝ) - 18))
      (finiteThreeMomentBCReferenceCP A B C).toLinearMap
      (finiteThreeMomentBCHaarCP K A B C idx).toLinearMap := by
  have hD : 18 ≤ Fintype.card B * Fintype.card C := by
    rw [card_BC_eq_two_pow_of_pauliEquiv K B C idx]
    exact hK
  apply relativeCPApproximation_reference_of_scaled_weingartenChoi
    (Fintype.card B * Fintype.card C) hD
    (finiteThreeMomentBCLocalChoiQ A B C)
    (finiteThreeMomentBCLocalChoiQ_norm_le_one A B C)
    (finiteThreeMomentBCLocalChoiQ_mul A B C)
    (finiteThreeMomentBCLocalChoiQ_star A B C)
    (Fintype.card (ThreeReplica A) : ℝ) (by positivity)
    (finiteThreeMomentBCHaarCP K A B C idx)
    (finiteThreeMomentBCReferenceCP A B C)
  · calc
      finiteChoiMatrix
          (finiteThreeMomentBCHaarCP K A B C idx).toLinearMap =
        (Fintype.card (ThreeReplica A) : ℝ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        finiteThreeMomentBCHaarCP_choi K A B C idx (by omega)
      _ = ((Fintype.card (ThreeReplica A) : ℝ) : ℂ) •
          finiteThreeMomentWeingartenRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _
  · rw [finiteThreeMomentBCReferenceCP_choi]
    calc
      finiteThreeMomentBCReferenceChoi A B C =
        (Fintype.card (ThreeReplica A) : ℝ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        finiteThreeMomentBCReferenceChoi_eq_card_smul_approximateHaarRawChoi
          A B C
      _ = ((Fintype.card (ThreeReplica A) : ℝ) : ℂ) •
          finiteThreeMomentApproximateHaarRawChoi
            (Fintype.card B * Fintype.card C)
            (finiteThreeMomentBCLocalChoiQ A B C) :=
        RCLike.real_smul_eq_coe_smul _ _

end

end TomographyOracleCore
