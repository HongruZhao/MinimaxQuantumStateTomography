import TomographyOracleCore.BinaryCliffordWebbIdentityPlacements
import TomographyOracleCore.UnitaryHaarOrientation

namespace TomographyOracleCore

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator BigOperators

noncomputable section

noncomputable instance pauliUnitaryCompactSpace (K : ℕ) :
    CompactSpace
      (unitary (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) := by
  letI : Nonempty (PauliBinaryWord K) := ⟨0⟩
  apply isCompact_iff_compactSpace.mp
  apply Metric.isCompact_of_isClosed_isBounded isClosed_unitary
  rw [Metric.isBounded_iff]
  refine ⟨2, ?_⟩
  intro U hU V hV
  calc
    dist U V = ‖U - V‖ := dist_eq_norm U V
    _ ≤ ‖U‖ + ‖V‖ := norm_sub_le U V
    _ = 2 := by
      rw [CStarRing.norm_of_mem_unitary hU,
        CStarRing.norm_of_mem_unitary hV]
      norm_num

noncomputable def pauliUnitaryHaarProbability (K : ℕ) :
    Measure (unitary (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :=
  let μ : Measure
      (unitary (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :=
    Measure.haar
  (μ univ)⁻¹ • μ

private theorem pauliUnitaryHaar_univ_ne_zero (K : ℕ) :
    (Measure.haar : Measure
      (unitary (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)))
        univ ≠ 0 := by
  exact isOpen_univ.measure_ne_zero _ univ_nonempty

private theorem pauliUnitaryHaar_univ_ne_top (K : ℕ) :
    (Measure.haar : Measure
      (unitary (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)))
        univ ≠ ∞ := by
  exact ne_of_lt isCompact_univ.measure_lt_top

instance pauliUnitaryHaarProbability_isProbabilityMeasure (K : ℕ) :
    IsProbabilityMeasure (pauliUnitaryHaarProbability K) where
  measure_univ := by
    rw [pauliUnitaryHaarProbability, Measure.smul_apply]
    exact ENNReal.inv_mul_cancel
      (pauliUnitaryHaar_univ_ne_zero K)
      (pauliUnitaryHaar_univ_ne_top K)

instance pauliUnitaryHaarProbability_isMulLeftInvariant (K : ℕ) :
    (pauliUnitaryHaarProbability K).IsMulLeftInvariant := by
  unfold pauliUnitaryHaarProbability
  infer_instance

theorem pauliUnitaryHaarProbability_map_mul_right (K : ℕ)
    (V : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    Measure.map (fun U ↦ U * V) (pauliUnitaryHaarProbability K) =
      pauliUnitaryHaarProbability K := by
  letI : Measure.IsHaarMeasure (pauliUnitaryHaarProbability K) := by
    unfold pauliUnitaryHaarProbability
    exact Measure.IsHaarMeasure.smul _
      (ENNReal.inv_ne_zero.mpr (pauliUnitaryHaar_univ_ne_top K))
      (ENNReal.inv_ne_top.mpr (pauliUnitaryHaar_univ_ne_zero K))
  let ν := Measure.map (fun U ↦ U * V) (pauliUnitaryHaarProbability K)
  letI : IsProbabilityMeasure ν :=
    Measure.isProbabilityMeasure_map (by fun_prop :
      AEMeasurable (fun U : unitary
        (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) ↦ U * V)
        (pauliUnitaryHaarProbability K))
  letI : Measure.IsHaarMeasure ν := by
    dsimp only [ν]
    exact Measure.isHaarMeasure_map_mul_right
      (pauliUnitaryHaarProbability K) V
  have h : ν = pauliUnitaryHaarProbability K := by
    apply Measure.isHaarMeasure_eq_of_isProbabilityMeasure
  exact h

instance pauliUnitaryHaarProbability_isMulRightInvariant (K : ℕ) :
    (pauliUnitaryHaarProbability K).IsMulRightInvariant where
  map_mul_right_eq_self := pauliUnitaryHaarProbability_map_mul_right K

theorem integral_comp_pauliUnitaryHaarProbability_mul_right
    (K : ℕ)
    (V : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) → E)
    (hf : AEStronglyMeasurable f (pauliUnitaryHaarProbability K)) :
    (∫ U, f (U * V) ∂pauliUnitaryHaarProbability K) =
      ∫ U, f U ∂pauliUnitaryHaarProbability K := by
  have hmul : Measurable
      (fun U : unitary
        (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) ↦ U * V) := by
    fun_prop
  have hfmap : AEStronglyMeasurable f
      (Measure.map (fun U ↦ U * V) (pauliUnitaryHaarProbability K)) := by
    rw [pauliUnitaryHaarProbability_map_mul_right]
    exact hf
  calc
    (∫ U, f (U * V) ∂pauliUnitaryHaarProbability K) =
        ∫ U, f U ∂Measure.map (fun U ↦ U * V)
          (pauliUnitaryHaarProbability K) := by
      symm
      exact integral_map hmul.aemeasurable hfmap
    _ = ∫ U, f U ∂pauliUnitaryHaarProbability K := by
      rw [pauliUnitaryHaarProbability_map_mul_right]

noncomputable def unitaryTensorCube
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    ThirdM K :=
  matrixTensorThree U.1 U.1 U.1

noncomputable def unitaryThirdConjugation
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (X : ThirdM K) : ThirdM K :=
  (unitaryTensorCube K U * X) * (unitaryTensorCube K U).conjTranspose

theorem unitaryTensorCube_mul
    (K : ℕ)
    (U V : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K (U * V) =
      unitaryTensorCube K U * unitaryTensorCube K V := by
  unfold unitaryTensorCube
  change matrixTensorThree (U.1 * V.1) (U.1 * V.1) (U.1 * V.1) =
    matrixTensorThree U.1 U.1 U.1 * matrixTensorThree V.1 V.1 V.1
  exact matrixTensorThree_mul U.1 U.1 U.1 V.1 V.1 V.1

theorem unitaryThirdConjugation_comp
    (K : ℕ)
    (U V : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (X : ThirdM K) :
    unitaryThirdConjugation K U (unitaryThirdConjugation K V X) =
      unitaryThirdConjugation K (U * V) X := by
  unfold unitaryThirdConjugation
  rw [unitaryTensorCube_mul, Matrix.conjTranspose_mul]
  noncomm_ring

theorem unitaryThirdConjugation_add
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (X Y : ThirdM K) :
    unitaryThirdConjugation K U (X + Y) =
      unitaryThirdConjugation K U X +
        unitaryThirdConjugation K U Y := by
  unfold unitaryThirdConjugation
  rw [Matrix.mul_add, Matrix.add_mul]

theorem unitaryThirdConjugation_smul
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (c : ℂ) (X : ThirdM K) :
    unitaryThirdConjugation K U (c • X) =
      c • unitaryThirdConjugation K U X := by
  unfold unitaryThirdConjugation
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem continuous_unitaryTensorCube (K : ℕ) :
    Continuous (unitaryTensorCube K) := by
  apply continuous_matrix
  intro x y
  change Continuous (fun U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) ↦
    U.1 x.1 y.1 * U.1 x.2.1 y.2.1 * U.1 x.2.2 y.2.2)
  have hentry (i j : PauliBinaryWord K) :
      Continuous (fun U : unitary
        (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ) ↦ U.1 i j) :=
    (continuous_apply_apply i j).comp continuous_subtype_val
  exact ((hentry x.1 y.1).mul (hentry x.2.1 y.2.1)).mul
    (hentry x.2.2 y.2.2)

theorem continuous_unitaryThirdConjugation
    (K : ℕ) (X : ThirdM K) :
    Continuous (fun U ↦ unitaryThirdConjugation K U X) := by
  have hcube := continuous_unitaryTensorCube K
  have hstar : Continuous
      (fun U ↦ (unitaryTensorCube K U).conjTranspose) := by
    apply continuous_matrix
    intro i j
    change Continuous (fun U ↦ star (unitaryTensorCube K U j i))
    exact Complex.continuous_conj.comp
      ((continuous_apply_apply j i).comp hcube)
  exact (hcube.matrix_mul continuous_const).matrix_mul hstar

theorem integrable_unitaryThirdConjugation
    (K : ℕ) (X : ThirdM K) :
    Integrable (fun U ↦ unitaryThirdConjugation K U X)
      (pauliUnitaryHaarProbability K) := by
  simpa [IntegrableOn] using
    (continuous_unitaryThirdConjugation K X).continuousOn.integrableOn_compact
      (μ := pauliUnitaryHaarProbability K) isCompact_univ

noncomputable def pauliHaarThirdTwirlLinearMap (K : ℕ) :
    ThirdM K →ₗ[ℂ] ThirdM K where
  toFun X := ∫ U, unitaryThirdConjugation K U X
      ∂pauliUnitaryHaarProbability K
  map_add' X Y := by
    simp_rw [unitaryThirdConjugation_add]
    exact integral_add
      (integrable_unitaryThirdConjugation K X)
      (integrable_unitaryThirdConjugation K Y)
  map_smul' c X := by
    simp_rw [unitaryThirdConjugation_smul]
    exact integral_smul c _

abbrev pauliHaarThirdTwirl (K : ℕ) (X : ThirdM K) : ThirdM K :=
  pauliHaarThirdTwirlLinearMap K X

theorem pauliHaarThirdTwirl_conjugation
    (K : ℕ)
    (V : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ))
    (X : ThirdM K) :
    pauliHaarThirdTwirl K (unitaryThirdConjugation K V X) =
      pauliHaarThirdTwirl K X := by
  change (∫ U, unitaryThirdConjugation K U
      (unitaryThirdConjugation K V X)
      ∂pauliUnitaryHaarProbability K) =
    ∫ U, unitaryThirdConjugation K U X
      ∂pauliUnitaryHaarProbability K
  calc
    (∫ U, unitaryThirdConjugation K U
        (unitaryThirdConjugation K V X)
        ∂pauliUnitaryHaarProbability K) =
      ∫ U, unitaryThirdConjugation K (U * V) X
        ∂pauliUnitaryHaarProbability K := by
          apply integral_congr_ae
          filter_upwards [] with U
          exact unitaryThirdConjugation_comp K U V X
    _ = ∫ U, unitaryThirdConjugation K U X
        ∂pauliUnitaryHaarProbability K :=
      integral_comp_pauliUnitaryHaarProbability_mul_right K V
        (fun U ↦ unitaryThirdConjugation K U X)
        (integrable_unitaryThirdConjugation K X).aestronglyMeasurable

noncomputable def finitePauliCosetThirdTwirlLinearMap (K : ℕ) :
    ThirdM K →ₗ[ℂ] ThirdM K where
  toFun X :=
    ((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
      ∑ e : PauliCosetCliffordEnsemble K,
        unitaryThirdConjugation K (pauliCosetCliffordUnitary K e) X
  map_add' X Y := by
    simp_rw [unitaryThirdConjugation_add, Finset.sum_add_distrib]
    module
  map_smul' c X := by
    simp_rw [unitaryThirdConjugation_smul, ← Finset.smul_sum]
    simp only [RingHom.id_apply]
    module

abbrev finitePauliCosetThirdTwirl
    (K : ℕ) (X : ThirdM K) : ThirdM K :=
  finitePauliCosetThirdTwirlLinearMap K X

theorem pauliHaarThirdTwirl_finitePauliCosetThirdTwirl
    (K : ℕ) (X : ThirdM K) :
    pauliHaarThirdTwirl K (finitePauliCosetThirdTwirl K X) =
      pauliHaarThirdTwirl K X := by
  classical
  change pauliHaarThirdTwirlLinearMap K
      (((Fintype.card (PauliCosetCliffordEnsemble K) : ℂ)⁻¹) •
        ∑ e : PauliCosetCliffordEnsemble K,
          unitaryThirdConjugation K (pauliCosetCliffordUnitary K e) X) = _
  rw [map_smul, map_sum]
  simp_rw [pauliHaarThirdTwirl_conjugation]
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard :
      (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (PauliCosetCliffordEnsemble K) ≠ 0)
  rw [inv_mul_cancel₀ hcard, one_smul]

def permutationMatrix {α : Type*} [DecidableEq α]
    (σ : α ≃ α) : Matrix α α ℂ :=
  fun x y ↦ if x = σ y then 1 else 0

theorem mul_permutationMatrix_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (M : Matrix α α ℂ) (σ : α ≃ α) (x y : α) :
    (M * permutationMatrix σ) x y = M x (σ y) := by
  classical
  simp only [Matrix.mul_apply, permutationMatrix]
  rw [Finset.sum_eq_single (σ y)]
  · simp
  · intro z hz hne
    simp [hne]
  · simp

theorem permutationMatrix_mul_apply
    {α : Type*} [Fintype α] [DecidableEq α]
    (σ : α ≃ α) (M : Matrix α α ℂ) (x y : α) :
    (permutationMatrix σ * M) x y = M (σ.symm x) y := by
  classical
  simp only [Matrix.mul_apply, permutationMatrix]
  rw [Finset.sum_eq_single (σ.symm x)]
  · simp
  · intro z hz hne
    have hx : x ≠ σ z := by
      intro h
      apply hne
      exact σ.injective (by simpa using h.symm)
    simp [hx]
  · simp

def tripleSwap12Equiv (ι : Type*) : TripleIndex ι ≃ TripleIndex ι where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun x := (x.2.1, x.1, x.2.2)
  left_inv x := rfl
  right_inv x := rfl

def tripleSwap13Equiv (ι : Type*) : TripleIndex ι ≃ TripleIndex ι where
  toFun x := (x.2.2, x.2.1, x.1)
  invFun x := (x.2.2, x.2.1, x.1)
  left_inv x := rfl
  right_inv x := rfl

def tripleSwap23Equiv (ι : Type*) : TripleIndex ι ≃ TripleIndex ι where
  toFun x := (x.1, x.2.2, x.2.1)
  invFun x := (x.1, x.2.2, x.2.1)
  left_inv x := rfl
  right_inv x := rfl

def tripleCycle123Equiv (ι : Type*) : TripleIndex ι ≃ TripleIndex ι where
  toFun x := (x.2.1, x.2.2, x.1)
  invFun x := (x.2.2, x.1, x.2.1)
  left_inv x := rfl
  right_inv x := rfl

def tripleCycle132Equiv (ι : Type*) : TripleIndex ι ≃ TripleIndex ι where
  toFun x := (x.2.2, x.1, x.2.1)
  invFun x := (x.2.1, x.2.2, x.1)
  left_inv x := rfl
  right_inv x := rfl

theorem registerSwap12_eq_permutationMatrix (K : ℕ) :
    registerSwap12 K = permutationMatrix (tripleSwap12Equiv _) := by
  classical
  ext x y
  simp [registerSwap12, permutationMatrix, tripleSwap12Equiv,
    Prod.ext_iff, and_assoc, and_left_comm, and_comm]

theorem registerSwap13_eq_permutationMatrix (K : ℕ) :
    registerSwap13 K = permutationMatrix (tripleSwap13Equiv _) := by
  classical
  ext x y
  simp [registerSwap13, permutationMatrix, tripleSwap13Equiv,
    Prod.ext_iff, and_assoc, and_left_comm, and_comm]

theorem registerSwap23_eq_permutationMatrix (K : ℕ) :
    registerSwap23 K = permutationMatrix (tripleSwap23Equiv _) := by
  classical
  ext x y
  simp [registerSwap23, permutationMatrix, tripleSwap23Equiv,
    Prod.ext_iff, and_assoc, and_left_comm, and_comm]

theorem registerCycle123_eq_permutationMatrix (K : ℕ) :
    registerCycle123 K = permutationMatrix (tripleCycle123Equiv _) := by
  classical
  ext x y
  simp [registerCycle123, permutationMatrix, tripleCycle123Equiv,
    Prod.ext_iff, and_assoc, and_left_comm, and_comm]

theorem registerCycle132_eq_permutationMatrix (K : ℕ) :
    registerCycle132 K = permutationMatrix (tripleCycle132Equiv _) := by
  classical
  ext x y
  simp [registerCycle132, permutationMatrix, tripleCycle132Equiv,
    Prod.ext_iff, and_assoc, and_left_comm, and_comm]

theorem matrixTensorThree_commutes_tripleSwap12
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    matrixTensorThree A A A * permutationMatrix (tripleSwap12Equiv ι) =
      permutationMatrix (tripleSwap12Equiv ι) * matrixTensorThree A A A := by
  ext x y
  rw [mul_permutationMatrix_apply, permutationMatrix_mul_apply]
  change A x.1 y.2.1 * A x.2.1 y.1 * A x.2.2 y.2.2 =
    A x.2.1 y.1 * A x.1 y.2.1 * A x.2.2 y.2.2
  ring

theorem matrixTensorThree_commutes_tripleSwap13
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    matrixTensorThree A A A * permutationMatrix (tripleSwap13Equiv ι) =
      permutationMatrix (tripleSwap13Equiv ι) * matrixTensorThree A A A := by
  ext x y
  rw [mul_permutationMatrix_apply, permutationMatrix_mul_apply]
  change A x.1 y.2.2 * A x.2.1 y.2.1 * A x.2.2 y.1 =
    A x.2.2 y.1 * A x.2.1 y.2.1 * A x.1 y.2.2
  ring

theorem matrixTensorThree_commutes_tripleSwap23
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    matrixTensorThree A A A * permutationMatrix (tripleSwap23Equiv ι) =
      permutationMatrix (tripleSwap23Equiv ι) * matrixTensorThree A A A := by
  ext x y
  rw [mul_permutationMatrix_apply, permutationMatrix_mul_apply]
  change A x.1 y.1 * A x.2.1 y.2.2 * A x.2.2 y.2.1 =
    A x.1 y.1 * A x.2.2 y.2.1 * A x.2.1 y.2.2
  ring

theorem matrixTensorThree_commutes_tripleCycle123
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    matrixTensorThree A A A * permutationMatrix (tripleCycle123Equiv ι) =
      permutationMatrix (tripleCycle123Equiv ι) * matrixTensorThree A A A := by
  ext x y
  rw [mul_permutationMatrix_apply, permutationMatrix_mul_apply]
  change A x.1 y.2.1 * A x.2.1 y.2.2 * A x.2.2 y.1 =
    A x.2.2 y.1 * A x.1 y.2.1 * A x.2.1 y.2.2
  ring

theorem matrixTensorThree_commutes_tripleCycle132
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) :
    matrixTensorThree A A A * permutationMatrix (tripleCycle132Equiv ι) =
      permutationMatrix (tripleCycle132Equiv ι) * matrixTensorThree A A A := by
  ext x y
  rw [mul_permutationMatrix_apply, permutationMatrix_mul_apply]
  change A x.1 y.2.2 * A x.2.1 y.1 * A x.2.2 y.2.1 =
    A x.2.1 y.1 * A x.2.2 y.2.1 * A x.1 y.2.2
  ring

theorem unitaryTensorCube_commutes_registerSwap12
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K U * registerSwap12 K =
      registerSwap12 K * unitaryTensorCube K U := by
  rw [registerSwap12_eq_permutationMatrix]
  exact matrixTensorThree_commutes_tripleSwap12 U.1

theorem unitaryTensorCube_commutes_registerSwap13
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K U * registerSwap13 K =
      registerSwap13 K * unitaryTensorCube K U := by
  rw [registerSwap13_eq_permutationMatrix]
  exact matrixTensorThree_commutes_tripleSwap13 U.1

theorem unitaryTensorCube_commutes_registerSwap23
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K U * registerSwap23 K =
      registerSwap23 K * unitaryTensorCube K U := by
  rw [registerSwap23_eq_permutationMatrix]
  exact matrixTensorThree_commutes_tripleSwap23 U.1

theorem unitaryTensorCube_commutes_registerCycle123
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K U * registerCycle123 K =
      registerCycle123 K * unitaryTensorCube K U := by
  rw [registerCycle123_eq_permutationMatrix]
  exact matrixTensorThree_commutes_tripleCycle123 U.1

theorem unitaryTensorCube_commutes_registerCycle132
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K U * registerCycle132 K =
      registerCycle132 K * unitaryTensorCube K U := by
  rw [registerCycle132_eq_permutationMatrix]
  exact matrixTensorThree_commutes_tripleCycle132 U.1

@[simp] theorem matrixTensorThree_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixTensorThree (1 : Matrix ι ι ℂ) 1 1 = 1 := by
  ext x y
  simp [matrixTensorThree, Matrix.one_apply]
  by_cases h1 : x.1 = y.1 <;>
    by_cases h2 : x.2.1 = y.2.1 <;>
      by_cases h3 : x.2.2 = y.2.2 <;>
        simp [h1, h2, h3] <;> aesop

theorem unitaryTensorCube_mul_conjTranspose
    (K : ℕ)
    (U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ)) :
    unitaryTensorCube K U * (unitaryTensorCube K U).conjTranspose = 1 := by
  unfold unitaryTensorCube
  rw [← matrixTensorThree_conjTranspose,
    ← matrixTensorThree_mul]
  have hU : U.1 * U.1.conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff.mp U.2)
  rw [hU, matrixTensorThree_one]

theorem pauliHaarThirdTwirl_eq_self_of_commutes
    (K : ℕ) (W : ThirdM K)
    (hcomm : ∀ U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ),
        unitaryTensorCube K U * W = W * unitaryTensorCube K U) :
    pauliHaarThirdTwirl K W = W := by
  have hpoint : ∀ U : unitary
      (Matrix (PauliBinaryWord K) (PauliBinaryWord K) ℂ),
      unitaryThirdConjugation K U W = W := by
    intro U
    unfold unitaryThirdConjugation
    calc
      (unitaryTensorCube K U * W) *
          (unitaryTensorCube K U).conjTranspose =
        (W * unitaryTensorCube K U) *
          (unitaryTensorCube K U).conjTranspose := by rw [hcomm U]
      _ = W * (unitaryTensorCube K U *
          (unitaryTensorCube K U).conjTranspose) := by noncomm_ring
      _ = W := by rw [unitaryTensorCube_mul_conjTranspose, mul_one]
  change (∫ U, unitaryThirdConjugation K U W
    ∂pauliUnitaryHaarProbability K) = W
  simp_rw [hpoint]
  simp

@[simp] theorem pauliHaarThirdTwirl_one (K : ℕ) :
    pauliHaarThirdTwirl K (1 : ThirdM K) = 1 := by
  apply pauliHaarThirdTwirl_eq_self_of_commutes
  intro U
  simp

@[simp] theorem pauliHaarThirdTwirl_registerSwap12 (K : ℕ) :
    pauliHaarThirdTwirl K (registerSwap12 K) = registerSwap12 K := by
  exact pauliHaarThirdTwirl_eq_self_of_commutes K _
    (unitaryTensorCube_commutes_registerSwap12 K)

@[simp] theorem pauliHaarThirdTwirl_registerSwap13 (K : ℕ) :
    pauliHaarThirdTwirl K (registerSwap13 K) = registerSwap13 K := by
  exact pauliHaarThirdTwirl_eq_self_of_commutes K _
    (unitaryTensorCube_commutes_registerSwap13 K)

@[simp] theorem pauliHaarThirdTwirl_registerSwap23 (K : ℕ) :
    pauliHaarThirdTwirl K (registerSwap23 K) = registerSwap23 K := by
  exact pauliHaarThirdTwirl_eq_self_of_commutes K _
    (unitaryTensorCube_commutes_registerSwap23 K)

@[simp] theorem pauliHaarThirdTwirl_registerCycle123 (K : ℕ) :
    pauliHaarThirdTwirl K (registerCycle123 K) = registerCycle123 K := by
  exact pauliHaarThirdTwirl_eq_self_of_commutes K _
    (unitaryTensorCube_commutes_registerCycle123 K)

@[simp] theorem pauliHaarThirdTwirl_registerCycle132 (K : ℕ) :
    pauliHaarThirdTwirl K (registerCycle132 K) = registerCycle132 K := by
  exact pauliHaarThirdTwirl_eq_self_of_commutes K _
    (unitaryTensorCube_commutes_registerCycle132 K)

end
end TomographyOracleCore

