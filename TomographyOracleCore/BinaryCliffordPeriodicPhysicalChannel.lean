import TomographyOracleCore.BinaryCliffordPeriodicCircuit
import TomographyOracleCore.BinaryCliffordBlockPhysicalFloor

namespace TomographyOracleCore

open scoped BigOperators
noncomputable section

/-- Physical dephasing for any explicitly conjugated Pauli, without requiring
the target-label map to be bundled as a symplectic-group element. -/
theorem conjugatedComputationalBasisMeasurementChannel_binaryPauli_of_conjugates
    (N : ℕ) (U : Matrix.unitaryGroup (PauliBinaryWord N) ℂ)
    (p q : PauliLabel N) (phase : ℂ) (_hphase : phase ≠ 0)
    (hconj : (U.1 * binaryPauliMatrix N p) * U.1.conjTranspose =
      phase • binaryPauliMatrix N q) :
    conjugatedComputationalBasisMeasurementChannel N U
        (binaryPauliMatrix N p) =
      if q.1 = 0 then binaryPauliMatrix N p else 0 := by
  unfold conjugatedComputationalBasisMeasurementChannel
  rw [hconj, computationalBasisMeasurementChannel_smul,
    computationalBasisMeasurementChannel_binaryPauliMatrix]
  by_cases hz : q.1 = 0
  · rw [if_pos hz, if_pos hz]
    exact unitary_unsandwich U hconj
  · rw [if_neg hz, if_neg hz]
    simp

/-- The literal two-layer periodic measurement channel is exactly its global
Pauli Z-hit indicator. -/
theorem conjugatedPeriodicTwoLayerMeasurementChannel_binaryPauli
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (e : PeriodicTwoLayerCliffordEnsemble m K)
    (p : PauliLabel (m * K)) :
    conjugatedComputationalBasisMeasurementChannel (m * K)
        (periodicTwoLayerCliffordUnitary m K σ e)
        (binaryPauliMatrix (m * K) p) =
      if (periodicTwoLayerPauliAction m K σ e p).1 = 0 then
        binaryPauliMatrix (m * K) p else 0 := by
  obtain ⟨phase, hphase, hconj⟩ :=
    periodicTwoLayerCliffordUnitary_conjugates_binaryPauli m K σ e p
  exact conjugatedComputationalBasisMeasurementChannel_binaryPauli_of_conjugates
    (m * K) (periodicTwoLayerCliffordUnitary m K σ e)
    p (periodicTwoLayerPauliAction m K σ e p) phase hphase hconj

/-- Uniform literal physical measurement channel over the finite two-layer
periodic ensemble. -/
noncomputable def averagedPeriodicTwoLayerMeasurementChannel
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (A : Matrix (PauliBinaryWord (m * K)) (PauliBinaryWord (m * K)) ℂ) :
    Matrix (PauliBinaryWord (m * K)) (PauliBinaryWord (m * K)) ℂ :=
  ((Fintype.card (PeriodicTwoLayerCliffordEnsemble m K) : ℂ)⁻¹) •
    ∑ e : PeriodicTwoLayerCliffordEnsemble m K,
      conjugatedComputationalBasisMeasurementChannel (m * K)
        (periodicTwoLayerCliffordUnitary m K σ e) A

/-- The averaged physical channel coefficient is the exact finite fraction
of two-layer circuits whose final Pauli is diagonal. -/
theorem averagedPeriodicTwoLayerMeasurementChannel_binaryPauli
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) :
    averagedPeriodicTwoLayerMeasurementChannel m K σ
        (binaryPauliMatrix (m * K) p) =
      (((Fintype.card
          {e : PeriodicTwoLayerCliffordEnsemble m K //
            (periodicTwoLayerPauliAction m K σ e p).1 = 0} : ℕ) : ℂ) /
        Fintype.card (PeriodicTwoLayerCliffordEnsemble m K)) •
          binaryPauliMatrix (m * K) p := by
  classical
  have hsum :
      (∑ e : PeriodicTwoLayerCliffordEnsemble m K,
        if (periodicTwoLayerPauliAction m K σ e p).1 = 0 then
          binaryPauliMatrix (m * K) p else 0) =
      ((Fintype.card
          {e : PeriodicTwoLayerCliffordEnsemble m K //
            (periodicTwoLayerPauliAction m K σ e p).1 = 0} : ℕ) : ℂ) •
        binaryPauliMatrix (m * K) p := by
    calc
      _ = ∑ e : PeriodicTwoLayerCliffordEnsemble m K,
          (if (periodicTwoLayerPauliAction m K σ e p).1 = 0
            then (1 : ℂ) else 0) • binaryPauliMatrix (m * K) p := by
          apply Finset.sum_congr rfl
          intro e he
          split_ifs <;> simp
      _ = (∑ e : PeriodicTwoLayerCliffordEnsemble m K,
          if (periodicTwoLayerPauliAction m K σ e p).1 = 0
            then (1 : ℂ) else 0) • binaryPauliMatrix (m * K) p := by
          rw [Finset.sum_smul]
      _ = _ := by rw [Finset.sum_boole, ← Fintype.card_subtype]
  unfold averagedPeriodicTwoLayerMeasurementChannel
  simp_rw [conjugatedPeriodicTwoLayerMeasurementChannel_binaryPauli]
  rw [hsum, smul_smul]
  apply congrArg (fun c : ℂ ↦ c • binaryPauliMatrix (m * K) p)
  rw [div_eq_mul_inv]
  ring

/-- Local nonidentity encoding turns the Z-word condition into precisely the
independent-block event predicate. -/
theorem blockActionHits_optionalNonidentityPauliBlock_iff
    (K : ℕ) (g : binaryTransvectionGroup K) (q : PauliLabel K) :
    blockActionHits (nonidentityZPauliFinset K)
        (optionalNonidentityPauliBlock q) g ↔
      (g.1.1 q).1 = 0 := by
  classical
  by_cases hq : q = 0
  · subst q
    simp [optionalNonidentityPauliBlock, blockActionHits]
  · simp only [optionalNonidentityPauliBlock, dif_neg hq, blockActionHits]
    simp only [nonidentityZPauliFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rfl

@[simp] theorem binaryWordBlockEquiv_blockPauliAction_fst
    (m K : ℕ) (g : Fin m → binaryTransvectionGroup K)
    (q : PauliLabel (m * K)) (j : Fin m) :
    binaryWordBlockEquiv m K (blockPauliAction m K g q).1 j =
      ((g j).1.1 (pauliLabelBlockEquiv m K q j)).1 := by
  have h := congrArg Prod.fst
    (pauliLabelBlockEquiv_blockPauliAction m K g q j)
  exact h

/-- Global diagonal output of a block action is exactly the product event
used by the previously proved independent-block counting theorem. -/
theorem blockPauliAction_fst_eq_zero_iff_independentBlockActionEvent
    (m K : ℕ) (g : Fin m → binaryTransvectionGroup K)
    (q : PauliLabel (m * K)) :
    (blockPauliAction m K g q).1 = 0 ↔
      ∀ j, blockActionHits (nonidentityZPauliFinset K)
        (globalPauliOptionalBlocks q j) (g j) := by
  constructor
  · intro h j
    change blockActionHits (nonidentityZPauliFinset K)
      (optionalNonidentityPauliBlock (pauliLabelBlockEquiv m K q j))
        (g j)
    rw [blockActionHits_optionalNonidentityPauliBlock_iff]
    have hblock := congrArg
      (fun x : PauliBinaryWord (m * K) ↦ binaryWordBlockEquiv m K x j) h
    simpa using hblock
  · intro h
    apply (binaryWordBlockEquiv m K).injective
    funext j
    have hj := (blockActionHits_optionalNonidentityPauliBlock_iff
      K (g j) (pauliLabelBlockEquiv m K q j)).mp (h j)
    simpa using hj

/-- Split a family of local Pauli-coset choices into its free Pauli and
generated-symplectic coordinates. -/
def pauliCosetBlockFamilyEquiv (m K : ℕ) :
    (Fin m → PauliCosetCliffordEnsemble K) ≃
      (Fin m → PauliLabel K) × (Fin m → binaryTransvectionGroup K) where
  toFun e := (fun j ↦ (e j).1, fun j ↦ (e j).2)
  invFun ag j := (ag.1 j, ag.2 j)
  left_inv e := by funext j; exact Prod.eta (e j)
  right_inv ag := by rcases ag with ⟨a, g⟩; rfl

/-- For a fixed incoming global Pauli, the successful second-layer
Pauli-coset choices are a free Pauli family times the already counted
independent generated-group event. -/
noncomputable def pauliCosetBlockHitEquiv
    (m K : ℕ) (q : PauliLabel (m * K)) :
    {e : Fin m → PauliCosetCliffordEnsemble K //
      (blockPauliAction m K (fun j ↦ (e j).2) q).1 = 0} ≃
      (Fin m → PauliLabel K) ×
        IndependentBlockActionEvent
          (C := binaryTransvectionGroup K)
          (globalPauliOptionalBlocks q)
          (nonidentityZPauliFinset K) where
  toFun e :=
    (fun j ↦ (e.1 j).1,
      ⟨fun j ↦ (e.1 j).2,
        (blockPauliAction_fst_eq_zero_iff_independentBlockActionEvent
          m K (fun j ↦ (e.1 j).2) q).mp e.2⟩)
  invFun ag :=
    ⟨fun j ↦ (ag.1 j, ag.2.1 j),
      (blockPauliAction_fst_eq_zero_iff_independentBlockActionEvent
        m K ag.2.1 q).mpr ag.2.2⟩
  left_inv e := by apply Subtype.ext; funext j; exact Prod.eta (e.1 j)
  right_inv ag := by
    rcases ag with ⟨a, ⟨g, hg⟩⟩
    rfl

/-- The free Pauli coordinate cancels from the conditional second-layer hit
ratio. -/
theorem pauliCosetBlockHit_ratio
    (m K : ℕ) (q : PauliLabel (m * K)) :
    ((Fintype.card
        {e : Fin m → PauliCosetCliffordEnsemble K //
          (blockPauliAction m K (fun j ↦ (e j).2) q).1 = 0} : ℕ) : ℝ) /
        Fintype.card (Fin m → PauliCosetCliffordEnsemble K) =
      ((Fintype.card
        (IndependentBlockActionEvent
          (C := binaryTransvectionGroup K)
          (globalPauliOptionalBlocks q)
          (nonidentityZPauliFinset K)) : ℕ) : ℝ) /
        Fintype.card (Fin m → binaryTransvectionGroup K) := by
  classical
  rw [Fintype.card_congr (pauliCosetBlockHitEquiv m K q),
    Fintype.card_prod]
  have hden := Fintype.card_congr (pauliCosetBlockFamilyEquiv m K)
  rw [hden, Fintype.card_prod]
  push_cast
  have hpauli : (Fintype.card (Fin m → PauliLabel K) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Fin m → PauliLabel K) ≠ 0)
  have hgroup : (Fintype.card (Fin m → binaryTransvectionGroup K) : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Fin m → binaryTransvectionGroup K) ≠ 0)
  field_simp [hpauli, hgroup]

/-- A successful two-layer circuit is equivalently a first-layer choice
together with a successful second-layer choice for the resulting label. -/
noncomputable def periodicTwoLayerHitEquivSigma
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) :
    {e : PeriodicTwoLayerCliffordEnsemble m K //
      (periodicTwoLayerPauliAction m K σ e p).1 = 0} ≃
      Σ e₁ : Fin m → PauliCosetCliffordEnsemble K,
        {e₂ : Fin m → PauliCosetCliffordEnsemble K //
          (blockPauliAction m K (fun j ↦ (e₂ j).2)
            (shiftedBlockPauliAction m K σ (fun j ↦ (e₁ j).2) p)).1 = 0} where
  toFun e := ⟨e.1.1, ⟨e.1.2, e.2⟩⟩
  invFun e := ⟨(e.1, e.2.1), e.2.2⟩
  left_inv e := by rfl
  right_inv e := by rfl

/-- Exact finite probability that the output Pauli of the concrete periodic
two-layer ensemble is computational-basis diagonal. -/
noncomputable def periodicTwoLayerHitProbability
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) : ℝ :=
  ((Fintype.card
      {e : PeriodicTwoLayerCliffordEnsemble m K //
        (periodicTwoLayerPauliAction m K σ e p).1 = 0} : ℕ) : ℝ) /
    Fintype.card (PeriodicTwoLayerCliffordEnsemble m K)

/-- Cancelling the free Pauli-coset coordinates identifies the concrete
periodic-circuit hit probability with the previously counted generated-group
block average. -/
theorem periodicTwoLayerHitProbability_eq_averagedGlobal
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) :
    periodicTwoLayerHitProbability m K σ p =
      averagedGlobalBinaryTransvectionHitProbability
        (fun e₁ : Fin m → PauliCosetCliffordEnsemble K ↦
          shiftedBlockPauliAction m K σ (fun j ↦ (e₁ j).2) p) := by
  classical
  unfold periodicTwoLayerHitProbability
  unfold averagedGlobalBinaryTransvectionHitProbability
  rw [Fintype.card_congr (periodicTwoLayerHitEquivSigma m K σ p),
    Fintype.card_sigma, Fintype.card_prod]
  push_cast
  simp_rw [← pauliCosetBlockHit_ratio]
  rw [← Finset.sum_div]
  ring

/-- Every nonzero or zero input label enjoys the uniform concrete
periodic-circuit diagonal-hit floor.  (For the zero label the bound is loose.) -/
theorem periodicTwoLayerHitProbability_floor
    {m K : ℕ} (hK : 0 < K)
    (σ : Equiv.Perm (Fin (m * K))) (p : PauliLabel (m * K)) :
    (1 / ((2 : ℝ) ^ K + 1)) ^ m ≤
      periodicTwoLayerHitProbability m K σ p := by
  rw [periodicTwoLayerHitProbability_eq_averagedGlobal]
  exact averagedGlobalBinaryTransvectionHitProbability_floor hK _

/-- Under the Cho--Kim block-growth condition, the literal periodic-circuit
hit probability has the calibrated universal lower bound `1/2`. -/
theorem ChoKimBlockCondition.half_le_calibrated_periodicTwoLayerHitProbability
    {n K : ℕ} (h : ChoKimBlockCondition n K)
    (σ : Equiv.Perm (Fin ((n / K) * K)))
    (p : PauliLabel ((n / K) * K)) :
    (1 : ℝ) / 2 ≤
      ((2 : ℝ) ^ n + 1) *
        periodicTwoLayerHitProbability (n / K) K σ p := by
  rw [periodicTwoLayerHitProbability_eq_averagedGlobal]
  exact h.half_le_calibrated_generated_block_probability _

/-- The literal averaged Born/dephasing channel is Pauli diagonal with
eigenvalue exactly the concrete periodic two-layer hit probability. -/
theorem averagedPeriodicTwoLayerMeasurementChannel_binaryPauli_eq_hitProbability
    (m K : ℕ) (σ : Equiv.Perm (Fin (m * K)))
    (p : PauliLabel (m * K)) :
    averagedPeriodicTwoLayerMeasurementChannel m K σ
        (binaryPauliMatrix (m * K) p) =
      (periodicTwoLayerHitProbability m K σ p : ℂ) •
        binaryPauliMatrix (m * K) p := by
  rw [averagedPeriodicTwoLayerMeasurementChannel_binaryPauli]
  simp [periodicTwoLayerHitProbability]

end
end TomographyOracleCore
