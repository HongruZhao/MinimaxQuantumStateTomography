import TomographyOracleCore.Revision.FourthSectorDecomposition
import TomographyOracleCore.Revision.BinaryCliffordFourthRange
import TomographyOracleCore.BinaryCliffordFourthBlockAction

/-!
# The literal Clifford fourth twirl equals the thirty-sector synthesis

All ingredients are proved: the range has dimension at most thirty; the
thirty sector matrices are independent and fixed by every physical Clifford
lift; and unitary conjugation preserves their Hilbert--Schmidt pairings.
-/

namespace TomographyOracleCore.Revision.PhysicalCliffordFourthTwirl

open FourthSectorDecomposition BinaryCliffordFourthRange BinaryCliffordNeutralFourth
open scoped BigOperators Matrix

noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective
local instance : Fintype QubitFourthReplicaIndex := Fintype.ofFinite _

theorem reindex_wordSector (K : ℕ) (i : Fin 30) :
    fourthCopyBlockReplicaReindexAlgEquiv K (wordSector K i) = qubitFourthSectorR K i :=
  (fourthCopyBlockReplicaMatrixEquiv K ℂ).apply_symm_apply _

theorem sectorR_linearIndependent {K : ℕ} (hK : 3 ≤ K) :
    LinearIndependent ℂ (qubitFourthSectorR K) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  change qubitFourthSectorCombination K c = 0 at hc
  have hGram : qubitFourthSectorRGramMatrix K *ᵥ c = 0 := by
    funext l
    rw [← qubitFourthSector_hilbertSchmidt_combination, hc]
    simp [qubitFourthComplexHilbertSchmidt]
  have hleft := qubitFourthComplexWgMatrix_mul_sectorRGram hK
  have happly := congrArg
    (fun v : Fin 30 → ℂ => qubitFourthComplexWgMatrix ((2 : ℝ) ^ K) *ᵥ v) hGram
  have hz : c = 0 := by
    simpa [Matrix.mulVec_mulVec, hleft] using happly
  exact congrFun hz i

theorem wordSector_linearIndependent {K : ℕ} (hK : 3 ≤ K) :
    LinearIndependent ℂ (wordSector K) := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  have h := congrArg (fourthCopyBlockReplicaReindexAlgEquiv K) hc
  simp only [map_sum, map_smul, map_zero, reindex_wordSector] at h
  exact Fintype.linearIndependent_iff.mp (sectorR_linearIndependent hK) c h

theorem finiteCliffordFourthAverage_wordSector (K : ℕ) (i : Fin 30) :
    finiteCliffordFourthAverage K (wordSector K i) = wordSector K i := by
  unfold finiteCliffordFourthAverage
  simp only [LinearMap.smul_apply, LinearMap.sum_apply]
  have hfix (e : PauliCosetCliffordEnsemble K) :
      pauliCosetCliffordFourthAction K e (wordSector K i) = wordSector K i :=
    unitaryFourthConjugation_fixes_wordSector K (pauliCosetCliffordUnitary_spec K e) i
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  have hcard : (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_smul]

theorem span_wordSector_le_range (K : ℕ) :
    Submodule.span ℂ (Set.range (wordSector K)) ≤ (finiteCliffordFourthAverage K).range := by
  apply Submodule.span_le.mpr
  rintro X ⟨i, rfl⟩
  exact ⟨wordSector K i, finiteCliffordFourthAverage_wordSector K i⟩

/-- The full range of the actual Clifford fourth average is exactly the
span of the thirty literal sectors. -/
theorem range_finiteCliffordFourthAverage_eq_sectorSpan {K : ℕ} (hK : 3 ≤ K) :
    (finiteCliffordFourthAverage K).range =
      Submodule.span ℂ (Set.range (wordSector K)) := by
  symm
  apply Submodule.eq_of_le_of_finrank_le (span_wordSector_le_range K)
  have hd : Module.finrank ℂ (Submodule.span ℂ (Set.range (wordSector K))) = 30 := by
    simpa using finrank_span_eq_card (wordSector_linearIndependent hK)
  rw [hd]
  exact finrank_finiteCliffordFourthAverage_range_le_thirty K

theorem unitaryConjugation_inv_fixes_of_fixes
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (S : Matrix ι ι ℂ)
    (hS : unitaryMatrixConjugationLinearMap U S = S) :
    unitaryMatrixConjugationLinearMap U⁻¹ S = S := by
  have h := congrArg (unitaryMatrixConjugationLinearMap U⁻¹) hS
  have hcancel : unitaryMatrixConjugationLinearMap U⁻¹
      (unitaryMatrixConjugationLinearMap U S) = S := by
    change (unitaryMatrixConjugationLinearMap U⁻¹ *
      unitaryMatrixConjugationLinearMap U) S = S
    rw [← unitaryMatrixConjugationLinearMap_mul, inv_mul_cancel,
      unitaryMatrixConjugationLinearMap_one]
    rfl
  rw [hcancel] at h
  exact h.symm

theorem hilbertSchmidt_conjugation_of_fixed
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix.unitaryGroup ι ℂ) (S X : Matrix ι ι ℂ)
    (hS : unitaryMatrixConjugationLinearMap U S = S) :
    qubitFourthComplexHilbertSchmidt S (unitaryMatrixConjugationLinearMap U X) =
      qubitFourthComplexHilbertSchmidt S X := by
  rw [unitaryMatrixConjugationLinearMap_inverse_adjoint,
    unitaryConjugation_inv_fixes_of_fixes U S hS]

/-- Every sector pairing is preserved by the actual average. -/
theorem hilbertSchmidt_wordSector_average
    (K : ℕ) (i : Fin 30) (X : FourthPauliMatrix K) :
    qubitFourthComplexHilbertSchmidt (wordSector K i) (finiteCliffordFourthAverage K X) =
      qubitFourthComplexHilbertSchmidt (wordSector K i) X := by
  unfold finiteCliffordFourthAverage
  simp only [LinearMap.smul_apply, LinearMap.sum_apply,
    qubitFourthComplexHilbertSchmidt_smul_right, qubitFourthComplexHilbertSchmidt_sum_right]
  have hfix (e : PauliCosetCliffordEnsemble K) :
      qubitFourthComplexHilbertSchmidt (wordSector K i) (pauliCosetCliffordFourthAction K e X) =
        qubitFourthComplexHilbertSchmidt (wordSector K i) X :=
    hilbertSchmidt_conjugation_of_fixed (pauliCosetCliffordTensorFourth K e) _ X
      (unitaryFourthConjugation_fixes_wordSector K (pauliCosetCliffordUnitary_spec K e) i)
  simp_rw [hfix]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
  have hcard : (Fintype.card (PauliCosetCliffordEnsemble K) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [inv_mul_cancel₀ hcard, one_mul]

theorem hilbertSchmidt_fourthReindex (K : ℕ) (A B : FourthPauliMatrix K) :
    qubitFourthComplexHilbertSchmidt
        (fourthCopyBlockReplicaReindexAlgEquiv K A)
        (fourthCopyBlockReplicaReindexAlgEquiv K B) = qubitFourthComplexHilbertSchmidt A B := by
  simp only [qubitFourthComplexHilbertSchmidt_eq_entrywise]
  change (∑ x, ∑ y,
    star (A ((fourthIndexPauliBinaryWordEquiv K).symm x)
      ((fourthIndexPauliBinaryWordEquiv K).symm y)) *
      B ((fourthIndexPauliBinaryWordEquiv K).symm x)
        ((fourthIndexPauliBinaryWordEquiv K).symm y)) = _
  have hinner (x : QubitFourthBlockReplicaIndex K) :
      (∑ y, star (A ((fourthIndexPauliBinaryWordEquiv K).symm x)
        ((fourthIndexPauliBinaryWordEquiv K).symm y)) *
        B ((fourthIndexPauliBinaryWordEquiv K).symm x)
          ((fourthIndexPauliBinaryWordEquiv K).symm y)) =
      ∑ y, star (A ((fourthIndexPauliBinaryWordEquiv K).symm x) y) *
        B ((fourthIndexPauliBinaryWordEquiv K).symm x) y :=
    Equiv.sum_comp (fourthIndexPauliBinaryWordEquiv K).symm
      (fun y : FourthIndex (PauliBinaryWord K) =>
        star (A ((fourthIndexPauliBinaryWordEquiv K).symm x) y) *
          B ((fourthIndexPauliBinaryWordEquiv K).symm x) y)
  simp_rw [hinner]
  exact Equiv.sum_comp (fourthIndexPauliBinaryWordEquiv K).symm
    (fun x : FourthIndex (PauliBinaryWord K) => ∑ y, star (A x y) * B x y)

def physicalCliffordFourthBlockAverage (K : ℕ) : QubitFourthComplexSuperoperator K :=
  (fourthCopyBlockReplicaReindexAlgEquiv K).toLinearMap.comp
    ((finiteCliffordFourthAverage K).comp
      (fourthCopyBlockReplicaReindexAlgEquiv K).symm.toLinearMap)

theorem physicalCliffordFourthBlockAverage_range
    {K : ℕ} (hK : 3 ≤ K)
    (X : Matrix (QubitFourthBlockReplicaIndex K) (QubitFourthBlockReplicaIndex K) ℂ) :
    ∃ c : Fin 30 → ℂ, physicalCliffordFourthBlockAverage K X =
      qubitFourthSectorCombination K c := by
  let Y := (fourthCopyBlockReplicaReindexAlgEquiv K).symm X
  have hmem : finiteCliffordFourthAverage K Y ∈
      Submodule.span ℂ (Set.range (wordSector K)) := by
    rw [← range_finiteCliffordFourthAverage_eq_sectorSpan hK]
    exact LinearMap.mem_range_self _ Y
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
  have h := congrArg (fourthCopyBlockReplicaReindexAlgEquiv K) hc
  simp only [map_sum, map_smul, reindex_wordSector] at h
  exact ⟨c, h.symm⟩

theorem physicalCliffordFourthBlockAverage_residual
    (K : ℕ)
    (X : Matrix (QubitFourthBlockReplicaIndex K) (QubitFourthBlockReplicaIndex K) ℂ)
    (i : Fin 30) :
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR K i)
      (X - physicalCliffordFourthBlockAverage K X) = 0 := by
  let Y := (fourthCopyBlockReplicaReindexAlgEquiv K).symm X
  have h := hilbertSchmidt_wordSector_average K i Y
  rw [← hilbertSchmidt_fourthReindex K (wordSector K i)
    (finiteCliffordFourthAverage K Y),
    ← hilbertSchmidt_fourthReindex K (wordSector K i) Y] at h
  rw [reindex_wordSector] at h
  change qubitFourthComplexHilbertSchmidt (qubitFourthSectorR K i)
      (physicalCliffordFourthBlockAverage K X) =
    qubitFourthComplexHilbertSchmidt (qubitFourthSectorR K i)
      (fourthCopyBlockReplicaReindexAlgEquiv K
        ((fourthCopyBlockReplicaReindexAlgEquiv K).symm X)) at h
  rw [AlgEquiv.apply_symm_apply] at h
  rw [qubitFourthComplexHilbertSchmidt_sub_right, h, sub_self]

/-- The exact physical Clifford fourth twirl, with no range, invariance,
representation, or inverse-Gram premise left open. -/
theorem physicalCliffordFourthBlockAverage_eq_synthesis
    {K : ℕ} (hK : 3 ≤ K) :
    physicalCliffordFourthBlockAverage K = qubitFourthSectorSynthesisCandidate K := by
  apply LinearMap.ext
  intro X
  obtain ⟨c, hc⟩ := physicalCliffordFourthBlockAverage_range hK X
  exact qubitFourthSectorProjection_unique hK X (physicalCliffordFourthBlockAverage K X)
    c hc (physicalCliffordFourthBlockAverage_residual K X)

end

end TomographyOracleCore.Revision.PhysicalCliffordFourthTwirl
