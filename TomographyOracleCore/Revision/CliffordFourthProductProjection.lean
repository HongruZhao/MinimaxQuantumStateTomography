import TomographyOracleCore.Revision.FourthTwirlTensorization

namespace TomographyOracleCore.Revision.CliffordFourthProductProjection

open FourthTwirlTensorization MatrixTensorPi MatrixTensorPiSpan
open PhysicalCliffordFourthTwirl FourthSectorDecomposition BinaryCliffordNeutralFourth
open scoped BigOperators
noncomputable section

local instance : Finite QubitFourthReplicaIndex :=
  Finite.of_injective BitVec.toFin BitVec.toFin_injective
local instance : Fintype QubitFourthReplicaIndex := Fintype.ofFinite _

theorem wordFourthAverage_eq_sum {K : ℕ} (hK : 3 ≤ K) (X : FourthPauliMatrix K) :
    finiteCliffordFourthAverage K X =
      ∑ i : Fin 30, ∑ j : Fin 30,
        (qubitFourthComplexWgMatrix ((2 : ℝ) ^ K) i j *
          qubitFourthComplexHilbertSchmidt (wordSector K j) X) • wordSector K i := by
  apply (fourthCopyBlockReplicaReindexAlgEquiv K).injective
  simp only [map_sum, map_smul, reindex_wordSector]
  have havg : fourthCopyBlockReplicaReindexAlgEquiv K (finiteCliffordFourthAverage K X) =
      physicalCliffordFourthBlockAverage K (fourthCopyBlockReplicaReindexAlgEquiv K X) := by
    simp only [physicalCliffordFourthBlockAverage, LinearMap.comp_apply,
      AlgEquiv.toLinearMap_apply, AlgEquiv.symm_apply_apply]
  rw [havg, physicalCliffordFourthBlockAverage_eq_synthesis hK,
    qubitFourthSectorSynthesisCandidate_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  unfold qubitFourthSectorAnalysis
  rw [← reindex_wordSector, hilbertSchmidt_fourthReindex]

def familySynthesis
    {ι L : Type*} [Fintype ι] [Fintype L]
    (S : L → Matrix ι ι ℂ) (W : Matrix L L ℂ) :
    Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
  ∑ i, ∑ j, W i j • (qubitFourthComplexHilbertSchmidtRightLinear (S j)).smulRight (S i)

theorem familySynthesis_apply
    {ι L : Type*} [Fintype ι] [Fintype L]
    (S : L → Matrix ι ι ℂ) (W : Matrix L L ℂ) (X : Matrix ι ι ℂ) :
    familySynthesis S W X =
      ∑ i, ∑ j, (W i j * qubitFourthComplexHilbertSchmidt (S j) X) • S i := by
  simp only [familySynthesis, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.smulRight_apply, smul_smul]
  rfl

variable {J : Type*} [Fintype J] [DecidableEq J]

def blockFourthAverage (K : ℕ) :
    Matrix (FourthIndex (J → PauliBinaryWord K)) (FourthIndex (J → PauliBinaryWord K)) ℂ →ₗ[ℂ]
      Matrix (FourthIndex (J → PauliBinaryWord K)) (FourthIndex (J → PauliBinaryWord K)) ℂ :=
  fourthAverage (fun e : J → PauliCosetCliffordEnsemble K =>
    tensorPiUnitary (fun j => pauliCosetCliffordUnitary K (e j)))

def blockSectorFamily (K : ℕ) (labels : J → Fin 30) :
    Matrix (FourthIndex (J → PauliBinaryWord K)) (FourthIndex (J → PauliBinaryWord K)) ℂ :=
  fourthTensorPi (fun j => wordSector K (labels j))

def blockWgMatrix (K : ℕ) : Matrix (J → Fin 30) (J → Fin 30) ℂ :=
  fun i j => ∏ a : J, qubitFourthComplexWgMatrix ((2 : ℝ) ^ K) (i a) (j a)

/-- The actual independent block average is the full tensor-sector
projection, on all matrices rather than only tensor-product inputs. -/
theorem blockFourthAverage_eq_synthesis {K : ℕ} (hK : 3 ≤ K) :
    blockFourthAverage (J := J) K = familySynthesis (blockSectorFamily K) (blockWgMatrix K) := by
  classical
  apply linearMap_ext_on_fourthTensorPi
  intro A
  change fourthAverage (fun e : J → PauliCosetCliffordEnsemble K =>
    tensorPiUnitary (fun j => pauliCosetCliffordUnitary K (e j))) (fourthTensorPi A) = _
  rw [fourthAverage_tensorPi]
  change fourthTensorPi (fun j => finiteCliffordFourthAverage K (A j)) = _
  simp_rw [wordFourthAverage_eq_sum hK, fourthTensorPi_sum, fourthTensorPi_smul,
    Finset.prod_mul_distrib]
  rw [familySynthesis_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← fourthTensorPi_hilbertSchmidt]
  rfl

end
end TomographyOracleCore.Revision.CliffordFourthProductProjection
