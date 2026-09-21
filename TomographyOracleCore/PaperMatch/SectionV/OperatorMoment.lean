import TomographyOracleCore.Revision.PhysicalFourthExpansion
import TomographyOracleCore.Revision.FourthMeasurementMoment
import TomographyOracleCore.PaperMatch.LowerMoments.ArbitraryBoundary

/-!
The operator identity of Section V, before contraction with a test state.

`coefficient` is the literal real coefficient a_zeta. `basisMoment` is an
average of actual four-copy rank-one projectors from the concrete two-layer
Pauli-coset Clifford ensemble. It is not defined by its sector expansion.

The full projective-normalizer uniform law in the paper is not identified
with this finite implementation in the current library. See the separate
paper correspondence report; the theorems below introduce no such axiom.
-/

namespace TomographyOracleCore.PaperMatch.SectionV

open Revision FourthTwirlTensorization FourthTwirlTransport FourthMeasurementMoment
open PhysicalFourthExpansion PhysicalFourthProjection FourthPhysicalSectorCoordinates
open CliffordFourthProductProjection CliffordFourthBasisInput CliffordFourthWgRows
open FourthSynthesisAdjoint FourthVectorBoundary PhysicalFourthBoundary
open FourthSectorExpansionBound
open FourthBoundaryReindex BlockSectorBoundary PauliOmegaBlocks
open scoped BigOperators InnerProductSpace
noncomputable section

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E]

theorem hilbertSchmidt_ext_left {A B : Matrix ι ι ℂ}
    (h : ∀ X, qubitFourthComplexHilbertSchmidt A X =
      qubitFourthComplexHilbertSchmidt B X) : A = B := by
  classical
  ext i j
  have ht := h (Matrix.single i j 1)
  simp [qubitFourthComplexHilbertSchmidt_eq_entrywise, Matrix.single, ite_and] at ht
  simpa using congrArg star ht

theorem fourthAverage_inverse_adjoint (U : E → Matrix.unitaryGroup ι ℂ)
    (A B : Matrix (FourthIndex ι) (FourthIndex ι) ℂ) :
    qubitFourthComplexHilbertSchmidt A (fourthAverage U B) =
      qubitFourthComplexHilbertSchmidt (fourthAverage (fun e => (U e)⁻¹) A) B := by
  simp only [fourthAverage, LinearMap.smul_apply, LinearMap.sum_apply,
    qubitFourthComplexHilbertSchmidt_smul_right,
    qubitFourthComplexHilbertSchmidt_smul_left,
    qubitFourthComplexHilbertSchmidt_sum_right,
    qubitFourthComplexHilbertSchmidt_sum_left,
    unitaryMatrixConjugationLinearMap_inverse_adjoint, unitaryTensorFourth_inv,
    star_inv₀, star_natCast]

/-- The measurement average acts in the reverse layer order. -/
theorem inverse_periodicFourthAverage (m h : ℕ) (hK : 3 ≤ 2 * h)
    (X : Matrix (FourthIndex (PauliBinaryWord (m * (2 * h))))
      (FourthIndex (PauliBinaryWord (m * (2 * h)))) ℂ) :
    fourthAverage (fun e => (periodicTwoLayerCliffordUnitary m (2 * h)
      (cyclicQubitShift (m * (2 * h)) h) e)⁻¹) X =
      physicalShiftedAverage m h (physicalBlockAverage m (2 * h) X) := by
  apply hilbertSchmidt_ext_left
  intro Y
  rw [← fourthAverage_inverse_adjoint]
  change qubitFourthComplexHilbertSchmidt X (periodicFourthAverage m h Y) = _
  rw [periodicFourthAverage_eq_composition, LinearMap.comp_apply,
    physicalBlockAverage_selfAdjoint m hK, physicalShiftedAverage_selfAdjoint m hK]

/-- Real coefficient in the paper, with q=2^h and Q=2^(2h). -/
def coefficient (m h : ℕ) (zeta : Fin m → Fin 30) : ℝ :=
  cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
    ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
      ∏ j : Fin m,
        qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
        qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) *
        qubitFourthRealWgMatrix ((2 : ℝ) ^ (2 * h)) (sigma j) (zeta j)

theorem complexWg_symmetric (x : ℝ) (i j : Fin 30) :
    qubitFourthComplexWgMatrix x i j = qubitFourthComplexWgMatrix x j i := by
  simp only [qubitFourthComplexWgMatrix, qubitFourthIntersectionClass_comm]

theorem coefficient_cast (m h : ℕ) (zeta : Fin m → Fin 30) :
    (coefficient m h zeta : ℂ) =
      (cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) : ℂ) ^ m *
        ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
          blockWgMatrix (2 * h) zeta sigma *
          ((∏ j : Fin m,
            qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
            qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j)
              (tau (finRotate m j)) : ℝ) : ℂ) := by
  unfold coefficient
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro tau _
  apply Finset.sum_congr rfl
  intro sigma _
  unfold blockWgMatrix
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [complexWg_symmetric]
  change ((_ : ℂ) * _ * (qubitFourthComplexWgMatrix _ (sigma j) (zeta j))) = _
  ring

/-- Direct expansion of the reverse composition, valid also when m=1. -/
theorem reverse_composition_basis_expansion {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (b : PauliBinaryWord (m * (2 * h))) :
    physicalShiftedAverage m h (physicalBlockAverage m (2 * h)
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)) =
      ∑ zeta : Fin m → Fin 30,
        (coefficient m h zeta : ℂ) • physicalShiftedBlockSectors m h zeta := by
  classical
  rw [physicalBlockAverage_basis m hK, map_smul, map_sum]
  simp_rw [physicalShiftedAverage_eq_synthesis m hK, familySynthesis_apply,
    physicalSectors_overlap hm hh]
  simp_rw [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro zeta _
  rw [coefficient_cast]
  simp only [Finset.mul_sum, Finset.sum_smul, mul_smul,
    Complex.ofReal_prod, Complex.ofReal_mul]

theorem inverse_conjugation_basis (U : Matrix.unitaryGroup ι ℂ) (b : ι) :
    unitaryMatrixConjugationLinearMap U⁻¹ (Matrix.single b b 1) =
      vectorProjector (measurementVector U b) := by
  ext i j
  simp [unitaryMatrixConjugationLinearMap_apply, Matrix.mul_apply,
    Matrix.single, ite_and, vectorProjector, measurementVector,
    Matrix.star_eq_conjTranspose, Matrix.vecMulVec_apply, Pi.star_apply]

omit [Fintype ι] in
theorem basis_tensor_four (b : ι) :
    matrixTensorFour (Matrix.single b b (1 : ℂ)) (Matrix.single b b 1)
      (Matrix.single b b 1) (Matrix.single b b 1) =
      Matrix.single (repeatedFourth b) (repeatedFourth b) 1 := by
  ext i j
  rcases i with ⟨i₁, i₂, i₃, i₄⟩
  rcases j with ⟨j₁, j₂, j₃, j₄⟩
  simp [matrixTensorFour_apply, Matrix.single, repeatedFourth, ite_and]
  aesop

/-- Literal conditional expectation of B^(tensor 4), with b fixed. -/
def basisMoment (U : E → Matrix.unitaryGroup ι ℂ) (b : ι) :
    Matrix (FourthIndex ι) (FourthIndex ι) ℂ :=
  (Fintype.card E : ℂ)⁻¹ • ∑ e : E,
    let B := vectorProjector (measurementVector (U e) b)
    matrixTensorFour B B B B

theorem basisMoment_eq_inverse_average (U : E → Matrix.unitaryGroup ι ℂ) (b : ι) :
    basisMoment U b = fourthAverage (fun e => (U e)⁻¹)
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1) := by
  simp only [basisMoment, fourthAverage, LinearMap.smul_apply, LinearMap.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro e _
  rw [← basis_tensor_four b, fourthConjugation_tensor, inverse_conjugation_basis]

/-- The new operator identity, for each computational outcome separately. -/
theorem basisMoment_eq_sector_sum {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (b : PauliBinaryWord (m * (2 * h))) :
    basisMoment (periodicTwoLayerCliffordUnitary m (2 * h)
      (cyclicQubitShift (m * (2 * h)) h)) b =
      ∑ zeta : Fin m → Fin 30,
        (coefficient m h zeta : ℂ) • physicalShiftedBlockSectors m h zeta := by
  rw [basisMoment_eq_inverse_average, inverse_periodicFourthAverage m h hK]
  exact reverse_composition_basis_expansion hm hh hK b

/-- Uniform circuit sampling and an independent uniform basis outcome. -/
def uniformMoment (U : E → Matrix.unitaryGroup ι ℂ) :
    Matrix (FourthIndex ι) (FourthIndex ι) ℂ :=
  (Fintype.card ι : ℂ)⁻¹ • ∑ b : ι, basisMoment U b

/-- Section V's labelled operator expectation identity. -/
theorem uniformMoment_eq_sector_sum {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h) :
    uniformMoment (periodicTwoLayerCliffordUnitary m (2 * h)
      (cyclicQubitShift (m * (2 * h)) h)) =
      ∑ zeta : Fin m → Fin 30,
        (coefficient m h zeta : ℂ) • physicalShiftedBlockSectors m h zeta := by
  classical
  simp only [uniformMoment, basisMoment_eq_sector_sum hm hh hK,
    Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]

/-- Same coefficient as the paper's c_{u,A'}(zeta); no adjoint on R. -/
def boundary (m h : ℕ) (zeta : Fin m → Fin 30)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) : ℂ :=
  ⟪vectorFourth u, (physicalShiftedBlockSectors m h zeta).toEuclideanLin
    (vectorFourth u)⟫_ℂ

theorem boundary_norm_le_one (m h : ℕ) (zeta : Fin m → Fin 30)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖boundary m h zeta u‖ ≤ 1 := by
  classical
  letI : DecidableEq (Fin m → PauliBinaryWord (2 * h)) :=
    fun a b => Fintype.decidablePiFintype a b
  let e := (permuteBinaryWord (cyclicQubitShift (m * (2 * h)) h)).symm.trans
    (binaryWordBlockEquiv m (2 * h))
  have h8 := LowerMoments.arbitrary_block_boundary
    (fun _ : Fin m => 2 * h) zeta (vectorReindex e u)
    (by rw [(vectorReindex e).norm_map, hu])
  have he := fourth_inner_reindex e
    ((blockSectors (2 * h) zeta).submatrix (fourthMapEquiv e) (fourthMapEquiv e)) u
  rw [reindex_pullback] at he
  change ‖⟪vectorFourth (vectorReindex e u),
    (blockSectors (2 * h) zeta).toEuclideanLin
      (vectorFourth (vectorReindex e u))⟫_ℂ‖ ≤ 1 at h8
  rw [he] at h8
  simpa only [boundary, physicalShiftedBlockSectors_eq_pullback] using h8

theorem basisMoment_contraction (U : E → Matrix.unitaryGroup ι ℂ) (b : ι)
    (u : EuclideanSpace ℂ ι) :
    qubitFourthComplexHilbertSchmidt (vectorProjector (vectorFourth u))
      (basisMoment U b) =
      (((Fintype.card E : ℝ)⁻¹ *
        ∑ e : E, ‖⟪measurementVector (U e) b, u⟫_ℂ‖ ^ 8 : ℝ) : ℂ) := by
  rw [basisMoment_eq_inverse_average, ← hilbertSchmidt_star,
    ← fourthAverage_inverse_adjoint, fourthAverage_diagonal]
  simp only [Complex.star_def, Complex.conj_ofReal]

theorem uniformMoment_contraction (U : E → Matrix.unitaryGroup ι ℂ)
    (u : EuclideanSpace ℂ ι) :
    qubitFourthComplexHilbertSchmidt (vectorProjector (vectorFourth u))
      (uniformMoment U) =
      (((Fintype.card ι : ℝ)⁻¹ * ∑ b : ι, (Fintype.card E : ℝ)⁻¹ *
        ∑ e : E, ‖⟪measurementVector (U e) b, u⟫_ℂ‖ ^ 8 : ℝ) : ℂ) := by
  simp only [uniformMoment, qubitFourthComplexHilbertSchmidt_smul_right,
    qubitFourthComplexHilbertSchmidt_sum_right, basisMoment_contraction,
    Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_sum]

/-- Scalar expansion obtained by contracting the new operator identity. -/
theorem uniformMoment_boundary_expansion {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) :
    qubitFourthComplexHilbertSchmidt (vectorProjector (vectorFourth u))
      (uniformMoment (periodicTwoLayerCliffordUnitary m (2 * h)
        (cyclicQubitShift (m * (2 * h)) h))) =
      ∑ zeta : Fin m → Fin 30, (coefficient m h zeta : ℂ) * boundary m h zeta u := by
  rw [uniformMoment_eq_sector_sum hm hh hK]
  simp only [qubitFourthComplexHilbertSchmidt_sum_right,
    qubitFourthComplexHilbertSchmidt_smul_right, hilbertSchmidt_projector_left, boundary]

/-- Literal real expectation under an independent uniform gate index and
uniform computational-basis label. The vector u is unrestricted. -/
def uniformOverlapMoment (U : E → Matrix.unitaryGroup ι ℂ)
    (u : EuclideanSpace ℂ ι) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ * ∑ b : ι, (Fintype.card E : ℝ)⁻¹ *
    ∑ e : E, ‖⟪measurementVector (U e) b, u⟫_ℂ‖ ^ 8

theorem uniformOverlapMoment_nonneg (U : E → Matrix.unitaryGroup ι ℂ)
    (u : EuclideanSpace ℂ ι) : 0 ≤ uniformOverlapMoment U u := by
  unfold uniformOverlapMoment
  positivity

/-- Lemma 7 in probability notation, obtained from its matrix identity. -/
theorem uniformOverlapMoment_sector_expansion {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) :
    (uniformOverlapMoment (periodicTwoLayerCliffordUnitary m (2 * h)
      (cyclicQubitShift (m * (2 * h)) h)) u : ℂ) =
      ∑ zeta : Fin m → Fin 30, (coefficient m h zeta : ℂ) * boundary m h zeta u := by
  rw [uniformOverlapMoment, ← uniformMoment_contraction]
  exact uniformMoment_boundary_expansion hm hh hK u

theorem uniformOverlapMoment_reindex
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (e : ι ≃ κ) (U : E → Matrix.unitaryGroup ι ℂ) (u : EuclideanSpace ℂ ι) :
    uniformOverlapMoment (fun t => reindexUnitary e (U t)) (vectorReindex e u) =
      uniformOverlapMoment U u := by
  unfold uniformOverlapMoment
  rw [← Fintype.card_congr e]
  congr 1
  rw [← Equiv.sum_comp e]
  simp_rw [measurement_inner_reindex]

/-- Equality with the pre-existing real moment; only summation order differs. -/
theorem uniformOverlapMoment_eq_finiteUniformEighth {D : ℕ}
    (U : E → Matrix.unitaryGroup (Fin D) ℂ) (u : EuclideanSpace ℂ (Fin D)) :
    uniformOverlapMoment U u = BornFourthMoment.finiteUnitaryUniformEighthMoment U u := by
  unfold uniformOverlapMoment BornFourthMoment.finiteUnitaryUniformEighthMoment
  simp only [Fintype.card_fin]
  change (D : ℝ)⁻¹ * (∑ b : Fin D, (Fintype.card E : ℝ)⁻¹ *
      ∑ e : E, ‖⟪measurementVector (U e) b, u⟫_ℂ‖ ^ 8) =
    ((Fintype.card E : ℝ) * (D : ℝ))⁻¹ *
      ∑ e : E, ∑ b : Fin D, ‖⟪measurementVector (U e) b, u⟫_ℂ‖ ^ 8
  rw [← Finset.mul_sum, ← mul_assoc, ← mul_inv_rev, Finset.sum_comm]

/-- Triangle inequality, kept separate so Theorem 9 supplies Lemmas 7 and 8
as actual proved inputs, rather than assuming either conclusion. -/
theorem real_moment_le_sum_abs {L : Type*} [Fintype L]
    (moment : ℝ) (a : L → ℝ) (c : L → ℂ)
    (h7 : (moment : ℂ) = ∑ zeta : L, (a zeta : ℂ) * c zeta)
    (h8 : ∀ zeta, ‖c zeta‖ ≤ 1) :
    moment ≤ ∑ zeta : L, |a zeta| := by
  calc
    moment ≤ ‖(moment : ℂ)‖ := by simpa using Complex.re_le_norm (moment : ℂ)
    _ = ‖∑ zeta : L, (a zeta : ℂ) * c zeta‖ := congrArg norm h7
    _ ≤ ∑ zeta : L, |a zeta| := by
      apply norm_sum_le_of_le
      intro zeta _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left (h8 zeta) (abs_nonneg _)).trans_eq (mul_one _)

theorem uniformMoment_le_sum_abs_coefficients {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖qubitFourthComplexHilbertSchmidt (vectorProjector (vectorFourth u))
      (uniformMoment (periodicTwoLayerCliffordUnitary m (2 * h)
        (cyclicQubitShift (m * (2 * h)) h)))‖ ≤
      ∑ zeta : Fin m → Fin 30, |coefficient m h zeta| := by
  rw [uniformMoment_boundary_expansion hm hh hK]
  apply norm_sum_le_of_le
  intro zeta _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (boundary_norm_le_one m h zeta u hu)
    (abs_nonneg _)).trans_eq (mul_one _)

/-- Regroup the finite expansion by its output sector. -/
theorem coefficient_pairing (m h : ℕ) (c : (Fin m → Fin 30) → ℂ) :
    ∑ zeta : Fin m → Fin 30, (coefficient m h zeta : ℂ) * c zeta =
      (cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) : ℂ) ^ m *
        sectorExpansion (qubitFourthGramMatrix ((2 : ℝ) ^ h))
          (qubitFourthComplexWgMatrix ((2 : ℝ) ^ (2 * h))) m c := by
  simp_rw [coefficient_cast, sectorExpansion, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tau _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sigma _
  apply Finset.sum_congr rfl
  intro zeta _
  simp only [blockWgMatrix]
  simp_rw [complexWg_symmetric _ (zeta _) (sigma _)]
  ring

/-- Equation (62), first finite identity: independent output labels. -/
theorem sum_product_abs_weingarten (Q : ℝ) (m : ℕ) (sigma : Fin m → Fin 30) :
    (∑ zeta : Fin m → Fin 30,
      ∏ j : Fin m, |qubitFourthRealWgMatrix Q (sigma j) (zeta j)|) =
      ∏ j : Fin m, ∑ z : Fin 30, |qubitFourthRealWgMatrix Q (sigma j) z| := by
  exact (Fintype.prod_sum
    (fun j z => |qubitFourthRealWgMatrix Q (sigma j) z|)).symm

theorem realWg_absolute_row_sum (Q : ℝ) (sigma : Fin 30) :
    (∑ z : Fin 30, |qubitFourthRealWgMatrix Q sigma z|) =
      cliffordFourthWgAbsoluteRowSum Q := by
  simpa only [qubitFourthComplexWgMatrix, qubitFourthRealWgMatrix,
    Complex.norm_real, Real.norm_eq_abs] using complexWg_absolute_row_sum Q sigma

/-- The first identity evaluates to a_Q^m, with the paper's real W_Q. -/
theorem sum_product_abs_weingarten_eq_row_power
    (Q : ℝ) (m : ℕ) (sigma : Fin m → Fin 30) :
    (∑ zeta : Fin m → Fin 30,
      ∏ j : Fin m, |qubitFourthRealWgMatrix Q (sigma j) (zeta j)|) =
      cliffordFourthWgAbsoluteRowSum Q ^ m := by
  rw [sum_product_abs_weingarten]
  simp only [realWg_absolute_row_sum, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]

/-- Equation (62), fixed-j identity: ordinary matrix square, not entrywise square. -/
theorem gram_overlap_sum_eq_square (q : ℝ) (left right : Fin 30) :
    (∑ sigma : Fin 30,
      qubitFourthGramMatrix q sigma left * qubitFourthGramMatrix q sigma right) =
      (qubitFourthGramMatrix q ^ 2) left right := by
  rw [pow_two, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro sigma _
  rw [qubitFourthGramMatrix_comm q sigma left]

/-- Summing each sigma_j independently applies the fixed-j identity at every block. -/
theorem sum_sigma_gram_products_eq_square_product
    (q : ℝ) (m : ℕ) (tau : Fin m → Fin 30) :
    (∑ sigma : Fin m → Fin 30, ∏ j : Fin m,
      qubitFourthGramMatrix q (sigma j) (tau j) *
        qubitFourthGramMatrix q (sigma j) (tau (finRotate m j))) =
      ∏ j : Fin m, (qubitFourthGramMatrix q ^ 2) (tau j) (tau (finRotate m j)) := by
  calc
    _ = ∏ j : Fin m, ∑ sigma : Fin 30,
        qubitFourthGramMatrix q sigma (tau j) *
          qubitFourthGramMatrix q sigma (tau (finRotate m j)) :=
      (Fintype.prod_sum (fun j sigma =>
        qubitFourthGramMatrix q sigma (tau j) *
          qubitFourthGramMatrix q sigma (tau (finRotate m j)))).symm
    _ = _ := by simp only [gram_overlap_sum_eq_square]

/-- Triangle inequality for a single literal signed coefficient a_zeta. -/
theorem coefficient_abs_le_unsigned_sum {m h : ℕ} (hK : 3 ≤ 2 * h)
    (zeta : Fin m → Fin 30) :
    |coefficient m h zeta| ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
          (∏ j : Fin m,
            qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
              qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j))) *
          (∏ j : Fin m,
            |qubitFourthRealWgMatrix ((2 : ℝ) ^ (2 * h)) (sigma j) (zeta j)|) := by
  have hfour : (4 : ℝ) < 2 ^ (2 * h) :=
    four_lt_two_pow_real_of_three_le hK
  have hs : 0 ≤ cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m := by
    rw [cliffordFourthWgSignedRowSum_eq hfour]
    positivity
  have hG := qubitFourthGramMatrix_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ h)
  unfold coefficient
  rw [abs_mul, abs_of_nonneg hs]
  apply mul_le_mul_of_nonneg_left _ hs
  calc
    _ ≤ ∑ tau : Fin m → Fin 30, |∑ sigma : Fin m → Fin 30,
        ∏ j : Fin m,
          qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
            qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) *
            qubitFourthRealWgMatrix ((2 : ℝ) ^ (2 * h)) (sigma j) (zeta j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
        |∏ j : Fin m,
          qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
            qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) *
            qubitFourthRealWgMatrix ((2 : ℝ) ^ (2 * h)) (sigma j) (zeta j)| := by
      exact Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro tau _
      apply Finset.sum_congr rfl
      intro sigma _
      rw [Finset.abs_prod, ← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro j _
      rw [abs_mul, abs_mul, abs_of_nonneg (hG _ _), abs_of_nonneg (hG _ _)]

/-- First line of (62) after summing over zeta: exactly a_Q^m is extracted. -/
theorem sum_abs_coefficients_le_overlap {m h : ℕ} (hK : 3 ≤ 2 * h) :
    (∑ zeta : Fin m → Fin 30, |coefficient m h zeta|) ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
            ∏ j : Fin m,
              qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
                qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j)) := by
  calc
    _ ≤ ∑ zeta : Fin m → Fin 30,
        cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
            (∏ j : Fin m,
              qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
                qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j))) *
            (∏ j : Fin m,
              |qubitFourthRealWgMatrix ((2 : ℝ) ^ (2 * h)) (sigma j) (zeta j)|) :=
      Finset.sum_le_sum (fun zeta _ => coefficient_abs_le_unsigned_sum hK zeta)
    _ = cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        ∑ tau : Fin m → Fin 30, ∑ sigma : Fin m → Fin 30,
          (∏ j : Fin m,
            qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau j) *
              qubitFourthGramMatrix ((2 : ℝ) ^ h) (sigma j) (tau (finRotate m j))) *
          (∑ zeta : Fin m → Fin 30, ∏ j : Fin m,
            |qubitFourthRealWgMatrix ((2 : ℝ) ^ (2 * h)) (sigma j) (zeta j)|) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro tau _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro sigma _
      rw [← Finset.mul_sum]
    _ = _ := by
      simp_rw [sum_product_abs_weingarten_eq_row_power, ← Finset.sum_mul]
      ring

/-- Exact endpoint of (62), before converting the cyclic sum to a trace. -/
theorem sum_abs_coefficients_le_cycle {m h : ℕ} (hK : 3 ≤ 2 * h) :
    (∑ zeta : Fin m → Fin 30, |coefficient m h zeta|) ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          ∑ tau : Fin m → Fin 30, ∏ j : Fin m,
            (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ 2)
              (tau j) (tau (finRotate m j)) := by
  simpa only [sum_sigma_gram_products_eq_square_product] using
    (sum_abs_coefficients_le_overlap (m := m) hK)

/-- The scalar first inequality preceding (62), from Lemmas 7 and 8. -/
theorem uniformOverlapMoment_le_sum_abs_coefficients {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    uniformOverlapMoment (periodicTwoLayerCliffordUnitary m (2 * h)
      (cyclicQubitShift (m * (2 * h)) h)) u ≤
      ∑ zeta : Fin m → Fin 30, |coefficient m h zeta| := by
  exact real_moment_le_sum_abs _ _ _
    (uniformOverlapMoment_sector_expansion hm hh hK u)
    (fun zeta => boundary_norm_le_one m h zeta u hu)

/-- The entire moment-to-cycle chain in (62), for the concrete gate law. -/
theorem uniformOverlapMoment_le_cycle {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    uniformOverlapMoment (periodicTwoLayerCliffordUnitary m (2 * h)
      (cyclicQubitShift (m * (2 * h)) h)) u ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          ∑ tau : Fin m → Fin 30, ∏ j : Fin m,
            (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ 2)
              (tau j) (tau (finRotate m j)) := by
  exact (uniformOverlapMoment_le_sum_abs_coefficients hm hh hK u hu).trans
    (sum_abs_coefficients_le_cycle hK)

/-- Equation (63), with the same matrix square and cyclic successor as (62). -/
theorem gram_square_cycle_eq_trace (q : ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ tau : Fin m → Fin 30, ∏ j : Fin m,
      (qubitFourthGramMatrix q ^ 2) (tau j) (tau (finRotate m j))) =
      (qubitFourthGramMatrix q ^ (2 * m)).trace := by
  change FourthCycleContraction.cyclePartition (qubitFourthGramMatrix q ^ 2) m = _
  rw [FourthCycleContraction.cyclePartition_eq_trace _ hm, ← pow_mul]

/-- The trace bound now explicitly passes through both identities and (62). -/
theorem sum_abs_coefficients_le_trace {m h : ℕ}
    (hm : 0 < m) (hK : 3 ≤ 2 * h) :
    (∑ zeta : Fin m → Fin 30, |coefficient m h zeta|) ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ (2 * m)).trace := by
  simpa only [gram_square_cycle_eq_trace _ hm] using
    (sum_abs_coefficients_le_cycle (m := m) hK)

theorem uniformMoment_le_trace {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖qubitFourthComplexHilbertSchmidt (vectorProjector (vectorFourth u))
      (uniformMoment (periodicTwoLayerCliffordUnitary m (2 * h)
        (cyclicQubitShift (m * (2 * h)) h)))‖ ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ (2 * m)).trace :=
  (uniformMoment_le_sum_abs_coefficients hm hh hK u hu).trans
    (sum_abs_coefficients_le_trace hm hK)

/-- The same estimate holds before averaging over b. -/
theorem basisMoment_le_trace {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (b : PauliBinaryWord (m * (2 * h)))
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖qubitFourthComplexHilbertSchmidt (vectorProjector (vectorFourth u))
      (basisMoment (periodicTwoLayerCliffordUnitary m (2 * h)
        (cyclicQubitShift (m * (2 * h)) h)) b)‖ ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ (2 * m)).trace := by
  rw [basisMoment_eq_sector_sum hm hh hK,
    ← uniformMoment_eq_sector_sum hm hh hK]
  exact uniformMoment_le_trace hm hh hK u hu

/-- Compatibility with the pre-existing measurement endpoint, now derived
through the operator expansion and the coefficient l1 bound. -/
theorem periodic_basis_diagonal_le_trace {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (b : PauliBinaryWord (m * (2 * h)))
    (u : EuclideanSpace ℂ (PauliBinaryWord (m * (2 * h)))) (hu : ‖u‖ = 1) :
    ‖qubitFourthComplexHilbertSchmidt
      (Matrix.single (repeatedFourth b) (repeatedFourth b) 1)
      (periodicFourthAverage m h (vectorProjector (vectorFourth u)))‖ ≤
      cliffordFourthWgSignedRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
        cliffordFourthWgAbsoluteRowSum ((2 : ℝ) ^ (2 * h)) ^ m *
          (qubitFourthGramMatrix ((2 : ℝ) ^ h) ^ (2 * m)).trace := by
  unfold periodicFourthAverage
  rw [fourthAverage_inverse_adjoint, ← basisMoment_eq_inverse_average,
    ← hilbertSchmidt_star, norm_star]
  exact basisMoment_le_trace hm hh hK b u hu

/-- Transfer to any finite circuit law with the same fourth average.
This hypothesis is explicit; it is not an axiom identifying the full
projective Clifford law with the concrete finite implementation. -/
theorem uniformMoment_eq_of_fourthAverage_eq
    {F : Type*} [Fintype F] (U : E → Matrix.unitaryGroup ι ℂ)
    (V : F → Matrix.unitaryGroup ι ℂ) (hUV : fourthAverage U = fourthAverage V) :
    uniformMoment U = uniformMoment V := by
  have hinv : fourthAverage (fun e => (U e)⁻¹) =
      fourthAverage (fun f => (V f)⁻¹) := by
    apply LinearMap.ext
    intro X
    apply hilbertSchmidt_ext_left
    intro Y
    rw [← fourthAverage_inverse_adjoint, ← fourthAverage_inverse_adjoint, hUV]
  simp only [uniformMoment, basisMoment_eq_inverse_average, hinv]

/-- A local, layer-by-layer version of the preceding transfer. -/
theorem uniformMoment_eq_sector_sum_of_layer_averages
    {E₁ E₂ : Type*} [Fintype E₁] [Fintype E₂] {m h : ℕ}
    (hm : 0 < m) (hh : 0 < h) (hK : 3 ≤ 2 * h)
    (U₁ : E₁ → Matrix.unitaryGroup (PauliBinaryWord (m * (2 * h))) ℂ)
    (U₂ : E₂ → Matrix.unitaryGroup (PauliBinaryWord (m * (2 * h))) ℂ)
    (h₁ : fourthAverage U₁ = physicalShiftedAverage m h)
    (h₂ : fourthAverage U₂ = physicalBlockAverage m (2 * h)) :
    uniformMoment (fun e : E₁ × E₂ => U₂ e.2 * U₁ e.1) =
      ∑ zeta : Fin m → Fin 30,
        (coefficient m h zeta : ℂ) • physicalShiftedBlockSectors m h zeta := by
  rw [← uniformMoment_eq_sector_sum hm hh hK]
  apply uniformMoment_eq_of_fourthAverage_eq
  rw [fourthAverage_product, h₁, h₂]
  exact (periodicFourthAverage_eq_composition m h).symm

end
end TomographyOracleCore.PaperMatch.SectionV
